## Classes and methods for divisors on simplicial complexes.

# TODO
# - add documentation, including examples
# - only compute the positive kernel on demand (and then save it


# technique for caching results of function calls
from functools import wraps
from sage.matroids.advanced import *

class FuncCache(object):
    def __init__(self):
        self.cache = {}

    def __call__(self, func):
        @wraps(func)
        def callee(*args, **kwargs):
            key = (args, str(kwargs))
            # see is there already result in cache
            if key in self.cache:
                result = self.cache.get(key)
            else:
                result = func(*args, **kwargs)
                self.cache[key] = result
            return result
        return callee

my_cache = FuncCache()



class KSimplicialComplex(SimplicialComplex):
    """
    Class for playing with higher critical groups of simplicial complexes.

    EXAMPLES::

	sage: load('simp.sage')
	sage: S = KSimplicialComplex([[1,2,3],[1,2,4],[1,2,5],[1,3,4],[1,3,5],[2,3,4],[2
	....: ,3,5]])
	sage: S.facets()
	{(1, 3, 4), (1, 3, 5), (2, 3, 5), (1, 2, 3), (2, 3, 4), (1, 2, 5), (1, 2, 4)}
	sage: S.critical()

	[Finitely generated module V/W over Integer Ring with invariants (5, 15),
	 Finitely generated module V/W over Integer Ring with invariants (15),
	 Finitely generated module V/W over Integer Ring with invariants (0, 0)]
    """

    def __init__(self, *kwds):
        # print "building a KSimplicialComplex"
        super(KSimplicialComplex,self).__init__(*kwds)
        self.set_immutable()
        C = self.chain_complex(augmented=true)
        self._complex = self.chain_complex(augmented=True)
        C = self._complex
        self._boundary = C.differential()
        D = C.differential()
        n = len(D)-1
        self._laplacian = [D[i]*D[i].transpose() for i in range(n)]
        self._ker = [D[i].right_kernel() for i in range(n)]
        self._critical = []
        for i in range(n-1):
            imageL = self._ker[i].submodule(self._laplacian[i+1].image().gens())
            self._critical.append(self._ker[i].quotient(imageL))
        self._picard = []
        self._laplacian_kernel = []
        self._polytope_ieqs = []
        self._Hilbert_basis = {}
        self._positive_kernel = []
        self._pivots = []
        for i in range(n-1):
            li = self._laplacian[i+1]
            self._picard.append(FreeModule(ZZ,rank=li.nrows()).quotient(li.image()))
            lk = li.right_kernel()
            self._laplacian_kernel.append(lk)
            p = lk.matrix().pivots()
            self._pivots.append(p)
            self._polytope_ieqs.append(li.delete_columns(p))
            c = Cone(lk.matrix())
            pos_orthant = Cone(identity_matrix(li.nrows()))
            pos_cone = c.intersection(pos_orthant)
            self._positive_kernel.append(pos_cone)

    def boundary(self, n=None):
        if n==None:
            return self._boundary
        else:
            return self._boundary[n]

    def betti(self, n=None):
        if n==None:
            return self._complex.betti()
        else:
            return self._complex.betti(n)

    def homology(self, n=None):
        if n==None:
            return self._complex.homology()
        else:
            return self._complex.homology(n)

    def complex(self):
        return self._complex

    def critical(self, n=None):
        if n==None:
            return self._critical
        else:
            return self._critical[n]

    def picard(self, n=None):
        if n==None:
            return self._picard
        else:
            return self._picard[n]

    def laplacian(self,n=None):
        if n==None:
            return self._laplacian
        else:
            return self._laplacian[n+1]

 
    def laplacian_kernel(self,k):
        r"""
        The kernel of the k-th laplacian.
        """
        return self._laplacian_kernel[k]

    def reduced_laplacian(self,k=None,tree=None, return_tree=True, check=True):
        r"""
        The reduced k-laplacian with respect to `tree`.  If tree=None, then a
        tree of dimension k is calculated (if possible).  If check=True, a
        warning is issued if the tree is not acyclic in codimension 1 (dimension
        k-1).  In that case, it is not necessarily true that the cokernel of the
        reduced laplacian is isomorphic to the critical group.  (TODO: find an
        example of this.)

        INPUT:

        k -  integer (dimension)
        tree - KSimplicialComplex (spanning tree of dimension k)
        check - boolean

        OUTPUT:

        matrix (if return_tree=False)
        (matrix,KSimplicialComplex) (if return_tree=True)

        EXAMPLES::

            sage: s = ksimplicial_complexes.equatorial_bipyramid()
            sage: s.reduced_laplacian()

            (
                    [0 0]                                                                 
                    [0 0], Simplicial complex with vertex set (1, 2, 3, 4, 5) and 5
                    facets
                    )
                    sage: s.reduced_laplacian(1)

                    (
                            [ 3 -1 -1  1  1]                                                                                                
                            [-1  3 -1 -1  0]                                                                                                
                            [-1 -1  2  0 -1]                                                                                                
                            [ 1 -1  0  3 -1]                                                                                                
                            [ 1  0 -1 -1  2], Simplicial complex with vertex set (1,
                            2, 3, 4, 5) and facets {(3, 4), (1, 5), (3, 5), (2, 5)}
                            )
                            sage: s.reduced_laplacian(1,return_tree=False)

                            [ 3 -1 -1  1  1]
                            [-1  3 -1 -1  0]
                            [-1 -1  2  0 -1]
                            [ 1 -1  0  3 -1]
                            [ 1  0 -1 -1  2]
                            sage: T = s.reduced_laplacian(1)[1]
                            sage: s.reduced_laplacian(1,tree=T,return_tree=False)

                            [ 3 -1 -1  1  1]
                            [-1  3 -1 -1  0]
                            [-1 -1  2  0 -1]
                            [ 1 -1  0  3 -1]
                            [ 1  0 -1 -1  2]
            sage: s = ksimplicial_complexes.square_antiprism()
            sage: s.reduced_laplacian()
            There is no 2-dimensional spanning tree.
        """
        if k==None:
            k = self.dimension()
        if tree==None:
            tree = self.find_spanning_tree(k)
            if tree==None:
                return None
        faces = filter(lambda f: f not in tree.n_cells(k),self.n_cells(k))
        face_indices = [self.n_cells(k).index(f) for f in faces]
        red_lap = self.laplacian(k).matrix_from_rows_and_columns(face_indices,face_indices)
        if check:
            if tree.homology(k-1).ngens!=0:
                print 'WARNING: the tree is not acyclic in codimension 1. Thus, the cokernel of the reduced k-laplacian may not be isomorphic to the k-th critical group.'
        if return_tree:
            return red_lap, tree
        else:
            return red_lap

    def positive_kernel(self,k):
        r"""
        The semigroup of nonnegative vectors in the kernel of the k-th
        laplacian.
        """
        return self._positive_kernel[k]

    @my_cache
    def positive_lattice(self,k):
        r"""
        The semigroup of the images of the k-faces under the boundary map.

        INPUT:

          k - integer

        OUTPUT:

          ConvexRationalPolyhedralCone

        EXAMPLES::

            sage: s = ksimplicial_complexes.hollow_simplex(2)
            sage: c = s.positive_lattice(1)
            sage: c
            3-d cone in 4-d lattice N
            sage: c.Hilbert_basis()

            N(1,  0,  0, -1),
            N(0, -1,  1,  0),
            N(0,  0, -1,  1)
            in 4-d lattice N
        """
        C = Cone(self.boundary(k).columns())
        return C

    def Hilbert_basis(self,k):
        r"""
        A Hilbert basis for the semigroup of nonnegative integer vectors in the
        kernel of the k-th laplacian.
        """
        if k not in [0..self.dimension()]:
            print "Argument out of range"
            return
        elif k not in self._Hilbert_basis.keys():
            self._Hilbert_basis[k] = self._positive_kernel[k].Hilbert_basis()
        return self._Hilbert_basis[k].matrix()

    def Picard_group_gens(self, k, text_version=False):
        r"""
        Generators for the k-th Picard group, i.e., of the cokernel of k-st
        Laplacian.

        INPUT:

          print - boolean

        OUTPUT:

        (list1, list2) where list1 is a list of generators for the torsion part and 
                       list2 is a list of generators for the free part

        EXAMPLES::

	    sage: e = equatorial_bipyramid()
	    sage: e.Picard_group_gens(0)
	    ([(-1, 0, 1, 0, 0), (-1, 0, 0, 1, 0)], [(0, 0, 0, 0, 1)])
	    sage: e.Picard_group_gens(0,True)
	    Torsion generators:
	     - (1,) + (3,)
	     - (1,) + (4,)

	    Free generators:
	     + (5,)
	    sage: e.Picard_group_gens(1,True)
	    Torsion generators:
	     + (1, 2) - (1, 4) + (2, 4)

	    Free generators:
	     + (2, 5)
	     + (3, 5)
	     + (3, 4)
	     + (1, 2)
	    sage: e.Picard_group_gens(2,True)
	    Torsion generators:

	    Free generators:
	     + (1, 2, 3)
	     + (1, 2, 4)
	     + (1, 2, 5)
	     + (1, 3, 4)
	     + (1, 3, 5)
	     + (2, 3, 4)
	     + (2, 3, 5)
        """
        el = self.laplacian(k)
        d, u, v = el.smith_form()
        w = u.inverse()
        torsion = []
        free = []
        for i,e in enumerate(el.elementary_divisors()):
            if e>1:
                torsion.append(w.column(i))
            elif e==0:
                free.append(w.column(i))
        if text_version:
            print 'Torsion generators:'
            for t in torsion:
                self.print_cycle(t,k)
            print
            print 'Free generators:'
            for f in free:
                self.print_cycle(f,k)
        else:
            return torsion, free

    def critical_group_gens(self, k, text_version=False):
        r"""
        Generators for the k-th critical group.

        INPUT:

          print - boolean

        OUTPUT:

        (list1, list2) where list1 is a list of generators for the torsion part and 
                       list2 is a list of generators for the free part

        EXAMPLES::
            sage: s = ksimplicial_complexes.equatorial_bipyramid()
            sage: s.critical()

            [Finitely generated module V/W over Integer Ring with invariants (5, 15),
             Finitely generated module V/W over Integer Ring with invariants (15),
              Finitely generated module V/W over Integer Ring with invariants (0, 0)]
              sage: s.critical_group_gens(0)
              ([(0, -1, 1, 0, 0), (0, 1, 0, 0, -1)], [])
              sage: s.critical_group_gens(0,True)
              Torsion generators:
               - (2,) + (3,)
                + (2,) - (5,)

                Free generators:
                sage: s.critical_group_gens(1,True)
                Torsion generators:
                 + (2, 3) - (2, 5) + (3, 5)

                 Free generators:
                 sage: s.critical_group_gens(2,True)
                 Torsion generators:

                 Free generators:
                  + (1, 2, 3) - (1, 2, 5) + (1, 3, 5) - (2, 3, 5)
                   + (1, 2, 4) - (1, 2, 5) - (1, 3, 4) + (1, 3, 5) + (2, 3, 4) - (2, 3, 5)
        """
        K = self.critical(k)
        inv  = K.invariants()
        torsion = []
        free = []
        for i,g in enumerate(K.gens()):
            if inv[i]==0:
                free.append(g.lift())
            else:
                torsion.append(g.lift())
        if text_version:
            print 'Torsion generators:'
            for t in torsion:
                self.print_cycle(t,k)
            print
            print 'Free generators:'
            for f in free:
                self.print_cycle(f,k)
        else:
            return torsion, free

    def div_gens(self, text_version=False):
        r"""
        Generators for the group of divisor classes.

        INPUT:

          print - boolean

        OUTPUT:

        (list1, list2) where list1 is a list of generators for the torsion part and 
                       list2 is a list of generators for the free part

        EXAMPLES::

	    sage: e = equatorial_bipyramid()
	    sage: e.div_gens(true)
	    Torsion generators:
	    (1, 0, -1, 0, 0, 1, 0, 0, 0)
	     + (1, 2) - (1, 4) + (2, 4)

	    Free generators:
	    (0, 0, 0, 0, 0, 0, 1, 0, 0)
	     + (2, 5)
	    (0, 0, 0, 0, 0, 0, 0, 0, 1)
	     + (3, 5)
	    (0, 0, 0, 0, 0, 0, 0, 1, 0)
	     + (3, 4)
	    (1, 0, 0, 0, 0, 0, 0, 0, 0)
	     + (1, 2)
        """
        return self.Picard_group_gens(self.dimension()-1,text_version)

    def print_cycle(self, C, k):
        r"""
        Print the k-cycle C.

        INPUT:

          C - list or vector representing a k-cell

        OUTPUT:

          print C as a linear combination of k-cells
        """
        kcells = self.n_cells(k)
        ourstring = ''
        for i,c in enumerate(C):
            if c!=0:
                if sign(c)==1:
                    ourstring += ' + '
                else:
                    ourstring += ' - '
                if abs(c)==1:
                    ourstring += str(kcells[i])
                else:
                    ourstring += str(abs(c))+str(kcells[i])
        print ourstring 

    def multiply_divs(self, D, F):
        r"""
        Return the product of divisors D and F in K_{n-2}.

        INPUT:

          D, F - lists or vectors representing divisors

        OUTPUT:

          vector representing the product of D and F in K_{n-2}
        """
        n = self.dimension()
        d = vector(D)
        f = vector(F)
        b = self.boundary(n-1)
        bd = b*d
        bf = b*f
        result = []
        for i in range(len(bd)):
            result.append(bd[i]*bf[i])
        return vector(result)

    def standard_repr_for_group_elt(self, sigma, k, verbose=False):
        r"""
        Given a vector representing an element of Pic^k(Delta) express it as and
        element of Z_d1 x ... Z_dm x Z^r where the di are the invariant factors
        for the k-th Laplacian.  If verbose is `True`, then list 

             d1,...,dm,0,...,0

        where the number of zeros is `r`.  

        INPUT:

          sigma   - list or vector representing element element of Pic^k(Delta)
          k       - dimension of sigma
          verbose - boolean

        OUTPUT:

          vector

        EXAMPLES::

	    sage: e = equatorial_bipyramid()
	    sage: a = e.Picard_group_gens(1)
	    sage: e.standard_repr_for_group_elt(a[1][0],1,true)
	    [15, 0, 0, 0, 0]
	    [0, 1, 0, 0, 0]
	    sage: e.standard_repr_for_group_elt(a[1][1],1,true)
	    [15, 0, 0, 0, 0]
	    [0, 0, 1, 0, 0]
	    sage: e.standard_repr_for_group_elt(a[1][2],1,true)
	    [15, 0, 0, 0, 0]
	    [0, 0, 0, 1, 0]
	    sage: e.standard_repr_for_group_elt(a[1][3],1,true)
	    [15, 0, 0, 0, 0]
	    [0, 0, 0, 0, 1]
        """
        el = self.laplacian(k)
        d, u, v = el.smith_form()
        coords = u*vector(sigma)
        ed = el.elementary_divisors()
        result = []
        good_ed = []
        for i,e in enumerate(ed):
            if e>1 or e==0:
                good_ed.append(e)
                result.append(coords[i])
        if verbose:
            print good_ed
            return result
        else:
            return result

    def mult_table_divs(self):
        r"""
        The multiplication table for divisor classes.
        """
        d = self.dimension()
        el = self.laplacian(d)
        ed = el.elementary_divisors()
        good_ed = []
        for i,e in enumerate(ed):
            if e>1 or e==0:
                good_ed.append(e)
        print good_ed
        torsion, free = self.div_gens()
        divs = torsion + free
        for a in divs:
            row = []
            for b in divs:
                m = self.multiply_divs(a,b)
                row.append(self.standard_repr_for_group_elt(m,d-2))
            print row
        return 
    
    def is_winning_degree(self,d,k,witness=False,rays_only=False):
        r"""
        Are all divisors of degree d winnable.  If rays_only is `True` compute
        degrees with respect to the rays of the positive kernel only.  If
        witness is `True` and the return value is false, return an unwinnable
        divisor of degree d.

        INPUT:

        d - list of integers (the degrees of a divisor)
        k - integer (dimension)
        witness - boolean
        rays_only - boolean

        OUTPUT:

        boolean or (boolean, list of integers)

        EXAMPLES::

            sage: s = ksimplicial_complexes.annulus(3)
            sage: s.homology()
            {-1: 0, 0: 0, 1: Z, 2: 0, 3: 0}
            sage: s.is_winning_degree([0]*s.Hilbert_basis(1).nrows(),1,true,false)
            (False, (1, 0, 0, -1, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0))
            sage: s.is_winning_degree([0]*s.Hilbert_basis(2).nrows(),2,true,false)
            (True, None)
        """
        if rays_only and len(d)!=len(self.positive_kernel(k).rays()):
            print 'dimensions of arguments do not agree'
            return
        elif len(d)!=self.Hilbert_basis(k).nrows():
            print 'dimensions of arguments do not agree'
            return
        # find a divisor of the given degree
        if rays_only:
            h = self.positive_kernel(k).rays().matrix()
        else:
            h = self.Hilbert_basis(k)
        D = h.solve_right(vector(ZZ,d))  # D had degree d
        # We get all divisors with the same degree as D by adding elements of
        # the torsion part of the critical group of dimension k.  See if any of
        # these are unwinnable.
        gp = self.Picard_group_gens(k)[0] # generators for torsion part of group
        invars = [i for i in self.critical(k).invariants() if i!=0] # orders for these generators
        c = cartesian_product_iterator([range(i) for i in invars])
        is_winnable = True
        for i in c:
            K = D + sum([i[j]*gp[j] for j in range(len(invars))])
            if not self.is_winnable(K,k):
                is_winnable=False
                break
        if witness:
            if is_winnable:
                return (True,None)
            else:
                return (False, K)
        else:
            if is_winnable:
                return True
            else:
                return False

#    def find_minimal_winning_degrees(self, d, rays_only=False, starting_point=None):
#        r"""
#        Find the minimal degrees such that if a divisor has degree large than
#        one of these, then it is winnable.
#
#        NOTE: For now we are assuming the every degree is realized by some
#        divisor, which might not be true.  (We can check for this by seeing if
#        each of the standard basis vectors is realizable.)
#
#        INPUT:
#
#        d - integer (dimension)
#        rays_only - boolean
#        starting_point - list of integers (degree vector)
#
#        OUTPUT:
#
#        list of integer vectors
#
#        EXAMPLES::
#
#            sage: s = ksimplicial_complexes.equatorial_bipyramid()
#            sage: s.find_minimal_winning_degrees(1)
#            Starting point: [2, 2, 2, 2]
#
#            [[1, 1, 2, 2]]
#            sage: s.find_minimal_winning_degrees(2)
#            Starting point: [0, 0, 0, 0, 0, 0, 0]
#
#            [[0, 0, 0, 0, 0, 0, 0]]
#            sage: s.facets()
#            {(1, 3, 4), (1, 3, 5), (2, 3, 5), (1, 2, 3), (2, 3, 4), (1, 2, 5), (1, 2, 4)}
#            sage: s.facets()[:-2]   # a simplicial tree
#            [(1, 3, 4), (1, 3, 5), (2, 3, 5), (1, 2, 3), (2, 3, 4)]
#            sage: ns = KSimplicialComplex(s.facets()[:-2])
#            sage: ns.find_minimal_winning_degrees(1)
#            Starting point: [0, 0, 0, 0]
#
#            [[0, 0, 0, 0]]
#        """
#        # the length of a valid degree vector
#        if rays_only:
#            deglen = len(self.positive_kernel(d).rays())
#        else:
#            deglen = self.Hilbert_basis(d).nrows()
#        # find a starting point if none is provided
#        if starting_point==None:
#            i = -1
#            winning = False
#            while not winning:
#                i +=1
#                winning = self.is_winning_degree([i]*deglen,d,False,rays_only)
#            starting_point = [i]*deglen
#            print 'Starting point: '+str(starting_point)
#            print
#        # search
#        active = [starting_point]
#        result = []  # collect the minimal winning degrees here
#        while(active!=[]):
#            current = active.pop()
#            all_unwinnable = True # see if all descendants are winnable
#            for i in range(deglen):
#                if current[i]>0:
#                    test = copy(current)
#                    test[i] -= 1
#                    if self.is_winning_degree(test,d,False,rays_only):
#                        all_unwinnable = False
#                        if test not in active:
#                            active.append(test)
#            if all_unwinnable:
#                if current not in result: 
#                    result.append(current)
#        return result

    def div_comp(self,v,w):
        r"""
        Compare two lists (of the same length component-wise.  If v <=w, return
        `True`, and otherwise, return `False`.

        INPUT:

        v, w - lists of numbers

        OUTPUT:

        boolean

        EXAMPLES::

        sage: s = ksimplicial_complexes.equatorial_bipyramid()
        sage: s.div_comp([1,3],[1,3])
        True
        sage: s.div_comp([1,5],[1,4])
        False
        sage: s.div_comp([1,2],[1,4])
        True
        """
        d = len(v)
        return forall(range(d), lambda i: v[i]<=w[i])[0]

    def find_minimal_winning_degrees(self, d, rays_only=False, verbose=False):
        r"""
        Find the minimal degrees such that if a divisor has degree large than
        one of these, then it is winnable.

        NOTE: For now we are assuming the every degree is realized by some
        divisor, which might not be true.  (We can check for this by seeing if
        each of the standard basis vectors is realizable.)

        INPUT:

        d - integer (dimension)
        rays_only - boolean
        verbose - boolean

        OUTPUT:

        list of integer vectors

        EXAMPLES::

            sage: s = ksimplicial_complexes.equatorial_bipyramid()
            sage: s.find_minimal_winning_degrees(1)
            Starting point: [2, 2, 2, 2]

            [[1, 1, 2, 2]]
            sage: s.find_minimal_winning_degrees(2)
            Starting point: [0, 0, 0, 0, 0, 0, 0]

            [[0, 0, 0, 0, 0, 0, 0]]
            sage: s.facets()
            {(1, 3, 4), (1, 3, 5), (2, 3, 5), (1, 2, 3), (2, 3, 4), (1, 2, 5), (1, 2, 4)}
            sage: s.facets()[:-2]   # a simplicial tree
            [(1, 3, 4), (1, 3, 5), (2, 3, 5), (1, 2, 3), (2, 3, 4)]
            sage: ns = KSimplicialComplex(s.facets()[:-2])
            sage: ns.find_minimal_winning_degrees(1)
            Starting point: [0, 0, 0, 0]

            [[0, 0, 0, 0]]
        """
        # the length of a valid degree vector
        if rays_only:
            deglen = len(self.positive_kernel(d).rays())
        else:
            deglen = self.Hilbert_basis(d).nrows()
        # search
        active = [[0]*deglen]  # start search here
        inactive = [] # excluded from becoming active 
        result = []  # collect the minimal winning degrees here
        while(active!=[]):
            current = active.pop()
            considering = []
            for i in range(deglen):
                new = copy(current)
                new[i] += 1
                considering.append(new)
            if self.is_winning_degree(current,d,False,rays_only):
                # we have found a minimal degree
                if verbose:
                    print current
                if current not in result:
                    result.append(current)
                for c in considering:
                    if c not in inactive:
                        inactive.append(c)
            else:
                for c in considering:
                    if not exists(active, lambda a: self.div_comp(a,c))[0]:
                        if not exists(result, lambda a: self.div_comp(a,c))[0]:
                            active = [c] + active
        return result

    def is_tree(self):
        r"""
        Is this simplicial complex a tree.  This means that it's top-dimensional
        homology is 0 and it Betti number in codimension 1 is 0.
        """
        d = self.dimension()
        if self.homology(d).ngens()==0 and self.betti(d-1)==0:
            return True
        else:
            return False

    def is_forest(self):
        r"""
        Is this simplicial complex a spanning forest.  This means that it's
        top-dimensional homology is 0.

        OUTPUT:

        boolean

        EXAMPLES::

            sage: s = ksimplicial_complexes.annulus()
            sage: s.is_forest()
            True
            sage: s = ksimplicial_complexes.hollow_simplex(2)
            sage: s.homology()
            {-1: 0, 0: 0, 1: 0, 2: Z}
            sage: s.is_forest()
            False
        """
        return self.homology(self.dimension()).ngens()==0

    def spanning_forest(self, all=False):
        r"""
        Find a spanning forest.  This is a top-dimensional subcomplex with the
        same codimension 1 skeleton and such that (i) its top homology is 0 and
        (ii) its number of facets is the same as the total number of facets minus
        the top betti number of the whole complex.  If all is True, return all
        spanning forests.

        INPUT:

        all - boolean

        OUTPUT:

        KSimplicialComplex or list of KSimplicialComplex

        EXAMPLES::


        """
        facets = self.facets()
        d = self.dimension()
        b = self.betti(d)
        result = []
        for c in Combinations(facets, len(facets)-b):
            candidate = SimplicialComplex(c)
            if candidate.n_skeleton(d-1)==self.n_skeleton(d-1) and candidate.homology(d).ngens()==0:
                if not all:
                    return KSimplicialComplex(candidate)
                else: 
                    result.append(KSimplicialComplex(candidate))
        return result

    def forest_number(self):
        r"""
        Find the spanning forest number.  This is the sum of the squares of the
        sizes of the torsion subgroups of the codimension 1 homology of all
        spanning forests.  

        OUTPUT:

        integer
        """
        d = self.dimension()
        forests = self.spanning_forest(True)
        result = 0
        for f in forests:
            torsion_size = prod([i for i in f.homology(d-1).invariants() if i!=0])
            result += torsion_size^2
        return result

    def find_spanning_tree(self, d=None):
        r"""
        Find a d-dimensional spanning tree.  For example, in a graph, a usual
        spanning tree has dimension 1.

        INPUT:

        d - integer

        OUTPUT:

        KSimplicialComplex

        EXAMPLES::

            sage: s = ksimplicial_complexes.equatorial_bipyramid()
            sage: s.n_cells(2)
            [(1, 2, 3), (1, 2, 4), (1, 2, 5), (1, 3, 4), (1, 3, 5), (2, 3, 4), (2,
            3, 5)]
            sage: t = s.find_spanning_tree()
            sage: t.n_cells(2)
            [(1, 2, 5), (1, 3, 4), (1, 3, 5), (2, 3, 4), (2, 3, 5)]
            sage: t.is_tree()
            True
        """
        if d==None:
            d = self.dimension()
        s = SimplicialComplex(self.n_cells(d))
        if s.betti(d-1)!=0:
            print 'There is no '+str(d)+'-dimensional spanning tree.'
            return None
        while s.homology(d).ngens()!=0:
            # find a generator for some homology in dimension d
            a = s.chain_complex().homology(d,generators=True)[0][1]
            a = a.vector(d)
            # remove on of its faces
            cells = s.n_cells(d)
            del cells[a.nonzero_positions()[0]]
            s = SimplicialComplex(cells)
        return KSimplicialComplex(s.n_cells(d))

    # METHODS FOR DIVISORS

    def divisor_degrees(self, D, k, rays_only=False):
        r"""
        The dot product of the k-dimensional divisor D with each element of the
        Hilbert basis for the positive kernel of k-Laplacian. If rays_only is
        `True`, then the degrees are only computes relative to these rays (and
        not necessarily the full Hilbert basis).

        INPUT:

          D - list
          k - integer 
          rays_only - boolean

        OUTPUT:

          list of integers

        EXAMPLES::

            sage: s = hollow_simplex(2)
            sage: D = [1,0,0,1,2,1]
            sage: s.divisor_degrees(D,1)
            [3, 3, 3]
            sage: s.Hilbert_basis(2) # dimension = 2-1 = 1

            [0 1 0 0 1 1]
            [0 1 1 1 1 0]
            [1 0 1 0 1 0]
        """
        if rays_only:
            return [vector(D)*vector(i) for i in self._positive_kernel[k].rays()] 
        else: 
            return [vector(D)*vector(i) for i in self.Hilbert_basis(k)]

    def divisor_polytope(self, D, k):
        r"""
        Let L be the k-Laplacian.  To find effective divisors linearly
        equivalent to D, we need to solve D - L*sigma >= 0.  Using the kernel of
        L, we can eliminate variables in sigma, which amount to removing the
        columns of L corresponding to pivots in ker(L).

        INPUT:

          D - list
          k - integer 

        OUTPUT:

          Polyhedron

        EXAMPLES::

            sage: s = hollow_simplex(2)
            sage: s.divisor_polytope([1,1,1,1,1,1],1)
            A 3-dimensional polyhedron in QQ^3 defined as the convex hull of 7
            vertices
        """
        p = self._polytope_ieqs[k]
        myieqs = [[D[i]] + list(-r) for i,r in enumerate(p)]
        return Polyhedron(ieqs=myieqs)

    def complete_linear_system(self, D, k):
        r"""
        All effective divisors linearly equivalent to the k-dimensional divisor
        D.

        INPUT:

          D - list (representing a k-divisor) 
          k - integer

        OUPUT:

          list of integer vectors (representing divisors)

        EXAMPLES::

	    sage: s = hollow_simplex(2)
	    sage: s.complete_linear_system([1,1,1,1,1,1],1)

	    [(2, 0, 0, 3, 1, 2),
	     (3, 2, 0, 2, 0, 1),
	     (0, 0, 0, 1, 3, 0),
	     (1, 0, 2, 2, 0, 3),
	     (1, 1, 1, 1, 1, 1),
	     (2, 3, 1, 0, 0, 0),
	     (0, 1, 3, 0, 0, 2)]
        """
        eff_divisors = []
        for sigma in self.divisor_polytope(D,k).integral_points():
            E = vector(D) - self._polytope_ieqs[k]*sigma
            eff_divisors.append(E)
        return eff_divisors

    def is_winnable(self, D, k):
        r"""
        Is the k-dimensional divisor D winnable?

        INPUT:

           D - list (representing a k-divisor)
           k - integer

        OUTPUT:

           boolean

        EXAMPLES::

            sage: s = hollow_simplex(2)
            sage: s.is_winnable([-1,0,0,1,0,1],1)
            False
            sage: s.is_winnable([-1,0,0,1,1,1],1)
            True
        """
        return not self.complete_linear_system(D,k)==[]

    def is_minimal_winnable(self, D, k, check=True, witness=1):
        r"""
        Is the k-dimensional divisor D winnable but unwinnable after decreasing any of its
        components by 1?  With check=False, assume D is winnable.  If witness=0,
        then only true/false is returned.  If witness=1, the return value is the
        empty list, [], if minimal, otherwise, a single smaller winnable divisor
        is returned.  If witness=2, then all winnable divisors with one fewer
        dollar are returned.

        INPUT:

          D - list (representing a k-divisor)
          k - integer
          check - boolean
          witness - 0, 1, or 2

        OUTPUT:

          boolean (if witness=0) or list (if witness=1,2)

        EXAMPLE::

        sage: s = hollow_simplex(2)
        sage: s.is_minimal_winnable([-1,0,0,2,1,1],1,witness=0) # not minimal
        False
        sage: s.is_minimal_winnable([-1,0,0,2,1,1],1,witness=1) # a guarantee
        [-1, -1, 0, 2, 1, 1]
        sage: s.is_minimal_winnable([-1,0,0,2,1,1],1,witness=2) # all winnables with one fewer dollar
        [[-1, -1, 0, 2, 1, 1], [-1, 0, 0, 1, 1, 1]]
        """
        if check:
            if not self.is_winnable(D,k):
                print 'ERROR: The input divisor is unwinnable.'
                return
        n = len(D)
        result = []
        for i in range(n):
            F = deepcopy(D)
            F[i] -= 1
            if self.is_winnable(F,k):
                if witness==0:
                    return False
                elif witness==1:
                    return F
                else:
                    result.append(F)
        if witness==0:
            return True
        elif witness==1:
            return []
        else:
            return result

    def find_minimal_winnable(self, D, k):
        r"""
        Find each minimal winnable divisor dominated by the k-dimensional
        divisor D.
        """
        if not self.is_winnable(D,k):
            print "ERROR: input divisor is not winnable."
            return
        active = [D]
        mindivs = []
        while active!=[]:
            F = active.pop()
            divs = self.is_minimal_winnable(F,k,check=False,witness=2)
            if divs==[]:
                if F not in mindivs:
                    mindivs.append(F)
            else:
                print len(active), len(mindivs)
                active = active + divs
        return mindivs

    def zero_divisor(self,k):
        r"""
        The k-dimensional zero divisor.
        """
        return SimplicialDivisor(self,[0]*len(self.n_faces(k)),k)

class SimplicialDivisor(list):
    r"""
    Class for divisor on a simplicial complex.

    EXAMPLES::

        sage: s = ksimplicial_complexes.hollow_simplex(2)
        sage: D = SimplicialDivisor(s,[2,2,1,1,1,1],1)
        sage: D.dim()
        1
        sage: D.face_list()
        [(2, 3), (0, 2), (1, 3), (1, 2), (0, 3), (0, 1)]
        sage: D.effective_div()

        [[3, 0, 1, 4, 0, 4],
         [3, 1, 0, 3, 1, 2],
         [4, 3, 0, 2, 0, 1],
         [1, 0, 1, 2, 2, 2],
         [1, 1, 0, 1, 3, 0],
         [2, 1, 2, 2, 0, 3],
         [2, 2, 1, 1, 1, 1],
         [3, 4, 1, 0, 0, 0],
         [0, 0, 3, 1, 1, 3],
         [0, 1, 2, 0, 2, 1],
         [1, 2, 3, 0, 0, 2]]
        sage: D.is_linearly_equivalent([2,1,2,2,0,3])
        True
        sage: D.is_linearly_equivalent([2,1,2,2,0,3],True)
        (-1, 1, -1, 0, 0, 0)
        sage: D.apply_firing_script([-1,1,-1,0,0,0])
        [2, 1, 2, 2, 0, 3]
        sage: F = D.borrow(0)
        sage: F
        [4, 3, 0, 2, 0, 1]
        sage: F.lend(0) == D
        True
        sage: hb = s.Hilbert_basis(2)
        sage: hb

        [0 1 0 0 1 1]
        [0 1 1 1 1 0]
        [1 0 1 0 1 0]
        sage: D
        [2, 2, 1, 1, 1, 1]
        sage: D.degrees()
        [4, 5, 4]
        sage: m = hb.right_kernel_matrix()
        sage: [SimplicialDivisor(s,i,1).is_winnable() for i in m]
        [False, False, False]
        sage: D = SimplicialDivisor(s,[-2,0,-1,0,5,1],1)
        sage: D.is_winnable()
        True
        sage: D.greedy_algorithm()
        0
        2
        0
        2
        [0, 2, 1, 0, 1, 3]
        sage: D.apply_firing_script([-2,0,-2,0,0,0])
        [0, 2, 1, 0, 1, 3]
        sage: D + D
        [-4, 0, -2, 0, 10, 2]
        sage: 4*D
        [-8, 0, -4, 0, 20, 4]
        sage: D > s.zero_divisor(1)
        False
    """

    def __init__(self, S, D, k):
        r"""
        Create a k-dimensional divisor on a simplicial complex S.

        INPUT:

        - S -- KSimplicialComplex

        - D -- list representing a divisor

        - k -- integer representing the dimension of D

        OUTPUT:

        SimplicialDivisor

        EXAMPLES::

	    sage: s = ksimplicial_complexes.hollow_simplex(2)
	    sage: D = SimplicialDivisor(s,vector([1,2,3,0,0,0]),1)
	    sage: D.__dict__

	    {'_dim': 1,
	     '_face_list': [(2, 3), (0, 2), (1, 3), (1, 2), (0, 3), (0, 1)],
	     '_ksimplicial_complex': Simplicial complex with vertex set (0, 1, 2, 3) and facets {(0, 2, 3), (0, 1, 2), (1, 2, 3), (0, 1, 3)}}
        """
        D = list(D)
        if len(D)!= len(S.n_faces(k)):
            raise SyntaxError(D)
        list.__init__(self,D)
        self._ksimplicial_complex = S
        self._dim = k
        self._face_list = S.n_cells(k)

    def __deepcopy__(self, memo):
        r"""
        Overrides the deepcopy method for dict.

        INPUT:

        memo -- (optional) dict

        EXAMPLES::

	    sage: s = ksimplicial_complexes.hollow_simplex(2)
	    sage: D = SimplicialDivisor(s,vector([1,2,3,0,0,0]),1)
	    sage: E = deepcopy(D)
	    sage: D[0] += 1
	    sage: D
	    [2, 2, 3, 0, 0, 0]
	    sage: E
	    [1, 2, 3, 0, 0, 0]
        """
        D = SimplicialDivisor(self._ksimplicial_complex, list(self), self._dim)
        return D

    def __setitem__(self, key, item):
        r"""
        Overrides the setitem method for dict.

        INPUT:

        ``key``, ``item`` -- objects

        EXAMPLES::   

	    sage: s = ksimplicial_complexes.hollow_simplex(2)
	    sage: D = SimplicialDivisor(s,vector([1,2,3,0,0,0]),1)
	    sage: D.polytope()
	    A 3-dimensional polyhedron in QQ^3 defined as the convex hull of 8 vertices
	    sage: D.__dict__

	    {'_dim': 1,
	     '_face_list': [(2, 3), (0, 2), (1, 3), (1, 2), (0, 3), (0, 1)],
	     '_ksimplicial_complex': Simplicial complex with vertex set (0, 1, 2, 3) and facets {(0, 2, 3), (0, 1, 2), (1, 2, 3), (0, 1, 3)},
	     '_polytope': A 3-dimensional polyhedron in QQ^3 defined as the convex hull of 8 vertices}
	    sage: D[0] += 1
	    sage: D
	    [2, 2, 3, 0, 0, 0]
	    sage: D.__dict__

	    {'_dim': 1,
	     '_face_list': [(2, 3), (0, 2), (1, 3), (1, 2), (0, 3), (0, 1)],
	     '_ksimplicial_complex': Simplicial complex with vertex set (0, 1, 2, 3) and facets {(0, 2, 3), (0, 1, 2), (1, 2, 3), (0, 1, 3)}}

        .. NOTE::

            In the example, above, changing the value of `D` at some vertex makes
            a call to setitem, which resets some of the stored variables for `D`.
        """
        list.__setitem__(self,key,item)
        S = self._ksimplicial_complex
        mydim = self._dim
        facelist = self._face_list
        self.__dict__ = {'_ksimplicial_complex':S, '_dim': mydim, '_face_list': facelist}
    
    def __getattr__(self, name):
        """
        Set certain variables only when called.

        INPUT:

        ``name`` -- name of an internal method

        EXAMPLES::  

	    sage: s = ksimplicial_complexes.hollow_simplex(2)
	    sage: D = SimplicialDivisor(s,vector([1,2,3,0,0,0]),1)
	    sage: D.__dict__

	    {'_dim': 1,
	     '_face_list': [(2, 3), (0, 2), (1, 3), (1, 2), (0, 3), (0, 1)],
	     '_ksimplicial_complex': Simplicial complex with vertex set (0, 1, 2, 3) and facets {(0, 2, 3), (0, 1, 2), (1, 2, 3), (0, 1, 3)}}
	    sage: D.polytope()
	    A 3-dimensional polyhedron in QQ^3 defined as the convex hull of 8 vertices
	    sage: D.__dict__

	    {'_dim': 1,
	     '_face_list': [(2, 3), (0, 2), (1, 3), (1, 2), (0, 3), (0, 1)],
	     '_ksimplicial_complex': Simplicial complex with vertex set (0, 1, 2, 3) and facets {(0, 2, 3), (0, 1, 2), (1, 2, 3), (0, 1, 3)},
	     '_polytope': A 3-dimensional polyhedron in QQ^3 defined as the convex hull of 8 vertices}
        """
        if name not in self.__dict__:
            if name=='_polytope':
                self._set_polytope()
                return self.__dict__[name]
            if name=='_polytope_integral_points':
                self._set_polytope_integral_points()
                return self.__dict__[name]
            if name=='_effective_div':
                self._set_effective_div()
                return self.__dict__[name]
            else:
                raise AttributeError(name)

    def __add__(self, other):
        r"""
        Addition of divisors.

        INPUT:

        ``other`` -- SandpileDivisor

        OUTPUT:

        sum of ``self`` and ``other``

        EXAMPLES::

            sage: s = ksimplicial_complexes.hollow_simplex(2)
            sage: D = SimplicialDivisor(s,vector([1,2,3,0,0,0]),1)
            sage: E = SimplicialDivisor(s,[1,0,0,0,0,0],1)
            sage: D + E
            [2, 2, 3, 0, 0, 0]
        """
        return SimplicialDivisor(self._ksimplicial_complex,vector(self)+vector(other) , self._dim)

    def __mul__(self, other):
        r"""
        Sum of the divisor with itself ``other`` times.

        INPUT:

        ``other`` -- integer

        OUTPUT:

        SimplicialDivisor

        EXAMPLES::  

            sage: s = ksimplicial_complexes.hollow_simplex(2)
            sage: D = SimplicialDivisor(s,vector([1,2,3,0,0,0]),1)
            sage: 3*D
            [3, 6, 9, 0, 0, 0]
            sage: D*3
            [3, 6, 9, 0, 0, 0]
        """
        return SimplicialDivisor(self._ksimplicial_complex,other*vector(self), self._dim)

    def __rmul__(self, other):
        r"""
        The sum of divisor with itself ``other`` times.

        INPUT:

        ``other`` -- Integer

        OUTPUT:

        SimplicialDivisor

        EXAMPLES::  

            sage: s = ksimplicial_complexes.hollow_simplex(2)
            sage: D = SimplicialDivisor(s,vector([1,2,3,0,0,0]),1)
            sage: 3*D
            [3, 6, 9, 0, 0, 0]
            sage: D*3
            [3, 6, 9, 0, 0, 0]
        """
        return SimplicialDivisor(self._ksimplicial_complex,other*vector(self), self._dim)

    def __radd__(self, other):
        r"""
        Right-side addition of divisors.

        INPUT:

        ``other`` -- SimplicialDivisor

        OUTPUT:

        sum of ``self`` and ``other``

        EXAMPLES::  

            sage: s = ksimplicial_complexes.hollow_simplex(2)
            sage: D = SimplicialDivisor(s,vector([1,2,3,0,0,0]),1)
            sage: E = SimplicialDivisor(s,[1,0,0,0,0,0],1)
            sage: D.__radd__(E)
            [2, 2, 3, 0, 0, 0]
            sage: D + E
            [2, 2, 3, 0, 0, 0]
        """
        s = self._ksimplicial_complex
        d = vector(self) + vector(other)
        return SimplicialDivisor(s, d, self._dim)

    def __sub__(self, other):
        r"""
        Subtraction of divisors.

        INPUT:

        ``other`` -- SimplicialDivisor

        OUTPUT:

        Difference of ``self`` and ``other``

        EXAMPLES::  # Update this!

            sage: S = sandpiles.Cycle(3)
            sage: D = SandpileDivisor(S, [1,2,3])
            sage: E = SandpileDivisor(S, [3,2,1])
            sage: D - E
            {0: -2, 1: 0, 2: 2}
        """
        s = self._ksimplicial_complex
        d = vector(self) - vector(other)
        return SimplicialDivisor(s, d, self._dim)

    def __rsub__(self, other):
        r"""
        Right-side subtraction of divisors.

        INPUT:

        ``other`` -- SimplicialDivisor

        OUTPUT:

        Difference of ``self`` and ``other``

        EXAMPLES::  

            sage: s = ksimplicial_complexes.hollow_simplex(2)
            sage: D = SimplicialDivisor(s,vector([1,2,3,0,0,0]),1)
            sage: E = SimplicialDivisor(s,[1,0,0,0,0,0],1)
            sage: D.__rsub__(E)
            [0, -2, -3, 0, 0, 0]
            sage: E - D
            [0, -2, -3, 0, 0, 0]
        """
        s = self._ksimplicial_complex
        d = vector(other) - vector(self)
        return SimplicialDivisor(s, d, self._dim)

    def __neg__(self):
        r"""
        The additive inverse of the divisor.

        OUTPUT:

        SimplicialDivisor

        EXAMPLES::  

	    sage: s = ksimplicial_complexes.hollow_simplex(2)
	    sage: D = SimplicialDivisor(s,[0,0,0,0,0,0],1)
	    sage: -D
	    [0, 0, 0, 0, 0, 0]
	    sage: D = SimplicialDivisor(s,[1,2,3,0,0,0],1)
	    sage: -D
	    [-1, -2, -3, 0, 0, 0]
        """
        return SimplicialDivisor(self._ksimplicial_complex, [-i for i in self],
                self._dim)

    def __le__(self, other):
        r"""
        ``True`` if every component of ``self`` is at most that of
        ``other``.

        INPUT:

        ``other`` -- SimplicialDivisor

        OUTPUT:

        boolean

        EXAMPLES::  

	    sage: s = ksimplicial_complexes.hollow_simplex(2)
	    sage: D = SimplicialDivisor(s,[0,0,0,0,0,0],1)
	    sage: E = SimplicialDivisor(s,[1,0,0,0,0,0],1)
	    sage: F = SimplicialDivisor(s,[1,-1,0,0,0,0],1)
	    sage: D < D
	    False
	    sage: D <= D
	    True
	    sage: D < E
	    True
	    sage: D < F
	    False
        """
        return forall(range(len(self)), lambda e: self[e]<=other[e])[0]

    def __lt__(self, other):
        r"""
        ``True`` if every component of ``self`` is at most that
        of ``other`` and the two divisors are not equal.

        INPUT:

        ``other`` -- SimplicialDivisor

        OUTPUT:

        boolean

        EXAMPLES::  

	    sage: s = ksimplicial_complexes.hollow_simplex(2)
	    sage: D = SimplicialDivisor(s,[0,0,0,0,0,0],1)
	    sage: E = SimplicialDivisor(s,[1,0,0,0,0,0],1)
	    sage: F = SimplicialDivisor(s,[1,-1,0,0,0,0],1)
	    sage: D < D
	    False
	    sage: D <= D
	    True
	    sage: D < E
	    True
	    sage: D < F
	    False
        """
        return self<=other and self!=other

    def __ge__(self, other):
        r"""
        ``True`` if every component of ``self`` is at least that of
        ``other``.

        INPUT:

        ``other`` -- SimplicialDivisor

        OUTPUT:

        boolean

        EXAMPLES::  

	    sage: s = ksimplicial_complexes.hollow_simplex(2)
	    sage: D = SimplicialDivisor(s,[0,0,0,0,0,0],1)
	    sage: E = SimplicialDivisor(s,[1,0,0,0,0,0],1)
	    sage: F = SimplicialDivisor(s,[1,-1,0,0,0,0],1)
	    sage: D > D
	    False
	    sage: D >= D
	    True
	    sage: D > E
	    False
	    sage: D > F
	    False
	    sage: E > F
	    True
	    sage: E >= F
	    True
        """
        return forall(range(len(self)), lambda e: self[e]>=other[e])[0]

    def __gt__(self, other):
        r"""
        ``True`` if every component of ``self`` is at least that
        of ``other`` and the two divisors are not equal.

        INPUT:

        ``other`` -- SimplicialDivisor

        OUTPUT:

        boolean

        EXAMPLES::  

	    sage: s = ksimplicial_complexes.hollow_simplex(2)
	    sage: D = SimplicialDivisor(s,[0,0,0,0,0,0],1)
	    sage: E = SimplicialDivisor(s,[1,0,0,0,0,0],1)
	    sage: F = SimplicialDivisor(s,[1,-1,0,0,0,0],1)
	    sage: D > D
	    False
	    sage: D >= D
	    True
	    sage: D > E
	    False
	    sage: D > F
	    False
	    sage: E > F
	    True
	    sage: E >= F
	    True
        """
        return self>=other and self!=other

    def simplicial_complex(self):
        r"""
        The divisor's underlying ksimplicial complex.

        OUTPUT:

        KSimplicial complex

        EXAMPLES::  

	    sage: s = ksimplicial_complexes.hollow_simplex(2)
	    sage: D = SimplicialDivisor(s,[0,0,0,0,0,0],1)
	    sage: D.simplicial_complex()
	    Simplicial complex with vertex set (0, 1, 2, 3) and facets {(0, 2, 3), (0, 1, 2), (1, 2, 3), (0, 1, 3)}
	    sage: D.simplicial_complex() == s
	    True
        """
        return self._ksimplicial_complex

    def dim(self):
        r"""
        The dimension of the divisor.

        OUTPUT:

        integer

        EXAMPLES::

            sage: load('simp.sage')
            sage: s = ksimplicial_complexes.hollow_simplex(2)
            sage: D = SimplicialDivisor(s,vector([1,2,3,0,0,0]),1)
            sage: D.dim()
            1
        """
        return self._dim

    def face_list(self):
        r"""
        The ordered list of k-faces where k is the dimension of the divisor.

        OUTPUT:

        list

        EXAMPLES::

            sage: s = ksimplicial_complexes.hollow_simplex(2)
            sage: D = SimplicialDivisor(s,vector([1,2,3,0,0,0]),1)
            sage: D.face_list()
            [(2, 3), (0, 2), (1, 3), (1, 2), (0, 3), (0, 1)]
        """
        return copy(self._face_list)

    def is_linearly_equivalent(self, D, with_firing_vector=False):
        r"""
        Is the given divisor linearly equivalent?  Optionally, returns the
        firing vector.  (See NOTE.)

        INPUT:

          D - SimplicialDivisor or list, tuple, etc. representing a divisor

          with_firing_vector - (default: ``False``) boolean

        OUTPUT:

          boolean or integer vector

        EXAMPLES::  

	    sage: s = ksimplicial_complexes.hollow_simplex(2)
	    sage: D = SimplicialDivisor(s,[0,0,0,0,0,0],1)
	    sage: F = D.borrow(0)
	    sage: F
	    [2, 1, -1, 1, -1, 0]
	    sage: D.is_linearly_equivalent(F)
	    True
	    sage: D.is_linearly_equivalent(F,True)
	    (-1, 0, 0, 0, 0, 0)
	    sage: D.is_linearly_equivalent([1,0,0,0,0,0])
	    False
	    sage: D.is_linearly_equivalent([1,0,0,0,0,0],True)
	    ()

        .. NOTE::

            - If ``with_firing_vector`` is ``False``, returns either ``True`` or ``False``.

            - If ``with_firing_vector`` is ``True`` then: (i) if ``self`` is linearly
              equivalent to `D`, returns a vector `v` such that ``self - self.laplacian(self._dim+1)v = D``.
              Otherwise, (ii) if ``self`` is not linearly equivalent to `D`, the output is the empty vector, ``()``.
        """
        # First try to convert D into a vector.
        v = vector(self)
        w = vector(D)
        # Now test for linear equivalence and find firing vector
        S = self._ksimplicial_complex
        lap = S.laplacian(self._dim)
        b = v - w
        if b in lap.image():
            if with_firing_vector:
                return lap.solve_right(b)
            else:
                return True
        else:
            if with_firing_vector:
                return vector([])
            else:
                return False

    def _set_polytope(self):
        r"""
        Compute the polyhedron determining the linear system for D.

        EXAMPLES::  

	    sage: s = ksimplicial_complexes.diamond_complex()
	    sage: D = SimplicialDivisor(s,[1,1,1,1,1],1)
	    sage: D.__dict__

	    {'_dim': 1,
	     '_face_list': [(1, 2), (1, 3), (2, 3), (2, 4), (3, 4)],
	     '_ksimplicial_complex': Simplicial complex with vertex set (1, 2, 3, 4) and facets {(1, 2, 3), (2, 3, 4)}}
	    sage: D._set_polytope()
	    sage: D.__dict__

	    {'_dim': 1,
	     '_face_list': [(1, 2), (1, 3), (2, 3), (2, 4), (3, 4)],
	     '_ksimplicial_complex': Simplicial complex with vertex set (1, 2, 3, 4) and facets {(1, 2, 3), (2, 3, 4)},
	     '_polytope': A 2-dimensional polyhedron in QQ^2 defined as the convex hull of 5 vertices}
        """
        S = self._ksimplicial_complex
        p = S._polytope_ieqs[self._dim]
        myieqs = [[self[i]] + list(-r) for i,r in enumerate(p)] 
        self._polytope = Polyhedron(ieqs=myieqs)

    def polytope(self):
        r"""
        The polytope determining the complete linear system for D.

        OUTPUT:

          Polyhedron

        EXAMPLES::

            sage: s = ksimplicial_complexes.diamond_complex()
            sage: D = SimplicialDivisor(s,[1,1,1,1,1],1)
            sage: D.polytope()
            A 2-dimensional polyhedron in QQ^2 defined as the convex hull of 5 vertices
        """
        return self._polytope

    def _set_polytope_integral_points(self):
        r"""
        Compute the integral points inside the polyhedron determining the linear system for D.

        EXAMPLES:: 

	    sage: s = ksimplicial_complexes.diamond_complex()
	    sage: D = SimplicialDivisor(s,[1,1,0,0,0],1)
	    sage: D.__dict__

	    {'_dim': 1,
	     '_face_list': [(1, 2), (1, 3), (2, 3), (2, 4), (3, 4)],
	     '_ksimplicial_complex': Simplicial complex with vertex set (1, 2, 3, 4) and facets {(1, 2, 3), (2, 3, 4)}}
	    sage: D._set_polytope_integral_points()
	    sage: D.__dict__

	    {'_dim': 1,
	     '_face_list': [(1, 2), (1, 3), (2, 3), (2, 4), (3, 4)],
	     '_ksimplicial_complex': Simplicial complex with vertex set (1, 2, 3, 4) and facets {(1, 2, 3), (2, 3, 4)},
	     '_polytope': A 1-dimensional polyhedron in QQ^2 defined as the convex hull of 2 vertices,
	     '_polytope_integral_points': ((-1, 1), (0, 0))}
        """
        self._polytope_integral_points = self.polytope().integral_points()

    def polytope_integral_points(self):
        r"""
        The integral points inside the polyhedron determining the linear system for D.

        OUTPUT:

        list of vectors

        EXAMPLES::

            sage: s = ksimplicial_complexes.diamond_complex()
            sage: D = SimplicialDivisor(s,[1,1,0,0,0],1)
            sage: D.polytope_integral_points()
            ((-1, 1), (0, 0))
        """
        return deepcopy(self._polytope_integral_points)

    def _set_effective_div(self):
        r"""
        Compute all of the linearly equivalent effective divisors linearly.

        EXAMPLES::  

            sage: s = ksimplicial_complexes.diamond_complex()
            sage: D = SimplicialDivisor(s,[1,1,0,0,0],1)
            sage: D.__dict__

            {'_dim': 1,
             '_face_list': [(1, 2), (1, 3), (2, 3), (2, 4), (3, 4)],
             '_ksimplicial_complex': Simplicial complex with vertex set (1, 2, 3, 4) and facets {(1, 2, 3), (2, 3, 4)}}
            sage: D._set_effective_div()
            sage: D.__dict__

            {'_dim': 1,
             '_effective_div': [[2, 0, 1, 0, 0], [1, 1, 0, 0, 0]],
             '_face_list': [(1, 2), (1, 3), (2, 3), (2, 4), (3, 4)],
             '_ksimplicial_complex': Simplicial complex with vertex set (1, 2, 3, 4) and facets {(1, 2, 3), (2, 3, 4)},
             '_polytope': A 1-dimensional polyhedron in QQ^2 defined as the convex hull of 2 vertices,
             '_polytope_integral_points': ((-1, 1), (0, 0))}
        """
        S = self._ksimplicial_complex
        P = self.polytope()
        dv = vector(self)
        self._effective_div = []
        for sigma in self.polytope_integral_points():
            E = vector(self) - S._polytope_ieqs[self._dim]*sigma
            self._effective_div.append(SimplicialDivisor(S,list(E),self._dim))
    
    def effective_div(self, with_firing_vectors=False):
        r"""
        All linearly equivalent effective divisors.  If with_firing_vector is
        True, the also return the firing script producing the effective divisor.

        INPUT:

          with_firing_vectors - (optional) boolean

        OUTPUT:

          list of SimplicialDivisor if with_firing_vectors=False
          list of [SimplicialDivisor, vector] if with_firing_vectors=True

        EXAMPLES::

            sage: s = ksimplicial_complexes.diamond_complex()
            sage: D = SimplicialDivisor(s,[1,1,0,0,0],1)
            sage: D.effective_div(True)
            [[[2, 0, 1, 0, 0], [0, 0, -1, 0, 1]], [[1, 1, 0, 0, 0], [0, 0, 0, 0, 0]]]
            sage: s = ksimplicial_complexes.diamond_complex()
            sage: D = SimplicialDivisor(s,[1,1,0,0,0],1)
            sage: D.effective_div()
            [[2, 0, 1, 0, 0], [1, 1, 0, 0, 0]]
            sage: D.effective_div(True)
            [[[2, 0, 1, 0, 0], [0, 0, -1, 0, 1]], [[1, 1, 0, 0, 0], [0, 0, 0, 0, 0]]]
            sage: D.apply_firing_script([0,0,-1,0,1])
            [2, 0, 1, 0, 0]
        """
        S = self._ksimplicial_complex
        pts = self.polytope_integral_points()
        nonpivots = [i for i in range(len(self)) if i not in S._pivots[self._dim]]
        effdivs = deepcopy(self._effective_div)
        if with_firing_vectors:
            result = []
            for i, D in enumerate(effdivs):
                int_point = pts[i]
                new = [0]*len(D)
                for p,q in enumerate(int_point):
                    new[nonpivots[p]] = q
                result.append([D,new])
            return result
        else:
            return effdivs

    def is_winnable(self, proof=False):
        r"""
        Is the divisor winnable.  If proof=True, return a linearly equivalent
        effective divisor and a firing script that attains that divisor.  (It
        takes just as long to use the method 'effective_div'.)

        INPUT:

          proof - boolean

        OUTPUT:

          boolean if proof=False
          list [SimplicialDivisor, vector]

        EXAMPLES::

            sage: s = ksimplicial_complexes.diamond_complex()
            sage: D = SimplicialDivisor(s,[-1,1,0,0,0],1)
            sage: D.is_winnable()
            True
            sage: D.is_winnable(True)
            [[0, 0, 1, 0, 0], [0, 0, -1, 0, 1]]
            sage: D.apply_firing_script([0,0,-1,0,1])
            [0, 0, 1, 0, 0]
        """
        if proof:
            result =  self.effective_div(True)[0]
        else:
            if len(self.effective_div()) > 0:
                result = True
            else: result = False
        return result

    def is_minimal_winnable(self, check=True, witness=1):
        r"""
	Is the divisor winnable but unwinnable after decreasing any of its
	components by 1?  With check=False, assume the divisor is winnable.  If
	witness=0, then only true/false is returned.  If witness=1, the return value is
	the empty list, [], if minimal, otherwise, a single smaller winnable divisor is
	returned.  If witness=2, then all winnable divisors with one fewer dollar are
	returned.

        INPUT:

          check - boolean
          witness - 0, 1, or 2

        OUTPUT:

          boolean (if witness=0) or list (if witness=1,2)

        EXAMPLE::

	  sage: s = ksimplicial_complexes.hollow_simplex(2)
	  sage: D = SimplicialDivisor(s,[-1,-1,1,1,1,1],1)
	  sage: D.is_winnable()
	  True
	  sage: D.is_minimal_winnable(witness=0)
	  False
	  sage: D.is_minimal_winnable(witness=1)
	  [-2, -1, 1, 1, 1, 1]
	  sage: D.is_minimal_winnable(witness=2)

	  [[-2, -1, 1, 1, 1, 1],
	   [-1, -2, 1, 1, 1, 1],
	   [-1, -1, 0, 1, 1, 1],
	   [-1, -1, 1, 0, 1, 1],
	   [-1, -1, 1, 1, 1, 0]]
        """
        if check:
            if not self.is_winnable():
                print 'ERROR: Not winnable.'
                return
        n = len(self)
        result = []
        for i in range(n):
            F = deepcopy(self)
            F[i] -= 1
            if F.is_winnable():
                if witness==0:
                    return False
                elif witness==1:
                    return F
                else:
                    result.append(F)
        if witness==0:
            return True
        elif witness==1:
            return []
        else:
            return result

    def find_minimal_winnable(self):
        r"""
        Find each minimal winnable divisor dominated by the k-dimensional
        """
        if not self.is_winnable():
            print "ERROR: input divisor is not winnable."
            return
        active = [D]
        mindivs = []
        while active!=[]:
            F = active.pop()
            divs = F.is_minimal_winnable(check=False,witness=2)
            if divs==[]:
                if F not in mindivs:
                    mindivs.append(F)
            else:
                print len(active), len(mindivs)
                active = active + divs
        return mindivs

    def degrees(self, rays_only=False):
        r"""
        The dot product with each element of the Hilbert basis for the positive
        kernel of k-Laplacian where k is the dimension of the divisor.  If
        rays_only is `True`, the degrees are calculated with respect to the list
        of rays and not necessarily the full Hilbert basis.

        INPUT:

        rays_only - boolean

        OUTPUT:

          list of integers

        EXAMPLES::

            sage: s = diamond_complex()
            sage: D = SimplicialDivisor(s,[1,2,1,1,1],1)
            sage: D.degrees()
            [2, 3, 4]
            sage: s.Hilbert_basis(1)

            [0 0 0 1 1]
            [1 1 0 0 0]
            [0 1 1 1 0]
        """
        S = self._ksimplicial_complex
        return S.divisor_degrees(self,self.dim(),rays_only)
        # return [vector(self)*vector(i) for i in S.Hilbert_basis(self._dim)]

    def is_in_positive_lattice(self, with_coeffs=False):
        r"""
        Is the boundary of the divisor in the positive lattice?  If
        with_coeffs=True return [] if not in the positive lattice, or return the
        coefficients of the boundary as linear combination of the Hilbert basis
        for the positive lattice.

        OUTPUT:

          boolean, [], or integer vector

        EXAMPLES::

            sage: s = ksimplicial_complexes.hollow_simplex(2)
            sage: D = SimplicialDivisor(s,[1,1,1,1,1,1],1)
            sage: D.is_in_positive_lattice()
            True
            sage: D.is_in_positive_lattice(True)
            (3, 3, 4)
            sage: D = SimplicialDivisor(s,[1,1,1,1,-1,-1],1)
            sage: D.is_in_positive_lattice()
            False
            sage: D.is_in_positive_lattice(True)
            []
        """
        s = self.simplicial_complex()
        pl = s.positive_lattice(self._dim)
        b = s.boundary(self._dim)*vector(self)
        if b in pl:
            if with_coeffs:
                return pl.Hilbert_coefficients(b)
            else:
                return True
        else:
            if with_coeffs:
                return []
            else:
                return False

    def positive_lattice_coeffs(self):
        r"""
        If the divisor is in the positive lattice, give its coefficients as a
        linear combination of the Hilbert basis for the positive lattice.  If
        it is not in the positive lattice, return [].
        
        OUTPUT::

        integer vector or []
        """
        return self.is_in_positive_lattice(True)

    def borrow(self, i):
        r"""
        Borrow at the i-th face.

        INPUT:

          i - integer

        OUTPUT:

          SimplicialDivisor

        EXAMPLES::

            sage: s = ksimplicial_complexes.simplex(2)
            sage: s.facets()
            {(0, 1, 2)}
            sage: D = SimplicialDivisor(s,[0,0,0],1)
            sage: D.lend(0)
            [-1, 1, -1]
            sage: D.borrow(0)
            [1, -1, 1]
        """
        s = self._ksimplicial_complex
        D = vector(deepcopy(self))
        D = D + s.laplacian(self._dim).columns()[i]
        return SimplicialDivisor(s, list(D), self._dim)

    def lend(self, i):
        r"""
        Lend at the i-th face.

        INPUT:

          i - integer

        OUTPUT:

          SimplicialDivisor

        EXAMPLES::

            sage: s = ksimplicial_complexes.simplex(2)
            sage: s.facets()
            {(0, 1, 2)}
            sage: D = SimplicialDivisor(s,[0,0,0],1)
            sage: D.lend(0)
            [-1, 1, -1]
            sage: D.borrow(0)
            [1, -1, 1]
        """
        s = self._ksimplicial_complex
        D = vector(deepcopy(self))
        D = D - s.laplacian(self._dim).columns()[i]
        return SimplicialDivisor(s, list(D), self._dim)

    def apply_firing_script(self, script):
        r"""
        Subtract L*script where L is the k-Laplacian.

        INPUT:

          script - vector, list, or SimplicialDivisor

        OUTPUT:

          Simplicial Divisor

        EXAMPLES::

            sage: s = hollow_simplex(2)
            sage: D = SimplicialDivisor(s,[-1,0,5,1,0,0],1)
            sage: D.apply_firing_script([0,0,0,-3,1,2])
            [3, 0, 1, 5, 0, 0]
        """
        s = self._ksimplicial_complex
        lap = s.laplacian(self._dim)
        v = vector(script)
        result = vector(self) - lap*v
        return SimplicialDivisor(s,list(result),self._dim)

    def is_effective(self):
        r"""
        Is the divisor nonnegative?

 	OUTPUT:
        
          boolean

        EXAMPLES::

            sage: s = ksimplicial_complexes.diamond_complex()
            sage: D = SimplicialDivisor(s,[1,1,1,1,1],1)
            sage: D.is_effective()
            True
            sage: D = SimplicialDivisor(s,[1,1,1,1,-1],1)
            sage: D.is_effective()
            False
        """
        s = self._ksimplicial_complex
        return self >= s.zero_divisor(self._dim)

    def greedy_algorithm(self, check=True, version=1):
        r"""
        Version 1: repeatedly borrow at negative k-faces except if the resulting
        divisor has already been seen.  Halt when an equivalent effective
        divisor is achieved or if there are no choices.  If check=True, we first
        check if the divisor is winnable.

        INPUT:

          check - boolean
          version - int

        OUTPUT:

          SimplicialDivisor - if greedy algorithm works

          list of seen SimplicialDivisors and  the current divisor in the search

        EXAMPLES::

	    sage: s = ksimplicial_complexes.hollow_simplex(2)
	    sage: D = SimplicialDivisor(s,[-1,0,5,1,0,0],1)
	    sage: D.is_winnable()
	    True
	    sage: D.greedy_algorithm()
	    0
	    4
	    5
	    1
	    Greedy algorithm does not work

	    ([[-1, 0, 5, 1, 0, 0],
	      [1, 1, 4, 2, -1, 0],
	      [0, 0, 3, 2, 1, -1],
	      [0, -1, 4, 3, 0, 1]],
	     [0, -1, 4, 3, 0, 1])
        """
        if check:
            if not self.is_winnable():
                print 'Not winnable!'
                return
        n = len(self)
        seen = [self]
        active = deepcopy(self)
        in_debt = [i for i in range(n) if self[i]<0]
        in_debt.reverse()
        while in_debt:
            i = in_debt.pop()
            print i
            D = active.borrow(i)
            if D.is_effective():
                return D
            elif D in seen: 
                pass
            else:
                active = deepcopy(D)
                seen.append(D)
                in_debt = [i for i in range(n) if D[i]<0]
                in_debt.reverse()
        print 'Greedy algorithm does not work'
        return seen, active

class KSimplicialComplexExamples(object):
    """
    Some examples of KSimplicialComplexes.

    Here are the available examples; you can also type
    ``ksimplicial_complexes.``  and hit tab to get a list:

    - :meth:`equatorial_bipyramid`
    - :meth:`diamond_complex`
    - :meth:`simplex`
    - :meth:`hollow_simplex`

    EXAMPLES::

            sage: s = ksimplicial_complexes.hollow_simplex(2)
            sage: s.critical()

            [Finitely generated module V/W over Integer Ring with invariants (4, 4),
             Finitely generated module V/W over Integer Ring with invariants (4),
              Finitely generated module V/W over Integer Ring with invariants (0)]
    """

    def __call__(self):
        r"""
        If ksimplicial_complexes() is executed, return a helpful message.

        INPUT:

        None

        OUTPUT:

        None

        EXAMPLES::

	    sage: ksimplicial_complexes()
	    Try ksimplicial_complexes.FOO() where FOO is in the list:

		diamond_complex, equatorial_bipyramid, hollow_simplex
        """
        print('Try ksimplicial_complexes.FOO() where FOO is in the list:\n')
        print("    " + ", ".join([str(i) for i in dir(ksimplicial_complexes)
                                  if i[0] != '_']))

    def equatorial_bipyramid(self):
        """
        The equitorial bipyramid.

        OUTPUT:

        - KSimplicialComplex

        EXAMPLES::

            sage: s = ksimplicial_complexes.equatorial_bipyramid()
            sage: s.facets()
            {(1, 3, 4), (1, 3, 5), (2, 3, 5), (1, 2, 3), (2, 3, 4), (1, 2, 5), (1, 2, 4)}
        """
        return KSimplicialComplex([[1,2,3],[1,2,4],[1,2,5],[1,3,4],[1,3,5],[2,3,4],[2,3,5]])

    def diamond_complex(self):
        """
        The diamond complex (two filled triangles joined along an edge).

        OUTPUT:

        - KSimplicialComplex

        EXAMPLES::

            sage: s = ksimplicial_complexes.diamond_complex()
            sage: s.facets()
            {(1, 2, 3), (2, 3, 4)}
        """
        return KSimplicialComplex([[1,2,3],[2,3,4]])

    def simplex(self, k):
        """
        The k-simplex (k+1 vertices).

        OUTPUT:

        - KSimplicialComplex

        EXAMPLES::

            sage: s = ksimplicial_complexes.simplex(2)
            sage: s.facets()
            {(0, 1, 2)}
        """
        return KSimplicialComplex(simplicial_complexes.Simplex(k))

    def hollow_simplex(self, k):
        """
        The k-simplex (k+1 vertices) with its k-dimensional face removed.

        OUTPUT:

        - KSimplicialComplex

        EXAMPLES::

            sage: s = ksimplicial_complexes.hollow_simplex(2)
            sage: s.facets()
            {(0, 2, 3), (0, 1, 2), (1, 2, 3), (0, 1, 3)}
        """
        return KSimplicialComplex(simplicial_complexes.Sphere(k))

    def square_antiprism(self):
        """
        The hollow square antiprism.

        OUTPUT:

        - KSimplicialComplex

        EXAMPLES::
        """
        return KSimplicialComplex([[1,2,5],[1,5,8],[1,4,8], [2,5,6],[2,3,6],[3,6,7],[3,7,4],[4,7,8]])

    def triangular_antiprism(self):
        """
        The hollow square antiprism.

        OUTPUT:

        - KSimplicialComplex

        EXAMPLES::
        """
        return KSimplicialComplex([[1,2,4],[1,3,6],[1,4,6],[2,3,5],[2,4,5],[3,5,6]])

    def ProjectivePlane(self):
        """
        Minimal triangulation of the real projective plane.

        OUTPUT:

        - KSimplicialComplex

        EXAMPLES::
        """
        return KSimplicialComplex(simplicial_complexes.ProjectivePlane())

    def annulus(self, variant=0):
        r"""
        An annulus with possible attached hollow of filled tetrahedron.

        INPUT:

        variant - integer (0, 1, 2, 3, 4)

        OUTPUT:

        - KSimplicialComplex
        """
        if variant==1:
            f = [(0,1,4),(0,1,6),(0,2,3),(0,3,4),(0,4,6),(1,2,5),(1,4,5),(1,4,6),(2,3,5)]
        elif variant==2:
            f = [(0,1,4),(0,2,3),(0,2,6),(0,3,4),(0,3,6),(1,2,5),(1,4,5),(2,3,5),(2,3,6)]
        elif variant==3:  # filled tetrahedron
            f = [(0,1,4,6),(0,2,3),(0,3,4),(1,2,5),(1,4,5),(2,3,5)]
        elif variant==4:  # filled tetrahedron
            f = [(0,1,4),(0,2,3),(0,3,4,6),(1,2,5),(1,4,5),(2,3,5)]
        else: # plain annulus
            f = [(0,1,4),(0,2,3),(0,3,4),(1,2,5),(1,4,5),(2,3,5)]
        return KSimplicialComplex(f)


ksimplicial_complexes = KSimplicialComplexExamples()
