import Mathlib.Data.Matrix.Defs
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Matrix.Notation
import DMT1.Lectures.L10_algebra.vector.vector

open DMT1.Algebra.Vector


/- @@@

# Matrix M N α



An M × N matrix with entries of type α is represented

as a value of type Matrix m n α. That is then defined

to be the function type M → N → α. Indices thus range

over values of arbitrary types. For finite index sets

we will use Fin types for both rows and columns. Matrix

(Fin m) (Fin n) α is thus the type of 2 x 2 matrices,

indexing from [0, 1] in each dimension to α elements.

@@@ -/



open Matrix



/- @@@

Here's an example of a 2 x 2 rational matrix using

standard natural number indexing and notation that

comes with Lean's Matrix types.

@@@ -/

def myMatrix : Matrix (Fin 2) (Fin 2) ℚ :=

 ![![1, 0],

 ![0, 2]]


/- @@@

## Linear Equivalences

Let's now jump stright from α matrices to linear

equivalences. A linear equivalence is a bijective

function between two linear spaces. You can think

of there being a function that maps vectors from

one module to corresponding vectors in the other,

the inverse function. That it's a bijection means

every object goes to a unique object in the other

module and comes right back under *inverse*.



For us, a linear equivalence will be between two

*modules*, where scalars can lack multiplicative

inverses. So in general there are no fractions or

fractions of actions in modules. To make a module,

which is almost a vector space, into one, give it

multiplicative inverses.

@@@ -/


/- @@@

## Between Modules



We have already established that our *Vc* vectors

form a module, formalized as *Module α (Vc α n)]*:

the type of module with *Vc* objects as the vectors

with α scalars. They also form a vector space with

α being an *field*. As ℚ is a field, we are working

with vector spaces without that being explicit.



So let's think about what a linear equivalence will

look like between *Module α (Vc α n)]* and itself.

A forward function would transform any vector in the

space to a corresponding vector in the same space,

with the inverse function taking that object back

to the start.



On the proverbial left, we have a Module α (Vc α n)]

and another one on the right. In between we'll need

representation of the forward and inverse functions.



The standard computation-oriented representation of

a linear mapping in linear algebra is as a matrix of

scalars. That's what we should use here.



Now we want not just any linear mapping but one that

is bijective, thus also invertible. So in addition

to representing a linear equivalence as a matrix we

can add a a proof that that matrix and thus the map

is invertible.



One way to know is to check whether its determinant

is zero. Another possible design would require that

the client pass two matrices, one the inverse of the

other, with a proof that's true in any instance (you

can again always *sorry* out your proofs as a way to

make progress).

@@@ -/




/- @@@

## TO DO



### A. Define a LinEqSelf type



Building on what we've provided define a *LinEqSelf*

type for representing linear equivalences between a

module and itself. Parameters will probably have to

include the shared scalar type, α, the *vector* type,

for us it's *Vc α n*, and and one or two α matrices

that specify the intended map and its inverse.

--/

/-
Group Members:
Leena Bacha
Kathleen O'Donovan
Brooke Hewitt
-/

#check Matrix

-- Type
structure LinEqSelf (α : Type u) [CommRing α] (n : ℕ) : Type u where
    (mat : Matrix (Fin n) (Fin n) α)
    (inv_mat : Matrix (Fin n) (Fin n) α)
    (left_inv : mat * inv_mat = 1)
    (right_inv : inv_mat * mat = 1)

-- Function to apply matrix to a vector
def toFun [CommRing α] : (LinEqSelf α n) → (Vc α n) → (Vc α n) :=
  fun m v => ⟨m.mat.mulVec v.toRep⟩

-- Function to apply inverse matrix to a vector
def invFun [CommRing α] : (LinEqSelf α n) → (Vc α n) → (Vc α n) :=
  fun m v => ⟨m.inv_mat.mulVec v.toRep⟩

/-
### B. Give Some Examples



Instantiate your type with different transformation

matrices. If you can, show examples, in 1, 2, and 3

dimensions. You'll need some kind of function to apply

the map, or its inverse, to a given vector.
-/

-- 1 dimension (1x1)
def matrix1 : Matrix (Fin 1) (Fin 1) ℚ := ![![3]]

def matrixInv1 : Matrix (Fin 1) (Fin 1) ℚ := ![![1/3]]

instance left_inv1 : matrix1 * matrixInv1 = 1 :=
    by
        ext i j
        fin_cases i
        fin_cases j
        simp [matrix1, matrixInv1, Matrix.mul_apply]

instance right_inv1 : matrixInv1 * matrix1 = 1 :=
    by
        ext i j
        fin_cases i
        fin_cases j
        simp [matrix1, matrixInv1, Matrix.mul_apply]

def LinEqSelf1 : LinEqSelf ℚ 1 :=
{
    mat := matrix1,
    inv_mat := matrixInv1,
    left_inv := left_inv1,
    right_inv := right_inv1,
}

def vc1 : Vc ℚ 1 := ⟨![2]⟩

#eval LinEqSelf1.mat * LinEqSelf1.inv_mat = 1 -- true
#eval LinEqSelf1.inv_mat * LinEqSelf1.mat = 1 -- true
#eval toFun LinEqSelf1 vc1 -- [6]
#eval invFun LinEqSelf1 vc1 -- [2/3]


-- 2 dimensions (2x2)
def matrix2 : Matrix (Fin 2) (Fin 2) ℚ :=
    ![![1, 0],
    ![0, 2]]

def matrixInv2 : Matrix (Fin 2) (Fin 2) ℚ :=
    ![![1, 0],
    ![0, 1/2]]

instance left_inv2 : matrix2 * matrixInv2 = 1 :=
    by
        ext i j
        fin_cases i <;>
        fin_cases j <;>
        simp [matrix2, matrixInv2, Matrix.mul_apply]

instance right_inv2 : matrixInv2 * matrix2 = 1 :=
    by
        ext i j
        fin_cases i <;>
        fin_cases j <;>
        simp [matrix2, matrixInv2, Matrix.mul_apply]

def LinEqSelf2 : LinEqSelf ℚ 2 :=
{
    mat := matrix2,
    inv_mat := matrixInv2,
    left_inv := left_inv2,
    right_inv := right_inv2,
}

def vc2 : Vc ℚ 2 := ⟨![1, 2]⟩

#eval LinEqSelf2.mat * LinEqSelf2.inv_mat = 1 -- true
#eval LinEqSelf2.inv_mat * LinEqSelf2.mat = 1 -- true
#eval toFun LinEqSelf2 vc2 -- [1, 4]
#eval invFun LinEqSelf2 vc2 -- [1, 1]

-- 3 dimensions (3x3)
def matrix3 : Matrix (Fin 3) (Fin 3) ℚ :=
    ![![5, 8, 7],
    ![2, 3, 1],
    ![4, 2, 9]]

def matrixInv3 : Matrix (Fin 3) (Fin 3) ℚ :=
    ![![-25/43, 58/43, 13/43],
    ![14/43, -17/43, -9/43],
    ![8/43, -22/43, 1/43]]

instance left_inv3 : matrix3 * matrixInv3 = 1 :=
    by
        ext i j
        fin_cases i <;>
        fin_cases j <;>
        simp [matrix3, matrixInv3, Matrix.mul_apply, Fin.sum_univ_succ]
        case «0».«0» => norm_num
        case «0».«1» => norm_num
        case «0».«2» => norm_num
        case «1».«0» => norm_num
        case «1».«1» => norm_num
        case «1».«2» => norm_num
        case «2».«0» => norm_num
        case «2».«1» => norm_num
        case «2».«2» => norm_num


instance right_inv3 : matrixInv3 * matrix3 = 1 :=
    by
        ext i j
        fin_cases i <;>
        fin_cases j <;>
        simp [matrix3, matrixInv3, Matrix.mul_apply, Fin.sum_univ_succ]
        case «0».«0» => norm_num
        case «0».«1» => norm_num
        case «0».«2» => norm_num
        case «1».«0» => norm_num
        case «1».«1» => norm_num
        case «1».«2» => norm_num
        case «2».«0» => norm_num
        case «2».«1» => norm_num
        case «2».«2» => norm_num


def LinEqSelf3 : LinEqSelf ℚ 3 :=
{
    mat := matrix3,
    inv_mat := matrixInv3,
    left_inv := left_inv3,
    right_inv := right_inv3,
}

def vc3 : Vc ℚ 3 := ⟨![5, 2, 4]⟩

#eval LinEqSelf3.mat * LinEqSelf3.inv_mat = 1 -- true
#eval LinEqSelf3.inv_mat * LinEqSelf3.mat = 1 -- true
#eval toFun LinEqSelf3 vc3 -- [69, 20, 60]
#eval invFun LinEqSelf3 vc3 -- [1, 0, 0]


/-
### C. Organize as Extension



Organize your work as an extension of the cleaned up

design for affine spaces in Chapter 10. You will add

a linEqSelf directory, with one file linEqSelf.lean).



### D. To submit



Zip and submit your extended version of the codebase

we provided.

@@@ -/



/- @@@

## Extra Credit



- Generalize to maps between different modules then

show, by instantiating your type, that there's a linear

equivalence between *Vc* and *Fin n → α* values under

all the usual operations.

- Define a function or new constructor that allows one

to create a linear equivalence by giving not a matrix

(or two) but an n-tuple of vectors, each intended to be

the image of the corresponding unit vector under the map.

- Pick any element of the problem space to formalize and

automate, do something interesting, and explain briefly

what you did, with a pointer to your code.

@@@ -/
