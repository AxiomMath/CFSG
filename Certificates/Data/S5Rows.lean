module

public import Mathlib.Algebra.Group.Basic
public import Mathlib.Data.List.Basic

public section

namespace Certificates.S5Rows

variable {M : Type*} [Group M] [DecidableEq M]

@[expose] def q8Span (i j : M) : List M :=
  [1, i ^ 2, i, i⁻¹, j, j⁻¹, i * j, j * i]

@[expose] def q8RelB (i j : M) : Bool :=
  decide (i ^ 4 = 1) && !decide (i ^ 2 = 1) && decide (i ^ 2 = j ^ 2) &&
    decide (j⁻¹ * i * j = i⁻¹)

@[expose] def threeCycB (y i j : M) : Bool :=
  decide (y⁻¹ * i * y = j) && (decide (y⁻¹ * j * y = i * j) || decide (y⁻¹ * j * y = j * i))

@[expose] def threeCycCheck (L Y : List M) (p : M → Bool) : Bool :=
  L.all fun i => L.all fun j => !(q8RelB i j && p i && p j) || Y.any fun y => threeCycB y i j

@[expose] def conjMulB (n i j : M) : Bool :=
  decide (n⁻¹ * i * n ∈ q8Span i j) &&
    (decide (n⁻¹ * j * n = j * i) || decide (n⁻¹ * j * n = j * i⁻¹))

@[expose] def conjMulCheck (L Y : List M) (p : M → Bool) : Bool :=
  L.all fun i => L.all fun j => !(q8RelB i j && p i && !p j) || Y.any fun n => conjMulB n i j

@[expose] def outerPairs (L : List M) (p : M → Bool) : List (M × M) :=
  L.flatMap fun i => (L.filter fun j => q8RelB i j && !(p i && p j)).map fun j => (i, j)

@[expose] def uniqueOuterCheck (L : List M) (p : M → Bool) : Bool :=
  (outerPairs L p).all fun a => (outerPairs L p).all fun b =>
    decide (a.1 ∈ q8Span b.1 b.2) && decide (a.2 ∈ q8Span b.1 b.2)

@[expose] def invPairB (f : M → ℕ) (u x i j : M) : Bool :=
  decide (u * u = 1) && !decide (u = 1) && decide (u⁻¹ * i * u ∈ q8Span i j) &&
    decide (u⁻¹ * j * u ∈ q8Span i j) && decide (u * x * (u * x) = 1) && !decide (u * x = 1) &&
    !decide (f u = f (u * x))

@[expose] def invPairCheck (L : List M) (f : M → ℕ) : Bool :=
  L.all fun i => L.all fun j => !q8RelB i j || L.any fun u => (q8Span i j).any fun x =>
    invPairB f u x i j

end Certificates.S5Rows
