module

public import CFSG.Blueprint.Chevalley
public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.Algebra.Group.Submonoid.Membership
public import Mathlib.Data.Matrix.Mul
public import Mathlib.Data.ZMod.Basic

public section

namespace CFSG.StandardType.NTPlane

open CFSG.Blueprint.Chevalley

abbrev X3 : Type := Fin Tag.E6.rank → ZMod 3

@[expose] def pairVec (x : X3) (v : Fin Tag.E6.rank → ℤ) : ZMod 3 :=
  ∑ i, x i * (v i : ZMod 3)

@[expose] def dualRefl (i : Fin Tag.E6.rank) (x : X3) : X3 :=
  fun c => x c - x i * ((Tag.E6.cartan i c : ℤ) : ZMod 3)

@[expose] def applyWord (l : List (Fin Tag.E6.rank)) (x : X3) : X3 :=
  l.foldr dualRefl x

@[expose] def reps : Fin 7 → X3 :=
  ![![0, 0, 0, 0, 0, 1], ![0, 0, 0, 0, 0, 2], ![0, 0, 0, 0, 1, 1], ![0, 0, 0, 1, 0, 0],
    ![0, 0, 1, 1, 1, 0], ![0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 2, 0]]

@[expose] def repOrbitSize : Fin 7 → ℕ := ![27, 27, 72, 80, 90, 216, 216]

@[expose] def repKerCard : Fin 7 → ℕ := ![40, 40, 30, 18, 24, 22, 22]

@[expose] def repKerGroupOrder : Fin 7 → ℕ := ![1920, 1920, 720, 216, 192, 240, 240]

@[expose] def kerRoots (x : X3) : Set (Fin Tag.E6.rank → ℤ) :=
  {α | IsRoot Tag.E6 α ∧ pairVec x α = 0}

@[expose] def reflMatRoot (α : Fin Tag.E6.rank → ℤ) :
    Matrix (Fin Tag.E6.rank) (Fin Tag.E6.rank) ℤ :=
  1 - Matrix.vecMulVec α (Tag.E6.cartan.mulVec α)

@[expose] def kerReflSet (x : X3) : Set (Matrix (Fin Tag.E6.rank) (Fin Tag.E6.rank) ℤ) :=
  {M | ∃ α ∈ kerRoots x, M = reflMatRoot α}

@[expose] def e6RootList : List (Fin Tag.E6.rank → ℤ) :=
  [![-1, -2, -2, -3, -2, -1],
   ![-1, -1, -2, -3, -2, -1],
   ![-1, -1, -2, -2, -2, -1],
   ![-1, -1, -2, -2, -1, -1],
   ![-1, -1, -2, -2, -1, 0],
   ![-1, -1, -1, -2, -2, -1],
   ![-1, -1, -1, -2, -1, -1],
   ![-1, -1, -1, -2, -1, 0],
   ![-1, -1, -1, -1, -1, -1],
   ![-1, -1, -1, -1, -1, 0],
   ![-1, -1, -1, -1, 0, 0],
   ![-1, 0, -1, -1, -1, -1],
   ![-1, 0, -1, -1, -1, 0],
   ![-1, 0, -1, -1, 0, 0],
   ![-1, 0, -1, 0, 0, 0],
   ![-1, 0, 0, 0, 0, 0],
   ![0, -1, -1, -2, -2, -1],
   ![0, -1, -1, -2, -1, -1],
   ![0, -1, -1, -2, -1, 0],
   ![0, -1, -1, -1, -1, -1],
   ![0, -1, -1, -1, -1, 0],
   ![0, -1, -1, -1, 0, 0],
   ![0, -1, 0, -1, -1, -1],
   ![0, -1, 0, -1, -1, 0],
   ![0, -1, 0, -1, 0, 0],
   ![0, -1, 0, 0, 0, 0],
   ![0, 0, -1, -1, -1, -1],
   ![0, 0, -1, -1, -1, 0],
   ![0, 0, -1, -1, 0, 0],
   ![0, 0, -1, 0, 0, 0],
   ![0, 0, 0, -1, -1, -1],
   ![0, 0, 0, -1, -1, 0],
   ![0, 0, 0, -1, 0, 0],
   ![0, 0, 0, 0, -1, -1],
   ![0, 0, 0, 0, -1, 0],
   ![0, 0, 0, 0, 0, -1],
   ![0, 0, 0, 0, 0, 1],
   ![0, 0, 0, 0, 1, 0],
   ![0, 0, 0, 0, 1, 1],
   ![0, 0, 0, 1, 0, 0],
   ![0, 0, 0, 1, 1, 0],
   ![0, 0, 0, 1, 1, 1],
   ![0, 0, 1, 0, 0, 0],
   ![0, 0, 1, 1, 0, 0],
   ![0, 0, 1, 1, 1, 0],
   ![0, 0, 1, 1, 1, 1],
   ![0, 1, 0, 0, 0, 0],
   ![0, 1, 0, 1, 0, 0],
   ![0, 1, 0, 1, 1, 0],
   ![0, 1, 0, 1, 1, 1],
   ![0, 1, 1, 1, 0, 0],
   ![0, 1, 1, 1, 1, 0],
   ![0, 1, 1, 1, 1, 1],
   ![0, 1, 1, 2, 1, 0],
   ![0, 1, 1, 2, 1, 1],
   ![0, 1, 1, 2, 2, 1],
   ![1, 0, 0, 0, 0, 0],
   ![1, 0, 1, 0, 0, 0],
   ![1, 0, 1, 1, 0, 0],
   ![1, 0, 1, 1, 1, 0],
   ![1, 0, 1, 1, 1, 1],
   ![1, 1, 1, 1, 0, 0],
   ![1, 1, 1, 1, 1, 0],
   ![1, 1, 1, 1, 1, 1],
   ![1, 1, 1, 2, 1, 0],
   ![1, 1, 1, 2, 1, 1],
   ![1, 1, 1, 2, 2, 1],
   ![1, 1, 2, 2, 1, 0],
   ![1, 1, 2, 2, 1, 1],
   ![1, 1, 2, 2, 2, 1],
   ![1, 1, 2, 3, 2, 1],
   ![1, 2, 2, 3, 2, 1]]

theorem card_closure_of_closed {M : Type*} [Monoid M] [DecidableEq M] (S : Set M) (ℓ : List M)
    (hnd : ℓ.Nodup) (h1 : 1 ∈ ℓ) (hcl : ∀ g ∈ ℓ, ∀ s ∈ S, g * s ∈ ℓ)
    (hreach : ∀ g ∈ ℓ, g ∈ Submonoid.closure S) :
    Nat.card (Submonoid.closure S) = ℓ.length := by
  have hsub : ∀ g : M, g ∈ Submonoid.closure S ↔ g ∈ ℓ := by
    intro g
    constructor
    · intro hg
      induction hg using Submonoid.closure_induction_right with
      | one => exact h1
      | mul_right x _ y hy ih => exact hcl x ih y hy
    · exact hreach g
  have hset : (Submonoid.closure S : Set M) = ↑ℓ.toFinset := by
    ext g
    simpa using hsub g
  have e : Nat.card (Submonoid.closure S) = (Submonoid.closure S : Set M).ncard :=
    (Nat.card_coe_set_eq (Submonoid.closure S : Set M))
  rw [e, hset, Set.ncard_coe_finset, List.toFinset_card_of_nodup hnd]

end CFSG.StandardType.NTPlane

end
