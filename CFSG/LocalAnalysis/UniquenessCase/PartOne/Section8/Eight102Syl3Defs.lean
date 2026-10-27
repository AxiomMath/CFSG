module

public import CFSG.ClassicalGroups.UnitaryFlag.HyperbolicData

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.Syl3

open Matrix CFSG.ClassicalGroups.UnitaryFlag CFSG.LocalAnalysis.ComponentInitial CFSG.Open

@[expose] def OmegaNine (X : Type) [Group X] (S : Subgroup X) : Prop :=
  ∃ E : Subgroup X, E ≤ S ∧ IsElemAbelian 3 E ∧ Nat.card E = 9 ∧ ∀ s ∈ S, s ^ 3 = 1 → s ∈ E

@[expose] def FixOmega (X : Type) [Group X] (S : Subgroup X) : Prop :=
  ∀ α : MulAut X, (∃ k : ℕ, α ^ (3 ^ k) = 1) → (∀ s ∈ S, α s ∈ S) →
    ∀ s ∈ S, s ^ 3 = 1 → α s = s

variable {p f : ℕ} {K : Type} [Field K]

@[expose] noncomputable def torusPow (h : UnitaryFieldData p f K) (r ε m : ℕ) :
    Subgroup (hypSU h r ε) where
  carrier := {g | ∃ a : Fin r → Kˣ, (∀ i, a i ^ m = 1) ∧
    ((g : GL (HypIndex r ε) K) : Matrix (HypIndex r ε) (HypIndex r ε) K) =
      diagonal (torusEntries h a 1)}
  mul_mem' := by
    rintro g g' ⟨a, ha, hg⟩ ⟨a', ha', hg'⟩
    refine ⟨a * a', fun i => by rw [Pi.mul_apply, mul_pow, ha, ha', one_mul], ?_⟩
    rw [Subgroup.coe_mul, Units.val_mul, hg, hg', diagonal_mul_diagonal]
    congr 1
    funext x
    rcases x with i | k | i <;> simp [torusEntries, mul_comm]
  one_mem' := ⟨1, fun i => one_pow _, by
    rw [Subgroup.coe_one, Units.val_one, ← diagonal_one]
    congr 1
    funext x
    rcases x with i | k | i <;> simp [torusEntries]⟩
  inv_mem' := by
    rintro g ⟨a, ha, hg⟩
    refine ⟨a⁻¹, fun i => by rw [Pi.inv_apply, inv_pow, ha, inv_one], ?_⟩
    rw [Subgroup.coe_inv]
    refine Units.inv_eq_of_mul_eq_one_right ?_
    rw [hg, diagonal_mul_diagonal, ← diagonal_one]
    congr 1
    funext x
    rcases x with i | k | i <;> simp [torusEntries]

theorem mem_torusPow {h : UnitaryFieldData p f K} {r ε m : ℕ} {g : hypSU h r ε} :
    g ∈ torusPow h r ε m ↔ ∃ a : Fin r → Kˣ, (∀ i, a i ^ m = 1) ∧
      ((g : GL (HypIndex r ε) K) : Matrix (HypIndex r ε) (HypIndex r ε) K) =
        diagonal (torusEntries h a 1) :=
  Iff.rfl

end CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.Syl3
