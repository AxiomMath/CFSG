module

public import Mathlib.GroupTheory.Sylow
import Mathlib.GroupTheory.Nilpotent

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UCK

@[expose] def SylowCenterLeCommutator (X : Type) [Group X] : Prop :=
  ∀ T : Sylow 3 X, ∀ x ∈ Subgroup.center ↥(T : Subgroup X), x ^ 3 = 1 →
    x ∈ commutator ↥(T : Subgroup X)

theorem center_le_commutator_of_card_center_eq_prime {p : ℕ} [Fact p.Prime] {T : Type} [Group T]
    [Finite T] (hT : IsPGroup p T) (hnc : ¬ IsMulCommutative T)
    (hZ : Nat.card (Subgroup.center T) = p) : Subgroup.center T ≤ commutator T := by
  haveI : Group.IsNilpotent T := hT.isNilpotent
  have hne : commutator T ≠ ⊥ := fun h => hnc ((commutator_eq_bot_iff T).mp h)
  have h1 : commutator T ⊓ Subgroup.center T ≠ ⊥ :=
    Group.IsNilpotent.inf_center_ne_bot_of_normal hne
  have hdvd : Nat.card ↥(commutator T ⊓ Subgroup.center T) ∣ p :=
    hZ ▸ Subgroup.card_dvd_of_le inf_le_right
  have hne1 : Nat.card ↥(commutator T ⊓ Subgroup.center T) ≠ 1 := fun h =>
    h1 (Subgroup.card_eq_one.mp h)
  have hcard : Nat.card ↥(commutator T ⊓ Subgroup.center T) = p :=
    ((Nat.dvd_prime (Fact.out : p.Prime)).mp hdvd).resolve_left hne1
  have heq : commutator T ⊓ Subgroup.center T = Subgroup.center T :=
    Subgroup.eq_of_le_of_card_ge inf_le_right (by rw [hcard, hZ])
  exact heq ▸ inf_le_left

end CFSG.LocalAnalysis.UniquenessCase.UCK
