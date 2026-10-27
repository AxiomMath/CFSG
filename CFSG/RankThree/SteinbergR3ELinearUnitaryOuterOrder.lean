module

public import CFSG.LocalAnalysis.ComponentInitial.UnitaryHigherLinearOuterOrder
public import CFSG.LocalAnalysis.ComponentInitial.UnitaryDiagonalOuterOrder
public import CFSG.LocalAnalysis.ComponentInitial.LinearCoverModel

public noncomputable section

namespace CFSG.RankThree.OuterOrder

open CFSG.Assembly.LowTwoRank
open CFSG.ComponentClassification.OuterAutomorphisms (Outer inner equivalence)
open CFSG.LocalAnalysis.ComponentInitial

@[expose] def determinantParameter (τ : StatedLieTag) (n q : ℕ) : ℕ :=
  match τ with
  | .PSL => Nat.gcd n (q - 1)
  | .PSU => Nat.gcd n (q + 1)
  | _ => 0

theorem mem_inner_of_orderOf_eq_five {T : Type} [Group T] [Finite T] {m : ℕ}
    (hout : Nat.card (Outer T) ∣ m) (h5 : ¬ 5 ∣ m) {α : MulAut T} (hα : orderOf α = 5) :
    α ∈ inner T := by
  have : Finite (MulAut T) := inferInstance
  set π := QuotientGroup.mk' (inner T) with hπ
  have h1 : orderOf (π α) ∣ 5 := hα ▸ orderOf_map_dvd π α
  have h2 : orderOf (π α) ∣ m := (orderOf_dvd_natCard (π α)).trans hout
  have h3 : orderOf (π α) = 1 := by
    rcases (Nat.dvd_prime (by norm_num)).1 h1 with h | h
    · exact h
    · exact absurd (h ▸ h2) h5
  rw [orderOf_eq_one_iff, hπ, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at h3
  exact h3

theorem higher_linear_unitary_outer_order_determinant_bound {T : Type} [Group T] [Finite T]
    {τ : StatedLieTag} (hτ : τ = .PSL ∨ τ = .PSU) {n ℓ f : ℕ} (hn : 3 ≤ n) (hℓ : ℓ.Prime)
    (hf : 1 ≤ f) (hT : StatedClassicalModel T τ n ℓ f) :
    Nat.card (Outer T) ∣ 2 * f * determinantParameter τ n (ℓ ^ f) ∧
      ∀ α : MulAut T, orderOf α = 5 → ¬ 5 ∣ f * determinantParameter τ n (ℓ ^ f) →
        α ∈ inner T := by
  have hout : Nat.card (Outer T) ∣ 2 * f * determinantParameter τ n (ℓ ^ f) := by
    rcases hτ with rfl | rfl
    · obtain ⟨-, K, _, _, hK, ⟨e⟩⟩ := hT
      have e' : T ≃* LinearFlag.projectiveSL n K :=
        (e.trans (projectiveSpecialLinearGroupEquivStatedProj n K).symm).trans
          (LinearCover.projectiveSpecialLinearEquivProjectiveSL n K)
      rw [Nat.card_congr (equivalence e').toEquiv]
      exact UnitaryHigher.higher_linear_outer_order_divides_field_gcd_bound hℓ hf hn hK
    · obtain ⟨⟨-, -, hadm⟩, K, _, _, hK, ⟨e⟩⟩ := hT
      have hq : (n, ℓ ^ f) ≠ (3, 2) := (show 3 ≤ n ∧ (n, ℓ ^ f) ≠ (3, 2) from hadm).2
      have h : UnitaryFieldData ℓ f K := ⟨hℓ, hf, by rw [hK, ← pow_mul, mul_comm]⟩
      have hq' : ¬(n = 3 ∧ ℓ ^ f = 2) := fun ⟨h1, h2⟩ => hq (by rw [h1, h2])
      have e' : T ≃* ClassicalGroups.UnitaryFlag.unitaryPSU h n :=
        e.trans (ClassicalGroups.UnitaryFlag.unitaryPSUEquiv h (by omega)).symm
      obtain ⟨-, -, -, -, hcard, -⟩ := UnitaryHigher.unitary_full_diagonal_outer_order h hn hq'
      rw [Nat.card_congr (equivalence e').toEquiv, hcard]
      rfl
  refine ⟨hout, fun α hα h5 => mem_inner_of_orderOf_eq_five hout ?_ hα⟩
  intro h
  rw [mul_assoc] at h
  rcases (Nat.Prime.dvd_mul (by norm_num)).1 h with h2 | h2
  · norm_num at h2
  · exact h5 h2

end CFSG.RankThree.OuterOrder
