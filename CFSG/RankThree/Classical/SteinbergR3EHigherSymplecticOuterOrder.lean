module

public import CFSG.LocalAnalysis.ComponentInitial.SymplecticPerfectCoverOuterPrime

public section

namespace CFSG.RankThree.Classical

open CFSG.Assembly.LowTwoRank CFSG.LocalAnalysis.ComponentInitial.SymplecticHigher
open CFSG.ComponentClassification.OuterAutomorphisms (Outer inner)

theorem higher_symplectic_outer_order_divides_field_multiplier_bound {ℓ f r : ℕ}
    (hℓ : ℓ.Prime) (hf : 1 ≤ f) (hr : 3 ≤ r) {K : Type} [Field K] (hK : Nat.card K = ℓ ^ f) :
    Nat.card (Outer (StatedProj (StatedSp r K))) ∣ f * Nat.gcd 2 (ℓ ^ f - 1) ∧
      Nat.card (Outer (StatedProj (StatedSp r K))) ∣ f * (ℓ ^ f - 1) := by
  have : Finite K := Nat.finite_of_card_ne_zero (by rw [hK]; exact (pow_pos hℓ.pos f).ne')
  have : NeZero r := ⟨by omega⟩
  obtain ⟨hID, -⟩ := standard_outer_quotient (K := K) (by omega : 1 ≤ r)
  have hID' : inner (StatedProj (StatedSp r K)) ≤ spLinearAutGroup r K := hID
  have hE : spSemilinearAutGroup r K = ⊤ := (automorphism_generation (K := K) hr).1
  have hidx : Nat.card (Outer (StatedProj (StatedSp r K))) =
      (inner (StatedProj (StatedSp r K))).relIndex (spLinearAutGroup r K) *
        ((spLinearAutGroup r K).relIndex (spSemilinearAutGroup r K) *
          (spSemilinearAutGroup r K).index) := by
    rw [Subgroup.relIndex_mul_index spLinearAutGroup_le_spSemilinearAutGroup,
      Subgroup.relIndex_mul_index hID']
    rfl
  rw [hE, Subgroup.index_top, mul_one] at hidx
  have ha := relIndex_inner_spLinearAutGroup_dvd (r := r) hℓ hf hK
  have hb := relIndex_spLinearAutGroup_dvd (r := r) hℓ hf hK
  rw [hE] at hb
  have h1 : Nat.card (Outer (StatedProj (StatedSp r K))) ∣ f * Nat.gcd 2 (ℓ ^ f - 1) := by
    rw [hidx, mul_comm f]
    exact Nat.mul_dvd_mul ha hb
  exact ⟨h1, h1.trans (Nat.mul_dvd_mul_left f (Nat.gcd_dvd_right 2 _))⟩

end CFSG.RankThree.Classical
