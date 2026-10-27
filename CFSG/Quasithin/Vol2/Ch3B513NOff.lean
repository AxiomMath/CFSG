module

public import CFSG.Quasithin.Vol2.Ch3B513NBasic

public section

namespace CFSG.Quasithin.B513N

variable {W : Type} [CommGroup W] [Finite W]

theorem index_fixV_le_card {G A : Subgroup (MulAut W)} (hA : IsFFStarOffender G A) :
    (fixV A).index ≤ Nat.card A := by
  have h := hA.2.2.2 ⊥ bot_le
  rw [B1.card_bot_mul_card_fixV, B1.card_eq_index_mul A] at h
  exact Nat.le_of_mul_le_mul_right h Nat.card_pos

theorem hasGood_of_offender_le (hW : ∀ w : W, w ^ 2 = 1) {G D : Subgroup (MulAut W)}
    (hD : IsFFStarMin G D) {S : Subgroup W} (hS : commV D ≤ S)
    (hcard : Nat.card ↥(fixV D ⊓ S) ≤ Nat.card D ^ 2) : HasGood G := by
  have hquad : IsQuadratic D := B1_4_3 hW hD
  exact ⟨D, hD.1.1, hD.1.2.1, hD.1.2.2.1, Or.inr ⟨hquad,
    (Subgroup.card_le_of_le (le_inf hquad hS)).trans hcard⟩⟩

theorem hasGood_of_offender_small (hW : ∀ w : W, w ^ 2 = 1) {G D : Subgroup (MulAut W)}
    (hD : IsFFStarMin G D) {S : Subgroup W} (hS : commV D ≤ S)
    (hcard : Nat.card ↥(fixV D ⊓ S) ≤ 2 ^ 6) : HasGood G := by
  by_cases h4 : (fixV D).index ≤ 4
  · exact hasGood_of_isFFStarMin hW hD h4
  · push Not at h4
    have hidx : 8 ≤ (fixV D).index := by
      rw [B1.index_eq_two_pow hW] at h4 ⊢
      have : 2 < rkIdx (fixV D) := by
        by_contra hle
        push Not at hle
        have : 2 ^ rkIdx (fixV D) ≤ 2 ^ 2 := Nat.pow_le_pow_right (by norm_num) hle
        omega
      calc 8 = 2 ^ 3 := by norm_num
        _ ≤ 2 ^ rkIdx (fixV D) := Nat.pow_le_pow_right (by norm_num) this
    have hD8 : 8 ≤ Nat.card D := hidx.trans (index_fixV_le_card hD.1)
    refine hasGood_of_offender_le hW hD hS (hcard.trans ?_)
    calc 2 ^ 6 = 8 ^ 2 := by norm_num
      _ ≤ Nat.card D ^ 2 := Nat.pow_le_pow_left hD8 2

theorem exists_isFFStarMin {G : Subgroup (MulAut W)} (hne : G ≠ ⊥) (hJ : G = ffJ G) :
    ∃ D, IsFFStarMin G D := by
  obtain ⟨A, hA⟩ : ∃ A, IsFFStarOffender G A := by
    by_contra hno
    push Not at hno
    exact hne (hJ.trans (le_bot_iff.1 (iSup₂_le fun A hA => absurd hA (hno A))))
  obtain ⟨D, hD, -⟩ := B5.exists_isFFStarMin_ffLe hA
  exact ⟨D, hD⟩

end CFSG.Quasithin.B513N
