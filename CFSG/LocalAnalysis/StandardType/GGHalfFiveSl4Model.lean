module

public import CFSG.LocalAnalysis.StandardType.GGSecFiveRest

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.Assembly.LowTwoRank

private theorem center_sl4_galoisField_eq_bot :
    Subgroup.center (Matrix.SpecialLinearGroup (Fin 4) (GaloisField 2 2)) = ⊥ := by
  haveI := Fintype.ofFinite (GaloisField 2 2)
  rw [Subgroup.eq_bot_iff_forall]
  intro A hA
  obtain ⟨r, hr, hrA⟩ := Matrix.SpecialLinearGroup.mem_center_iff.1 hA
  rw [Fintype.card_fin] at hr
  have hr0 : r ≠ 0 := by
    rintro rfl
    rw [zero_pow (show (4 : ℕ) ≠ 0 by norm_num)] at hr
    exact zero_ne_one hr
  have h3 : r ^ 3 = 1 := by
    have h := FiniteField.pow_card_sub_one_eq_one r hr0
    rw [Fintype.card_eq_nat_card, GaloisField.card 2 2 (by norm_num),
      show (2 : ℕ) ^ 2 - 1 = 3 by norm_num] at h
    exact h
  have hr1 : r = 1 := by
    have h4 : r ^ 4 = r := by
      rw [show (4 : ℕ) = 3 + 1 by norm_num, pow_add, h3, one_mul, pow_one]
    rw [h4] at hr
    exact hr
  apply Subtype.ext
  rw [← hrA, hr1]
  ext i j
  simp [Matrix.scalar_apply]

theorem equiv_sl4_of_statedModel {Y : Type} [Group Y]
    (h : StatedClassicalModel Y .PSL 4 2 2) :
    Nonempty (Y ≃* Matrix.SpecialLinearGroup (Fin 4) (GaloisField 2 2)) := by
  obtain ⟨-, K, hK, hKfin, hKcard, ⟨e⟩⟩ := h
  letI : Field K := hK
  letI : Finite K := hKfin
  refine ⟨e.trans ((CFSG.ClassicalModels.statedLinearModelEquivGaloisPSL K 4 2 2
    (by norm_num) hKcard).trans ?_)⟩
  exact (QuotientGroup.quotientMulEquivOfEq center_sl4_galoisField_eq_bot).trans
    QuotientGroup.quotientBot

theorem statedModel_of_equiv_sl3 {Y : Type} [Group Y]
    (e : Y ≃* Matrix.SpecialLinearGroup (Fin 3) (GaloisField 2 2)) :
    StatedClassicalModel (Y ⧸ Subgroup.center Y) .PSL 3 2 2 := by
  refine ⟨?_, GaloisField 2 2, inferInstance, inferInstance, ?_, ⟨?_⟩⟩
  · unfold StatedLieAdmissible
    exact ⟨Nat.prime_two, by norm_num, by norm_num, by norm_num, by norm_num⟩
  · exact GaloisField.card 2 2 (by norm_num)
  · exact (QuotientGroup.congr (Subgroup.center Y)
      (Subgroup.center (Matrix.SpecialLinearGroup (Fin 3) (GaloisField 2 2))) e
      (Subgroup.map_center_eq e)).trans
      (CFSG.Assembly.LowTwoRank.projectiveSpecialLinearGroupEquivStatedProj 3 (GaloisField 2 2))

end CFSG.StandardType

end
