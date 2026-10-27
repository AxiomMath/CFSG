module

public import CFSG.RankThree.PartTwo.Sec21.Item226Struct
import CFSG.LinearAlgebra.SL2MinimalFaithfulMatrix
import CFSG.LocalAnalysis.ProperTwoGeneratedCore.Lemma37.UnitaryOuterSmall

public section

namespace CFSG.RankThree.PartTwo.Sec21

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo Matrix
open CFSG.Assembly.RankThreeEven (projSL projSU)

theorem natCard_galoisField_two_zero : Nat.card (GaloisField 2 0) = 2 :=
  CFSG.ProperTwoGeneratedCore.Lemma37.UnitaryOuter.card_galoisField_two_zero

theorem card_projSL_two_galoisField_zero : Nat.card (projSL 2 (GaloisField 2 0)) = 6 := by
  rw [Nat.card_congr (projSLTwoEquivSL (GaloisField 2 0)).toEquiv,
    CFSG.SL2MinimalFaithful.card_specialLinearGroup_fin_two, natCard_galoisField_two_zero]
  norm_num

theorem card_projSU_four_zero_dvd : Nat.card (projSU 4 2 0) ∣ 20160 := by
  classical
  let F := GaloisField 2 (2 * 0)
  have hF : Nat.card F = 2 := natCard_galoisField_two_zero
  let := Fintype.ofFinite F
  have hGL : Nat.card (GL (Fin 4) F) = 20160 := by
    rw [Matrix.card_GL_field, Fin.prod_univ_four, Fintype.card_eq_nat_card, hF]
    norm_num
  have hindex : (Subgroup.center (GL (Fin 4) F)).index = Nat.card (ProjGenLinGroup (Fin 4) F) :=
    rfl
  calc Nat.card (projSU 4 2 0) ∣ Nat.card (ProjGenLinGroup (Fin 4) F) :=
        Subgroup.card_subgroup_dvd_card _
    _ ∣ Nat.card (GL (Fin 4) F) := hindex ▸ (Subgroup.center (GL (Fin 4) F)).index_dvd_card
    _ = 20160 := hGL

theorem eq_of_mulEquiv_projSL_two_of_one_lt {a b : ℕ} (hb : 1 < b)
    (e : projSL 2 (GaloisField 2 a) ≃* projSL 2 (GaloisField 2 b)) : a = b := by
  rcases Nat.eq_zero_or_pos a with rfl | ha
  · exfalso
    have h := Nat.card_congr e.toEquiv
    rw [card_projSL_two_galoisField_zero, card_projSL_two b (by omega)] at h
    have h4 : 2 ^ 2 ∣ 2 ^ b * ((2 ^ b) ^ 2 - 1) := (pow_dvd_pow 2 (by omega)).mul_right _
    rw [← h] at h4
    norm_num at h4
  · exact eq_of_mulEquiv_projSL_two ha (by omega) e

theorem eq_of_mulEquiv_projSU_four_of_one_lt {a b : ℕ} (hb : 1 < b)
    (e : projSU 4 2 a ≃* projSU 4 2 b) : a = b := by
  rcases Nat.eq_zero_or_pos a with rfl | ha
  · exfalso
    have hd := card_projSU_four_zero_dvd
    rw [Nat.card_congr e.toEquiv, card_projSU le_rfl (by omega), ordTwistedA_three_eq (by omega)]
      at hd
    have h6 : 2 ^ 12 ∣ (2 ^ b) ^ 6 := by
      rw [← pow_mul]
      exact pow_dvd_pow 2 (by omega)
    have h := (h6.mul_right _).trans hd
    norm_num at h
  · exact eq_of_mulEquiv_projSU_four ha (by omega) e

theorem item223_of_print (h2115 : Item2115) (h222 : Item222)
    (hKW : KOfWellDefinedAll) (hP : Item223Print) : Item223 := by
  intro G _ _ A E U c L hpair hA81 n ⟨eLn⟩ φ hφ ψ hψ
  have hK := hKW G A E U c L hpair
  have hS3 := s3_of_item223Print hP hpair hA81
  have htr := transitive_dStar_of_s3 h2115 h222 hpair hA81 hS3
    (fun _ hd hdL => centralReflection_of_s3 h222 hpair hA81 hS3 hd hdL)
  obtain ⟨φ₀, -, hφ₀D, n₀, hn₀, -, ⟨eL₀⟩, ⟨eK₀⟩, -⟩ := exists_case_five h222 hpair hA81
  obtain rfl : n = n₀ := eq_of_mulEquiv_projSU_four_of_one_lt hn₀ (eLn.symm.trans eL₀)
  obtain ⟨g, hg, hgφ⟩ := htr φ₀ hφ₀D φ hφ
  obtain ⟨eφ⟩ := nonempty_kOf_mulEquiv_of_conj hK hφ₀D (closure_dStar_le_wStar A hg) hgφ
  have eK := eφ.trans eK₀
  obtain ⟨h1, h2, h3⟩ := hP G A E U c L hpair hA81 φ hφ ψ hψ
  refine ⟨fun X hX hKX => ?_, h2, fun hne => ?_⟩
  · obtain ⟨m, hm, -, ⟨eX⟩, ⟨eKm⟩⟩ := h1 X hX hKX
    obtain rfl : m = n := eq_of_mulEquiv_projSL_two (by omega) (by omega) (eKm.symm.trans eK)
    exact ⟨eX⟩
  · obtain ⟨⟨m, ⟨eKm⟩, ⟨eY⟩⟩, hS⟩ := h3 hne
    obtain rfl : m = n := eq_of_mulEquiv_projSL_two_of_one_lt hn₀ (eKm.symm.trans eK)
    exact ⟨⟨eY⟩, hS⟩

end CFSG.RankThree.PartTwo.Sec21
