module

public import CFSG.LocalAnalysis.StandardType.GGKD2Leaf6D3Contracts
public import CFSG.LocalAnalysis.SeitzReduction.LinearPilotTPGraphFieldCore
public import CFSG.LocalAnalysis.SeitzReduction.UnitaryPilotBlocks
public import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10GInnLinFldGrp
public import CFSG.Assembly.LowTwoRank
public import CFSG.CharacterTheory.Wreathed.ProjectiveTwoParameterUniqueness
public import CFSG.CharacterTheory.Wreathed.BrauerWongTypes
public import CFSG.CharacterTheory.Wreathed.WreathCentralSquare
public import CFSG.LieType.SemisimpleCentralizers.HeldLangPSL
public import CFSG.LocalAnalysis.ComponentClassification.BurgoynePSLInner
public import CFSG.LocalAnalysis.ComponentClassification.BurgoyneProjSlice
public import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10FBase2
public import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10GField
public import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10GInnLinPieces
public import CFSG.LocalAnalysis.GLTheoremA.CatA.YS1011U64Types
public import CFSG.LocalAnalysis.GLTheoremA.S11.Inputs119
public import Certificates.Certificate8046
public import Certificates.Certificate8049
public import Certificates.Certificate8052

public section

namespace S2MathAs3_1624

open CFSG CFSG.Assembly CFSG.StandardType
open CFSG.ClassicalGroups.UnitaryFlag CFSG.Open

noncomputable section

private theorem ltrd3j8_factorization_504 : (504 : ℕ).factorization 2 = 3 := by
  rw [show (504 : ℕ) = 2 ^ 3 * 63 by norm_num]
  rw [Nat.factorization_mul (by norm_num) (by norm_num), Finsupp.add_apply,
    Nat.factorization_pow_self (p := 2) (n := 3) (by norm_num : Nat.Prime 2),
    Nat.factorization_eq_zero_of_not_dvd (p := 2) (n := 63)
      (by norm_num : ¬ 2 ∣ 63), add_zero]

private theorem ltrd3j8_arith {m n : ℕ} (hm : 2 ≤ m)
    (h : 3 * n * (m * (m - 1) / 2) = 3) : m = 2 ∧ n = 1 := by
  have hm1 : 1 ≤ m - 1 := by omega
  have hprod : 2 ≤ m * (m - 1) := by
    calc 2 = 2 * 1 := by norm_num
      _ ≤ m * (m - 1) := Nat.mul_le_mul hm hm1
  have hhalf1 : 1 ≤ m * (m - 1) / 2 := by omega
  have hnle : 3 * n ≤ 3 := by
    calc 3 * n = 3 * n * 1 := (Nat.mul_one _).symm
      _ ≤ 3 * n * (m * (m - 1) / 2) := Nat.mul_le_mul_left _ hhalf1
      _ = 3 := h
  have hn0 : n ≠ 0 := by
    rintro rfl
    norm_num at h
  have hn1 : n = 1 := by omega
  have hhalf_eq : m * (m - 1) / 2 = 1 := by
    rw [hn1] at h
    omega
  have hmle : m ≤ 2 := by
    by_contra hlt
    rw [Nat.not_le] at hlt
    have hm1' : 2 ≤ m - 1 := by omega
    have hprod6 : 6 ≤ m * (m - 1) := by
      calc 6 = 3 * 2 := by norm_num
        _ ≤ m * (m - 1) := Nat.mul_le_mul hlt hm1'
    have hhalf3 : 3 ≤ m * (m - 1) / 2 := by omega
    omega
  exact ⟨by omega, hn1⟩

theorem unitaryA1EightForcesSixOne_of_component (h : UnitaryComponentContractSimilitude) :
    UnitaryA1EightForcesSixOne := by
  intro K hKf hKfin hKcharP n hUF d hd S κ hκ hS hS3 hSnorm J hJcomp hJlabel
  obtain ⟨h3dvd, m, E, hEf, hEa, hEfin, hEUF, hm2, hd3m, hcubic, ⟨φ⟩⟩ :=
    (h K n hUF d hd S κ hκ hS hS3 hSnorm J) hJcomp
  letI : Field E := hEf
  letI : Algebra K E := hEa
  letI : Finite E := hEfin
  let Q := ↥(unitarySU 2 (3 * n) E m) ⧸
    Subgroup.center ↥(unitarySU 2 (3 * n) E m)
  have hlabel : LargeEvenRecipeLinear 2 8
      (fun R' _ _ _ => Nonempty (↥J ⧸ Subgroup.center ↥J ≃* R')) := hJlabel
  unfold LargeEvenRecipeLinear at hlabel
  obtain ⟨K₀, hK0f, hK0fin, hK0card, ⟨ψ⟩⟩ := hlabel
  letI : Field K₀ := hK0f
  letI : Finite K₀ := hK0fin
  have hcardQ : Nat.card Q = 504 := by
    have e1 : Q ≃* LargeEvenProj (LargeEvenSLGroup (Fin 2) K₀) := φ.symm.trans ψ
    have eL : Q ≃* CFSG.LieType.SemisimpleCentralizers.HeldLang.PSL (Fin 2) K₀ :=
      e1.trans (CFSG.LocalAnalysis.GLTheoremA.Y10GInnLinFld.pslEquivLarge (K := K₀) 2).symm
    have eSP : Q ≃* StatedProj (StatedSL 2 K₀) :=
      eL.trans (Classical.choice
        (CFSG.LocalAnalysis.GLTheoremA.Y10GInnLinFld.nonempty_psl_equiv_statedProj 2 K₀))
    have eM : Q ≃* Matrix.ProjectiveSpecialLinearGroup (Fin 2) K₀ :=
      eSP.trans (CFSG.Assembly.LowTwoRank.projectiveSpecialLinearGroupEquivStatedProj 2 K₀).symm
    rw [Nat.card_congr eM.toEquiv]
    rw [CFSG.Wreathed.ProjectiveTwoParameterUniqueness.card_projective_two_field K₀, hK0card]
    norm_num
  have hcardUSU := CFSG.SeitzReduction.LinearPilot.card_unitarySU_and_factorization
    (p := 2) (e := 3 * n) (K := E) (h := hEUF) (n := m) (by omega)
  have hfac := hcardUSU.2
  have hodd : Odd (Nat.card (Subgroup.center ↥(unitarySU 2 (3 * n) E m))) :=
    CFSG.SeitzReduction.UnitaryPilot.odd_card_center_unitarySU (h := hEUF) m
  have hcenter : (Nat.card (unitarySU 2 (3 * n) E m)).factorization 2 =
      (Nat.card Q).factorization 2 := by
    have hcardN : Nat.card (unitarySU 2 (3 * n) E m) =
        Nat.card Q * Nat.card (Subgroup.center ↥(unitarySU 2 (3 * n) E m)) :=
      Subgroup.card_eq_card_quotient_mul_card_subgroup
        (Subgroup.center ↥(unitarySU 2 (3 * n) E m))
    have hQnz : Nat.card Q ≠ 0 := by rw [hcardQ]; norm_num
    have hZnz : Nat.card (Subgroup.center ↥(unitarySU 2 (3 * n) E m)) ≠ 0 := by
      rintro h0
      exact (Nat.not_even_iff_odd.mpr hodd) (by simpa [h0] using Nat.even_zero)
    have hZfac : (Nat.card (Subgroup.center ↥(unitarySU 2 (3 * n) E m))).factorization 2 = 0 :=
      Nat.factorization_eq_zero_of_not_dvd
        (p := 2) (n := Nat.card (Subgroup.center ↥(unitarySU 2 (3 * n) E m))) (by
          intro hdvd
          exact (Nat.not_even_iff_odd.mpr hodd) (even_iff_two_dvd.mpr hdvd))
    rw [hcardN, Nat.factorization_mul hQnz hZnz, Finsupp.add_apply, hZfac, add_zero]
  have hNfac : (Nat.card (unitarySU 2 (3 * n) E m)).factorization 2 = 3 := by
    rw [hcenter, hcardQ]
    exact ltrd3j8_factorization_504
  have hexp : 3 * n * (m * (m - 1) / 2) = 3 := by
    have h2 : 2 ^ (3 * n * (m * (m - 1) / 2)) = 2 ^ 3 := by
      rw [pow_mul, ← hfac, hNfac]
    exact Nat.pow_right_injective (by norm_num : 1 < 2) h2
  obtain ⟨hm2', hn1⟩ := ltrd3j8_arith hm2 hexp
  subst hm2'
  exact ⟨by omega, hn1⟩

end

end S2MathAs3_1624

end
