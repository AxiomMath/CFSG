module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section17.SeventeenTen
public import CFSG.RankThree.PartOne.CTP.SporadicOrders
public import CFSG.LocalAnalysis.EvenSporadicStandard.HSStd.Zassenhaus.ONan.CenterFree
public import CFSG.GH74.GLS.Stage2.Signalizer.Odd87GrpE4Par

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8

open CFSG.Open CFSG.LocalAnalysis.UniquenessCase.UC22
open CFSG.LocalAnalysis.UniquenessCase.UC22.F08
open CFSG.Blueprint (LieModel)

variable {X : Type} [Group X] [Finite X]

theorem not_three_dvd_center_of_isSpor_M11
    (h : IsSpor X .M11) : ¬ 3 ∣ Nat.card (Subgroup.center X) := by
  obtain ⟨e⟩ := h
  haveI : IsSimpleGroup CFSG.Blueprint.NativeSporadic.M11 :=
    CFSG.Sporadic.Mathieu.fam_m11_simplicity.2.2
  have hcard : ¬ (Nat.card CFSG.Blueprint.NativeSporadic.M11).Prime := by
    rw [CFSG.Sporadic.Mathieu.card_M11]
    norm_num
  have hZ : Subgroup.center (CFSG.Blueprint.NativeSporadic.Carrier .M11) = ⊥ := by
    change Subgroup.center CFSG.Blueprint.NativeSporadic.M11 = ⊥
    exact CFSG.EvenSporadicStandard.HSStd.Zassenhaus.ONan.center_eq_bot_of_isSimpleGroup_of_not_prime_card
      hcard
  have hX : Subgroup.center X = ⊥ := CFSG.ABGLocalTools.center_eq_bot_of_mulEquiv e hZ
  rw [hX, Subgroup.card_bot]
  norm_num

theorem not_three_dvd_center_of_isSpor_M12
    (h : IsSpor X .M12) : ¬ 3 ∣ Nat.card (Subgroup.center X) := by
  obtain ⟨e⟩ := h
  haveI : IsSimpleGroup CFSG.Blueprint.NativeSporadic.M12 :=
    CFSG.Sporadic.Mathieu.fam_m12_simplicity.2.2
  have hcard : ¬ (Nat.card CFSG.Blueprint.NativeSporadic.M12).Prime := by
    rw [CFSG.Sporadic.Mathieu.card_M12]
    norm_num
  have hZ : Subgroup.center (CFSG.Blueprint.NativeSporadic.Carrier .M12) = ⊥ := by
    change Subgroup.center CFSG.Blueprint.NativeSporadic.M12 = ⊥
    exact CFSG.EvenSporadicStandard.HSStd.Zassenhaus.ONan.center_eq_bot_of_isSimpleGroup_of_not_prime_card
      hcard
  have hX : Subgroup.center X = ⊥ := CFSG.ABGLocalTools.center_eq_bot_of_mulEquiv e hZ
  rw [hX, Subgroup.card_bot]
  norm_num

theorem not_three_dvd_center_of_isSpor_M22
    (h : IsSpor X .M22) : ¬ 3 ∣ Nat.card (Subgroup.center X) := by
  obtain ⟨e⟩ := h
  haveI : IsSimpleGroup CFSG.Blueprint.NativeSporadic.M22 :=
    CFSG.Sporadic.Mathieu.fam_m22_simplicity.2.2
  have hcard : ¬ (Nat.card CFSG.Blueprint.NativeSporadic.M22).Prime := by
    rw [CFSG.Sporadic.Mathieu.card_M22]
    norm_num
  have hZ : Subgroup.center (CFSG.Blueprint.NativeSporadic.Carrier .M22) = ⊥ := by
    change Subgroup.center CFSG.Blueprint.NativeSporadic.M22 = ⊥
    exact CFSG.EvenSporadicStandard.HSStd.Zassenhaus.ONan.center_eq_bot_of_isSimpleGroup_of_not_prime_card
      hcard
  have hX : Subgroup.center X = ⊥ := CFSG.ABGLocalTools.center_eq_bot_of_mulEquiv e hZ
  rw [hX, Subgroup.card_bot]
  norm_num

theorem not_three_dvd_center_of_isSpor_M23
    (h : IsSpor X .M23) : ¬ 3 ∣ Nat.card (Subgroup.center X) := by
  obtain ⟨e⟩ := h
  haveI : IsSimpleGroup CFSG.Blueprint.NativeSporadic.M23 :=
    CFSG.Sporadic.Mathieu.fam_m23_simplicity.2.2
  have hcard : ¬ (Nat.card CFSG.Blueprint.NativeSporadic.M23).Prime := by
    rw [CFSG.RankThree.PartOne.CTP.card_M23]
    norm_num
  have hZ : Subgroup.center (CFSG.Blueprint.NativeSporadic.Carrier .M23) = ⊥ := by
    change Subgroup.center CFSG.Blueprint.NativeSporadic.M23 = ⊥
    exact CFSG.EvenSporadicStandard.HSStd.Zassenhaus.ONan.center_eq_bot_of_isSimpleGroup_of_not_prime_card
      hcard
  have hX : Subgroup.center X = ⊥ := CFSG.ABGLocalTools.center_eq_bot_of_mulEquiv e hZ
  rw [hX, Subgroup.card_bot]
  norm_num

theorem not_three_dvd_center_of_isSpor_M24
    (h : IsSpor X .M24) : ¬ 3 ∣ Nat.card (Subgroup.center X) := by
  obtain ⟨e⟩ := h
  haveI : IsSimpleGroup CFSG.Blueprint.NativeSporadic.M24 :=
    CFSG.Sporadic.Mathieu.fam_m24_simplicity.2.2
  have hcard : ¬ (Nat.card CFSG.Blueprint.NativeSporadic.M24).Prime := by
    rw [CFSG.Sporadic.Mathieu.card_M24]
    norm_num
  have hZ : Subgroup.center (CFSG.Blueprint.NativeSporadic.Carrier .M24) = ⊥ := by
    change Subgroup.center CFSG.Blueprint.NativeSporadic.M24 = ⊥
    exact CFSG.EvenSporadicStandard.HSStd.Zassenhaus.ONan.center_eq_bot_of_isSimpleGroup_of_not_prime_card
      hcard
  have hX : Subgroup.center X = ⊥ := CFSG.ABGLocalTools.center_eq_bot_of_mulEquiv e hZ
  rw [hX, Subgroup.card_bot]
  norm_num

theorem not_three_dvd_center_of_isMathieu
    (h : IsMathieu X) : ¬ 3 ∣ Nat.card (Subgroup.center X) := by
  rcases h with h | h | h | h | h
  · exact not_three_dvd_center_of_isSpor_M11 h
  · exact not_three_dvd_center_of_isSpor_M12 h
  · exact not_three_dvd_center_of_isSpor_M22 h
  · exact not_three_dvd_center_of_isSpor_M23 h
  · exact not_three_dvd_center_of_isSpor_M24 h

theorem not_three_dvd_center_of_isSpor_J2
    (h : IsSpor X .J2) : ¬ 3 ∣ Nat.card (Subgroup.center X) := by
  obtain ⟨e⟩ := h
  haveI : IsSimpleGroup CFSG.Blueprint.NativeSporadic.J2 := CFSG.Sporadic.J2.isSimpleGroup_J2
  have hcard : ¬ (Nat.card CFSG.Blueprint.NativeSporadic.J2).Prime := by
    rw [CFSG.Sporadic.J2.card_J2]
    norm_num
  have hZ : Subgroup.center (CFSG.Blueprint.NativeSporadic.Carrier .J2) = ⊥ := by
    change Subgroup.center CFSG.Blueprint.NativeSporadic.J2 = ⊥
    exact CFSG.EvenSporadicStandard.HSStd.Zassenhaus.ONan.center_eq_bot_of_isSimpleGroup_of_not_prime_card
      hcard
  have hX : Subgroup.center X = ⊥ := CFSG.ABGLocalTools.center_eq_bot_of_mulEquiv e hZ
  rw [hX, Subgroup.card_bot]
  norm_num

theorem not_three_dvd_center_of_isSpor_HS
    (h : IsSpor X .HS) : ¬ 3 ∣ Nat.card (Subgroup.center X) := by
  obtain ⟨e⟩ := h
  haveI : IsSimpleGroup CFSG.Blueprint.NativeSporadic.HS := CFSG.Sporadic.HS.isSimpleGroup_HS
  have hcard : ¬ (Nat.card CFSG.Blueprint.NativeSporadic.HS).Prime := by
    rw [CFSG.Sporadic.HS.card_HS]
    norm_num
  have hZ : Subgroup.center (CFSG.Blueprint.NativeSporadic.Carrier .HS) = ⊥ := by
    change Subgroup.center CFSG.Blueprint.NativeSporadic.HS = ⊥
    exact CFSG.EvenSporadicStandard.HSStd.Zassenhaus.ONan.center_eq_bot_of_isSimpleGroup_of_not_prime_card
      hcard
  have hX : Subgroup.center X = ⊥ := CFSG.ABGLocalTools.center_eq_bot_of_mulEquiv e hZ
  rw [hX, Subgroup.card_bot]
  norm_num

theorem not_three_dvd_center_of_isSpor_Ru
    (h : IsSpor X .Ru) : ¬ 3 ∣ Nat.card (Subgroup.center X) := by
  obtain ⟨e⟩ := h
  haveI : IsSimpleGroup CFSG.Blueprint.NativeSporadic.Ru := CFSG.Sporadic.Ru.isSimpleGroup_Ru
  have hcard : ¬ (Nat.card CFSG.Blueprint.NativeSporadic.Ru).Prime := by
    rw [CFSG.Sporadic.Ru.card_Ru]
    norm_num
  have hZ : Subgroup.center (CFSG.Blueprint.NativeSporadic.Carrier .Ru) = ⊥ := by
    change Subgroup.center CFSG.Blueprint.NativeSporadic.Ru = ⊥
    exact CFSG.EvenSporadicStandard.HSStd.Zassenhaus.ONan.center_eq_bot_of_isSimpleGroup_of_not_prime_card
      hcard
  have hX : Subgroup.center X = ⊥ := CFSG.ABGLocalTools.center_eq_bot_of_mulEquiv e hZ
  rw [hX, Subgroup.card_bot]
  norm_num

theorem not_three_dvd_center_of_isSpor_J4
    (h : IsSpor X .J4) : ¬ 3 ∣ Nat.card (Subgroup.center X) := by
  obtain ⟨e⟩ := h
  haveI : IsSimpleGroup CFSG.Blueprint.NativeSporadic.J4 := CFSG.Sporadic.J4.isSimpleGroup_J4
  have hcard : ¬ (Nat.card CFSG.Blueprint.NativeSporadic.J4).Prime := by
    rw [CFSG.Sporadic.J4.card_J4]
    norm_num
  have hZ : Subgroup.center (CFSG.Blueprint.NativeSporadic.Carrier .J4) = ⊥ := by
    change Subgroup.center CFSG.Blueprint.NativeSporadic.J4 = ⊥
    exact CFSG.EvenSporadicStandard.HSStd.Zassenhaus.ONan.center_eq_bot_of_isSimpleGroup_of_not_prime_card
      hcard
  have hX : Subgroup.center X = ⊥ := CFSG.ABGLocalTools.center_eq_bot_of_mulEquiv e hZ
  rw [hX, Subgroup.card_bot]
  norm_num

theorem not_three_dvd_center_of_isAlt {n : ℕ} (hn : 6 ≤ n) (h : IsAlt X n) :
    ¬ 3 ∣ Nat.card (Subgroup.center X) := by
  obtain ⟨e⟩ := h
  have hZ : Subgroup.center (alternatingGroup (Fin n)) = ⊥ :=
    alternatingGroup.center_eq_bot (by simpa using (show 4 ≤ n by omega))
  have hX : Subgroup.center X = ⊥ := CFSG.ABGLocalTools.center_eq_bot_of_mulEquiv e hZ
  rw [hX, Subgroup.card_bot]
  norm_num

theorem not_three_dvd_center_of_lieModel_PSL_five_two
    (h : LieModel X .PSL 5 2 1) : ¬ 3 ∣ Nat.card (Subgroup.center X) := by
  have hZ := CFSG.EvenSporadicStandard.HSStd.Zassenhaus.ONan.center_eq_bot_of_lieModel_psl_five_two h
  rw [hZ, Subgroup.card_bot]
  norm_num

theorem not_three_dvd_center_of_lieModel_PSL_three_three_one
    (h : LieModel X .PSL 3 3 1) : ¬ 3 ∣ Nat.card (Subgroup.center X) := by
  have hZ := CFSG.GH74.GLS.Stage2.Signalizer.Odd87.CentralQuotient.center_eq_bot_of_lieModel_psl3 h
  rw [hZ, Subgroup.card_bot]
  norm_num

theorem not_three_dvd_center_of_isSp4 {n : ℕ} (h : IsSp4 X n) :
    ¬ 3 ∣ Nat.card (Subgroup.center X) := by
  have hn1 : 1 ≤ n := h.admissible.2.1
  have hnot : ¬ (CFSG.EvenSmallLie.CatalogOrders.lieOrd .PSp 2 (2 ^ n)).Prime := by
    intro hp
    have h4n : 2 ≤ 4 * n := by omega
    have hdvd : 2 ^ (4 * n) ∣ CFSG.EvenSmallLie.CatalogOrders.lieOrd .PSp 2 (2 ^ n) := by
      have h := CFSG.EvenSmallLie.CatalogOrders.pow_lieExp_dvd (t := .PSp) (n := 2)
        (by decide) (2 ^ n)
      have h4 : CFSG.EvenSmallLie.CatalogOrders.lieExp .PSp 2 = 4 := by decide
      rw [h4] at h
      have he : (2 ^ n) ^ 4 = 2 ^ (4 * n) := by
        have h1 : (2 ^ n) ^ 4 = 2 ^ (n * 4) := (pow_mul 2 n 4).symm
        rw [h1, show n * 4 = 4 * n by ring]
      rw [he] at h
      exact h
    have hlt : 2 ^ (4 * n) ≠ 1 := by
      have h2 : 2 ≤ 2 ^ (4 * n) := by
        calc 2 = 2 ^ 1 := (pow_one 2).symm
          _ ≤ 2 ^ (4 * n) := Nat.pow_le_pow_right (by norm_num) (by omega)
      omega
    have hnp : ¬ (2 ^ (4 * n)).Prime :=
      Nat.Prime.not_prime_pow (x := 2) (n := 4 * n) h4n
    obtain hEq : CFSG.EvenSmallLie.CatalogOrders.lieOrd .PSp 2 (2 ^ n) = 2 ^ (4 * n) :=
      (hp.dvd_iff_eq hlt).mp hdvd
    exact hnp (hEq ▸ hp)
  have hZ := CFSG.EvenSporadicStandard.HSStd.Zassenhaus.ONan.center_eq_bot_of_lieModel
    (t := .PSp) (n := 2) (p := 2) (f := n) (by decide) (by norm_num) h hnot
  rw [hZ, Subgroup.card_bot]
  norm_num

theorem not_three_dvd_center_of_isG2Der
    {n : ℕ} (h : IsG2Der X n) : ¬ 3 ∣ Nat.card (Subgroup.center X) := by
  rcases h with ⟨rfl, h⟩ | ⟨-, h⟩
  · have hnot : ¬ (CFSG.EvenSmallLie.CatalogOrders.lieOrd .PSU 3 (3 ^ 1)).Prime := by
      intro hp
      have hdvd : 27 ∣ CFSG.EvenSmallLie.CatalogOrders.lieOrd .PSU 3 (3 ^ 1) := by
        have h := CFSG.EvenSmallLie.CatalogOrders.pow_lieExp_dvd (t := .PSU) (n := 3)
          (by decide) (3 ^ 1)
        have he : CFSG.EvenSmallLie.CatalogOrders.lieExp .PSU 3 = 3 := by decide
        rw [he] at h
        simpa using h
      rcases hp.eq_one_or_self_of_dvd 27 hdvd with h1 | h27
      · norm_num at h1
      · exact absurd (h27.symm ▸ hp) (by norm_num)
    have hZ := CFSG.EvenSporadicStandard.HSStd.Zassenhaus.ONan.center_eq_bot_of_lieModel
      (t := .PSU) (n := 3) (p := 3) (f := 1) (by decide) (by norm_num) h hnot
    rw [hZ, Subgroup.card_bot]
    norm_num
  · have hZ := CFSG.LocalAnalysis.UniquenessCase.PartTwo.S17.center_eq_bot_of_lieModel_g2 h
    rw [hZ, Subgroup.card_bot]
    norm_num

theorem not_three_dvd_center_of_isSU5 (hGA : CFSG.Open.GriessAllModelsStatement) {m : ℕ}
    (h : IsSU5 X m) : ¬ 3 ∣ Nat.card (Subgroup.center X) := by
  obtain ⟨hq, hU⟩ := h
  have hmod : CFSG.Open.StatedClassicalModel (X ⧸ Subgroup.center X) .PSU 5 2 m :=
    LieModel.statedClassicalModel hU (by decide)
  have hdvd := CFSG.RankThree.PartOne.card_center_dvd_of_model hGA hq hmod
  have hgen : CFSG.Blueprint.Multiplier.genericOrders .PSU 5 2 m =
      (Nat.gcd 5 (2 ^ m + 1), 1) := rfl
  have hexc : CFSG.Blueprint.Multiplier.exceptionalOrders .PSU 5 2 m = (1, 1) := by
    unfold CFSG.Blueprint.Multiplier.exceptionalOrders
    simp
  rw [hgen, hexc] at hdvd
  have hdvd' : Nat.card (Subgroup.center X) ∣ Nat.gcd 5 (2 ^ m + 1) := by
    simpa using hdvd
  intro h3
  exact absurd (h3.trans (hdvd'.trans (Nat.gcd_dvd_left 5 (2 ^ m + 1)))) (by norm_num)

theorem not_three_dvd_center_of_isSU5Four (h : IsSU5Four X) :
    ¬ 3 ∣ Nat.card (Subgroup.center X) := by
  rw [h.2]
  norm_num

theorem list880_center_three_imp
    (h : CFSG.LocalAnalysis.UniquenessCase.UC22.F08.List880 X)
    (hZ : 3 ∣ Nat.card (Subgroup.center X)) :
    CFSG.LocalAnalysis.UniquenessCase.UC22.F08.IsA6Z3 X ∨
    CFSG.LocalAnalysis.UniquenessCase.UC22.F08.IsA7Z3 X ∨
    CFSG.LocalAnalysis.UniquenessCase.UC22.F08.IsM22Z3 X := by
  have hGA : CFSG.Open.GriessAllModelsStatement :=
    CFSG.Milestones.cl_lit_griess_schur_multipliers_all_models_statement
  unfold List880 at h
  rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
  · exact absurd hZ (not_three_dvd_center_of_isMathieu h)
  · exact absurd hZ (not_three_dvd_center_of_isSpor_J2 h)
  · exact absurd hZ (not_three_dvd_center_of_isSpor_HS h)
  · exact absurd hZ (not_three_dvd_center_of_isSpor_Ru h)
  · exact absurd hZ (not_three_dvd_center_of_isSpor_J4 h)
  · exact Or.inl h
  · exact Or.inr (Or.inl h)
  · exact Or.inr (Or.inr h)
  · exact absurd hZ (not_three_dvd_center_of_isAlt (by norm_num) h)
  · exact absurd hZ (not_three_dvd_center_of_isAlt (by norm_num) h)
  · exact absurd hZ (not_three_dvd_center_of_isAlt (by norm_num) h)
  · exact absurd hZ (not_three_dvd_center_of_lieModel_PSL_five_two h)
  · exact absurd hZ (not_three_dvd_center_of_lieModel_PSL_three_three_one h)
  · obtain ⟨n, hn⟩ := h
    exact absurd hZ (not_three_dvd_center_of_isSp4 hn)
  · obtain ⟨n, hn⟩ := h
    exact absurd hZ (not_three_dvd_center_of_isG2Der hn)
  · obtain ⟨m, -, hm⟩ := h
    exact absurd hZ (not_three_dvd_center_of_isSU5 hGA hm)
  · exact absurd hZ (not_three_dvd_center_of_isSU5Four h)

end CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8
