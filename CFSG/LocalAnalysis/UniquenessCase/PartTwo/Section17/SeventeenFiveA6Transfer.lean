module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section17.SeventeenFiveA6Defs
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.AltLocal17A6
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section17.ComponentOrbitThree
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section17.ImageOTwoQuotNormalizer
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section17.SeventeenTwentyOne
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section17.SeventeenFiveA6
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.ComponentCalV1

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.S17

open Subgroup CFSG.Open CFSG.Quasithin CFSG.GroupTheory
open CFSG.LocalAnalysis.UniquenessCase.UC22
open CFSG.LocalAnalysis.UniquenessCase.PartTwo
open scoped Pointwise commutatorElement

variable {G : Type} [Group G] [Finite G]

theorem S1Nine_pow_four_mem_centralizer {D : Data G} {L : Subgroup G}
    (hL : L ∈ calC D.M) (hexp : ExpFourAut17 D L) :
    ∀ s ∈ S1Nine D L, s ^ 4 ∈ Subgroup.centralizer (K1Nine D L : Set (Mbar9 D)) := by
  intro s hs
  have hs' : s ∈ CFSG.Quasithin.imageOTwoQuot D.M (NTL17 D L) := by
    rw [NTL17, imageOTwoQuot_inf_normalizer (D := D) (L := L) hL]
    exact hs
  obtain ⟨t, htM, htN, hts⟩ := CFSG.Quasithin.mem_imageOTwoQuot_iff.mp hs'
  rw [← hts, Subgroup.mem_centralizer_iff]
  intro k hk
  obtain ⟨l, hlM, hlL, hkl⟩ := CFSG.Quasithin.mem_imageOTwoQuot_iff.mp hk
  rw [← hkl]
  let π : ↥D.M →* Mbar9 D := QuotientGroup.mk' (CFSG.Open.pCore 2 ↥D.M)
  let tM : ↥D.M := ⟨t, htM⟩
  let lM : ↥D.M := ⟨l, hlM⟩
  have hπt : π tM = (QuotientGroup.mk ⟨t, htM⟩ : Mbar9 D) :=
    QuotientGroup.mk'_apply (CFSG.Open.pCore 2 ↥D.M) tM
  have hπl : π lM = (QuotientGroup.mk ⟨l, hlM⟩ : Mbar9 D) :=
    QuotientGroup.mk'_apply (CFSG.Open.pCore 2 ↥D.M) lM
  rw [← hπt, ← hπl]
  have hmemL : t ^ 4 * l * (t ^ 4)⁻¹ * l⁻¹ ∈ CFSG.Open.pCoreOf 2 L :=
    (hexp t htN).2.2.2 l hlL
  have hmemM : t ^ 4 * l * (t ^ 4)⁻¹ * l⁻¹ ∈ CFSG.Open.pCoreOf 2 D.M :=
    CFSG.Quasithin.A4.pCoreOf_le_of_subnormal 2 hL.1 hmemL
  have hinv : π lM * (π tM) ^ 4 * (π lM)⁻¹ * ((π tM) ^ 4)⁻¹ = 1 := by
    have h1 : π (lM * tM ^ 4 * lM⁻¹ * (tM ^ 4)⁻¹) = 1 := by
      rw [QuotientGroup.mk'_apply]
      rw [CFSG.Quasithin.mk_eq_one_iff_mem_pCoreOf (M := D.M)
        (x := lM * tM ^ 4 * lM⁻¹ * (tM ^ 4)⁻¹)]
      have hinvM : (t ^ 4 * l * (t ^ 4)⁻¹ * l⁻¹)⁻¹ ∈ CFSG.Open.pCoreOf 2 D.M :=
        (CFSG.Open.pCoreOf 2 D.M).inv_mem hmemM
      show l * t ^ 4 * l⁻¹ * (t ^ 4)⁻¹ ∈ CFSG.Open.pCoreOf 2 D.M
      have hEq : l * t ^ 4 * l⁻¹ * (t ^ 4)⁻¹ =
          (t ^ 4 * l * (t ^ 4)⁻¹ * l⁻¹)⁻¹ := by group
      rw [hEq]
      exact hinvM
    simpa only [map_mul, map_pow, map_inv] using h1
  have hcomm : (π tM) ^ 4 * π lM = π lM * (π tM) ^ 4 := by
    have h3 : π lM * (π tM) ^ 4 * (π lM)⁻¹ = (π tM) ^ 4 := mul_inv_eq_one.mp hinv
    calc (π tM) ^ 4 * π lM
        = (π lM * (π tM) ^ 4 * (π lM)⁻¹) * π lM := by rw [h3]
      _ = π lM * (π tM) ^ 4 := by group
  exact hcomm.symm

theorem le_normalizer_of_noncentral_three_exp4 {D : Data G} {V₀ V : Subgroup G}
    {hV : Hyp125 D V₀ V}
    (h17_1 : R17_1At D V₀ V hV) (hk : D.k = 1) {L : Subgroup G} (hL : L ∈ calC D.M)
    (hshape : Nonempty (BarO2Z17 L ≃* alternatingGroup (Fin 6)))
    (hexp : ExpFourAut17 D L)
    (hKnc : Inputs1719.K_A6Exp4Noncentral) :
    D.T ≤ Subgroup.normalizer (L : Set G) :=
  le_normalizer_of_noncentral_three_of_pow h17_1 hk hL (n := 4)
    (S1Nine_pow_four_mem_centralizer hL hexp)
    (fun Y _ _ K S hKY hKe hexpS => by
      obtain ⟨e⟩ := hKe
      obtain ⟨e1⟩ := centerQuot_of_barO2Z hL hshape
      exact hKnc Y K S hKY
        ⟨(QuotientGroup.congr _ _ e (Subgroup.map_center_eq e)).trans e1⟩ hexpS)

theorem exists_s3_pair_of_calC_exp4 {D : Data G} {L : Subgroup G} (hL : L ∈ calC D.M)
    (hnorm : Tbar9 D ≤ Subgroup.normalizer (K1Nine D L : Set (Mbar9 D)))
    (hshape : Nonempty (BarO2Z17 L ≃* alternatingGroup (Fin 6)))
    (hexp : ExpFourAut17 D L) (hKpair : Inputs1719.K_A6Exp4SThreePair) :
    ∃ L₁ L₂ : Subgroup G, D.T ≤ L₁ ∧ D.T ≤ L₂ ∧ L ⊔ D.T = L₁ ⊔ L₂ ∧
      Nonempty (Bar2 L₁ ≃* Equiv.Perm (Fin 3)) ∧
      Nonempty (Bar2 L₂ ≃* Equiv.Perm (Fin 3)) :=
  exists_s3_pair_of_calC_bar2_of_pow hL hnorm (n := 4)
    (S1Nine_pow_four_mem_centralizer hL hexp)
    (fun Y _ _ K S hKY hKe hexpS => by
      obtain ⟨e⟩ := hKe
      obtain ⟨e1⟩ := centerQuot_of_barO2Z hL hshape
      exact hKpair Y K S hKY
        ⟨(QuotientGroup.congr _ _ e (Subgroup.map_center_eq e)).trans e1⟩ hexpS)

theorem false_of_expFour {D : Data G} {V₀ V : Subgroup G} (hV : Hyp125 D V₀ V)
    (h17_1 : R17_1At D V₀ V hV) (h17_4 : R17_4AtA D V₀ V hV)
    (h869 : F08.R869 D) (h127 : R127 D) (hC117 : C117 D V₀ V) (h106 : Inputs1719.W4Lem10_6Q)
    (hKpair : Inputs1719.K_A6Exp4SThreePair)
    (hk : D.k = 1) {L : Subgroup G} (hL : L ∈ calC D.M)
    (hshape : Nonempty (BarO2Z17 L ≃* alternatingGroup (Fin 6)))
    (hexp : ExpFourAut17 D L) : False := by
  have hTL : D.T ≤ Subgroup.normalizer (L : Set G) :=
    le_normalizer_of_noncentral_three_exp4 (hV := hV) h17_1 hk hL hshape hexp
      (Inputs1719.k_A6Exp4Noncentral_of_sThreePair hKpair)
  have hnt : ¬ F08.Thin8 L := not_thin8_of_barO2Z_altSix hshape
  have hN : calNOf L = {D.M} :=
    h869 L (Or.inl hL) L le_rfl
      (sup_eq_left.mpr (CFSG.LieType.BorelTits.pCoreOf_le 2 L)) hnt
  have hU : UniqueMax D.M L := UC22.uc22p22u_uniqueMax_of_calN D hL.1.le hN
  have hcomp : barSub V₀ V hV.isElemAbelian L ∈ compBar D.M V₀ V hV.isElemAbelian :=
    barSub_mem_compBar_of_uniqueMax h127 hV hC117 hL hU
  have hnorm : Tbar9 D ≤ Subgroup.normalizer (K1Nine D L : Set (Mbar9 D)) :=
    CFSG.Quasithin.S152Y.imageOTwoQuot_le_normalizer (M := D.M) (X := D.T) (Y := L) hTL
  obtain ⟨L₁, L₂, hT₁, hT₂, hsup, hq₁, hq₂⟩ :=
    exists_s3_pair_of_calC_exp4 (D := D) (L := L) hL hnorm hshape hexp hKpair
  have hST : D.T ⊓ Subgroup.normalizer (L : Set G) = D.T := inf_eq_left.mpr hTL
  have hk2 : D.k = 2 :=
    h17_4 L L₁ L₂ hL hTL hcomp (by rw [hST]; exact hT₁)
      (by rw [hST]; exact hT₂) (by rw [hST]; exact hsup) hq₁ hq₂
      (Or.inr (aCandLe_two_of_barO2Z17_A6 h106 hL hshape))
      (Inputs1719.uniqueMax_sup_T_of_not_thin h869 hL hnt)
  omega

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.S17
