module

public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section7.OddCore
import CFSG.HardMathSupport.Malle.OvergroupTransport.Transport
import CFSG.HardMathSupport.Solomon.Proving.GLBCoreNormalizer
import CFSG.LocalAnalysis.UniquenessCase.UC6Dict

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartOne.Section7

open CFSG.Open
open CFSG.RankThree.PartOne (IsStronglyPEmbedded)

variable {G : Type} [Group G] [Finite G]

theorem normalizer_le_of_uniqueFourUnique (hU : uniqueFourUnique G) {M : Subgroup G}
    (hM : uniqueFourIsMaxTwoLocal M) {p : ℕ} (hp : p ∈ uniqueFourSigma M) :
    ∀ D : Subgroup G, D ≠ ⊥ → IsPGroup 2 D →
      2 ≤ CFSG.Open.pRank p (Subgroup.normalizer (D : Set G) ⊓ M) →
      Subgroup.normalizer (D : Set G) ≤ M := by
  intro D hD hD2 hrank
  exact (hU M hM ⟨p, hp⟩).2
    (Subgroup.normalizer (D : Set G)) ⟨D, hD, hD2, rfl⟩ ⟨p, hp, hrank⟩

theorem pRank_pPrimeCore_le_three_of_uniqueFourUnique (hU : uniqueFourUnique G)
    {M : Subgroup G} (hM : uniqueFourIsMaxTwoLocal M) {p : ℕ} (hp : p ∈ uniqueFourSigma M)
    (hsp : IsStronglyPEmbedded p M) {H : Subgroup G} (hHM : ¬ H ≤ M)
    (hHrank : 2 ≤ CFSG.Open.pRank p (H ⊓ M)) {q : ℕ} (hq : q.Prime) :
    CFSG.Open.pRank q ((CFSG.pPrimeCore p ↥H).map H.subtype) ≤ 3 := by
  classical
  haveI : Fact q.Prime := ⟨hq⟩
  let KH : Subgroup ↥H := CFSG.pPrimeCore p ↥H
  let KG : Subgroup G := KH.map H.subtype
  haveI hKHnormal : (CFSG.pPrimeCore p ↥H).Normal := CFSG.pPrimeCore_normal
  have hKM : KG ≤ M := by
    have h := pPrimeCore_le hsp hp.1.1 hHrank
    simpa [KG, KH] using h
  by_contra hle
  have h4KG : 4 ≤ CFSG.Open.pRank q KG := by
    change 4 ≤ CFSG.Open.pRank q ((CFSG.pPrimeCore p ↥H).map H.subtype)
    exact Nat.succ_le_of_lt (Nat.lt_of_not_ge hle)
  have h4M : 4 ≤ CFSG.Open.pRank q M :=
    h4KG.trans (CFSG.SectionRank.pRank_mono hq.one_lt hKM)
  have hq2 : q ≠ 2 := by
    rintro rfl
    have hoddKH : Odd (Nat.card KH) := by
      simpa [KH] using
        odd_card_pPrimeCore hsp hp.1.1 (normalizer_le_of_uniqueFourUnique hU hM hp) hHM hHrank
    have hcard : Nat.card KG = Nat.card KH := by
      dsimp [KG]
      exact Subgroup.card_map_of_injective H.subtype_injective
    have hoddKG : Odd (Nat.card KG) := by
      rw [hcard]
      exact hoddKH
    obtain ⟨E, hEKG, hEel, hEcard⟩ :=
      CFSG.SectionRank.exists_pRank (p := 2) (by norm_num : 1 < 2) KG
    have h2E : 2 ∣ Nat.card E := by
      rw [hEcard]
      exact dvd_pow_self 2 (by omega)
    have h2KG : 2 ∣ Nat.card KG := h2E.trans (Subgroup.card_dvd_of_le hEKG)
    exact (Nat.not_even_iff_odd.mpr hoddKG) (even_iff_two_dvd.mpr h2KG)
  have hq_sigma : q ∈ uniqueFourSigma M :=
    CFSG.LocalAnalysis.UniquenessCase.UC6.four_le_pRank_imp_mem_sigma hU
      hM hq hq2 h4M
  obtain ⟨P, hPM, hΓM⟩ :=
    CFSG.LocalAnalysis.UniquenessCase.UC6.exists_sylow_le_of_sigma hU
      hM hq_sigma
  have hb := (hU M hM ⟨q, hq_sigma⟩).2
  have h4KH : 4 ≤ CFSG.Open.pRank q KH := by
    have hrank : CFSG.Open.pRank q KG = CFSG.Open.pRank q KH :=
      CFSG.HardMathSupport.Malle.OvergroupTransport.pRank_map_of_injective q
        H.subtype_injective KH
    rwa [hrank] at h4KG
  obtain ⟨EH, hEHKH, hEelH, hEcardH⟩ :=
    CFSG.SectionRank.exists_pRank (p := q) hq.one_lt KH
  have hEHsub_q : IsPGroup q (EH.subgroupOf KH) :=
    (hEelH.isPGroup).of_equiv (Subgroup.subgroupOfEquivOfLe hEHKH).symm
  obtain ⟨R_H, hEH_RH⟩ := hEHsub_q.exists_le_sylow
  let RG : Subgroup G := ((R_H : Subgroup ↥KH).map KH.subtype).map H.subtype
  have hEH_le : EH ≤ ((R_H : Subgroup ↥KH).map KH.subtype : Subgroup ↥H) := by
    rw [← Subgroup.map_subgroupOf_eq_of_le hEHKH]
    exact Subgroup.map_mono hEH_RH
  have hEHG_le_RG : EH.map H.subtype ≤ RG := by
    dsimp [RG]
    exact Subgroup.map_mono hEH_le
  have hRG_q : IsPGroup q RG := by
    dsimp [RG]
    exact (R_H.isPGroup'.map KH.subtype).map H.subtype
  have hRG_le_KG : RG ≤ KG := by
    dsimp [RG, KG]
    exact Subgroup.map_mono (Subgroup.map_subtype_le (R_H : Subgroup ↥KH))
  have hRG_le_M : RG ≤ M := hRG_le_KG.trans hKM
  have h4RG : 4 ≤ CFSG.Open.pRank q RG := by
    have hEHG_el : IsElemAbelian q (EH.map H.subtype) :=
      CFSG.SectionRank.isElemAbelian_map hEelH H.subtype
    have hEHG_card : Nat.card (EH.map H.subtype) = q ^ CFSG.Open.pRank q KH := by
      rw [Subgroup.card_map_of_injective H.subtype_injective, hEcardH]
    have h := CFSG.SectionRank.le_pRank hq.one_lt hEHG_le_RG hEHG_el hEHG_card
    exact h4KH.trans h
  obtain ⟨g, hg⟩ :=
    CFSG.LocalAnalysis.UniquenessCase.UC6.exists_le_uniqueFourConj_sylow (p := q) hRG_q P
  have hRc_le_P : uniqueFourConj g⁻¹ RG ≤ (P : Subgroup G) := by
    have h := CFSG.LocalAnalysis.UniquenessCase.UC6.uniqueFourConj_mono hg g⁻¹
    rw [CFSG.LocalAnalysis.UniquenessCase.UC6.uniqueFourConj_inv_conj] at h
    exact h
  have hRc_le_M : uniqueFourConj g⁻¹ RG ≤ M := hRc_le_P.trans hPM
  have hRc_le_Mg : uniqueFourConj g⁻¹ RG ≤ uniqueFourConj g⁻¹ M :=
    CFSG.LocalAnalysis.UniquenessCase.UC6.uniqueFourConj_mono hRG_le_M g⁻¹
  have h4Rc : 4 ≤ CFSG.Open.pRank q (uniqueFourConj g⁻¹ RG) := by
    rw [CFSG.LocalAnalysis.UniquenessCase.UC6.pRank_uniqueFourConj q hq RG g⁻¹]
    exact h4RG
  have h4inter : 4 ≤ CFSG.Open.pRank q (uniqueFourConj g⁻¹ M ⊓ M) :=
    h4Rc.trans (CFSG.SectionRank.pRank_mono hq.one_lt (le_inf hRc_le_Mg hRc_le_M))
  have hMg_local : IsTwoLocal (uniqueFourConj g⁻¹ M) :=
    CFSG.LocalAnalysis.UniquenessCase.UC6.isTwoLocal_conj hM.1 g⁻¹
  have hMg_max : IsMaxTwoLocalSubgroup (uniqueFourConj g⁻¹ M) :=
    CFSG.LocalAnalysis.UniquenessCase.UC6.isMaxTwoLocal_conj hM g⁻¹
  have hMg_le_M : uniqueFourConj g⁻¹ M ≤ M :=
    hb (uniqueFourConj g⁻¹ M) hMg_local
      ⟨q, hq_sigma, le_trans (by norm_num) h4inter⟩
  have hMg_eq_M : uniqueFourConj g⁻¹ M = M :=
    (hMg_max.2 M hM.1 hMg_le_M).symm
  have h2Rc : 2 ≤ CFSG.Open.pRank q (uniqueFourConj g⁻¹ RG) :=
    le_trans (by norm_num) h4Rc
  have hNRc_M : Subgroup.normalizer (uniqueFourConj g⁻¹ RG : Set G) ≤ M :=
    (CFSG.HardMathSupport.Solomon.Proving.normalizer_le_glbCore hRc_le_P h2Rc).trans hΓM
  have hNRc_Mg : Subgroup.normalizer (uniqueFourConj g⁻¹ RG : Set G) ≤
      uniqueFourConj g⁻¹ M := by
    rw [hMg_eq_M]
    exact hNRc_M
  have hNRG_M : Subgroup.normalizer (RG : Set G) ≤ M := by
    have h := CFSG.LocalAnalysis.UniquenessCase.UC6.uniqueFourConj_mono hNRc_Mg g
    rw [CFSG.LocalAnalysis.UniquenessCase.UC6.uniqueFourConj_normalizer,
      CFSG.LocalAnalysis.UniquenessCase.UC6.uniqueFourConj_conj_inv,
      CFSG.LocalAnalysis.UniquenessCase.UC6.uniqueFourConj_conj_inv] at h
    exact h
  have hfr : Subgroup.normalizer
      (((R_H : Subgroup ↥KH).map KH.subtype : Subgroup ↥H) : Set ↥H) ⊔ KH = ⊤ :=
    Sylow.normalizer_sup_eq_top (p := q) (G := ↥H) (N := KH) R_H
  have hsplit : (Subgroup.normalizer
      (((R_H : Subgroup ↥KH).map KH.subtype : Subgroup ↥H) : Set ↥H)).map H.subtype ⊔
        KG = H := by
    have h := congrArg (Subgroup.map H.subtype) hfr
    rw [Subgroup.map_sup, Subgroup.map_top, Subgroup.range_subtype] at h
    simpa [KG] using h
  have hnorm_le_M : (Subgroup.normalizer
      (((R_H : Subgroup ↥KH).map KH.subtype : Subgroup ↥H) : Set ↥H)).map H.subtype ≤
        M :=
    (Subgroup.le_normalizer_map H.subtype).trans hNRG_M
  exact hHM (hsplit ▸ sup_le hnorm_le_M hKM)

end CFSG.LocalAnalysis.UniquenessCase.PartOne.Section7
