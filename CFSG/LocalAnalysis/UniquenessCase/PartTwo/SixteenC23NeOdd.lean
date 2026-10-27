module

public import CFSG.CGT.PushingUpLit.Transport
public import CFSG.LocalAnalysis.SeitzReduction.EPilotPosition
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenResultsB
public import CFSG.LocalAnalysis.UniquenessCase.UC22P22f

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22

variable {G : Type} [Group G] [Finite G]

private theorem c23ne_exists_mem_normalizer_of_lt {H P : Subgroup G} (hP : IsPGroup 2 P)
    (hHP : H ≤ P) (hne : H ≠ P) :
    ∃ x ∈ P, x ∉ H ∧ x ∈ Subgroup.normalizer (H : Set G) := by
  set IP : Subgroup P := H.subgroupOf P with hIP
  have hIPlt : IP < ⊤ := by
    refine lt_of_le_of_ne le_top fun htop => hne (le_antisymm hHP fun x hx => ?_)
    have : (⟨x, hx⟩ : P) ∈ IP := by rw [htop]; trivial
    exact Subgroup.mem_subgroupOf.mp this
  have hnc : NormalizerCondition P :=
    Group.normalizerCondition_of_isNilpotent (G := P) (h := hP.isNilpotent)
  have hlt : IP < Subgroup.normalizer (IP : Set P) := hnc IP hIPlt
  obtain ⟨x, hxN, hxnot⟩ := SetLike.exists_of_lt hlt
  refine ⟨x, x.2, fun hx => hxnot (Subgroup.mem_subgroupOf.mpr hx), ?_⟩
  have hxsub : x ∈ (Subgroup.normalizer (H : Set G)).subgroupOf P := by
    rw [Subgroup.subgroupOf_normalizer_eq hHP]
    exact hxN
  exact Subgroup.mem_subgroupOf.mp hxsub

private theorem c23ne_conj_wClos_prop (D : Data G) (h63 : R16_63 D) {V₀ V L : Subgroup G}
    {hV : IsElemAbelian 2 V} (hS : Sect16 D V₀ V L hV) (hsit : Sit1663 D V₀ V hV L)
    {m : G} (hm : m ∈ D.M) :
    ⁅E3.wClos V 0 (conjSubgroup D.T m), V⁆ = ⊥ ∧
      Subgroup.normalizer (E3.wClos V 0 (conjSubgroup D.T m) : Set G) ≤ D.M := by
  have h63' := h63 V₀ V L hV hS hsit
  have hMnorm : D.M ≤ Subgroup.normalizer (V : Set G) :=
    hS.setting.hyp151.hyp125.pairFacts.le_normalizer
  have hVm : conjSubgroup V m = V :=
    conjSubgroup_eq_iff_mem_normalizer.mpr (hMnorm hm)
  have hW : E3.wClos V 0 (conjSubgroup D.T m) = conjSubgroup (E3.wClos V 0 D.T) m :=
    E3.wClos_conj (V := V) (i := 0) D.T m
  constructor
  · rw [hW]
    calc ⁅conjSubgroup (E3.wClos V 0 D.T) m, V⁆
        = ⁅conjSubgroup (E3.wClos V 0 D.T) m, conjSubgroup V m⁆ := by rw [hVm]
      _ = conjSubgroup ⁅E3.wClos V 0 D.T, V⁆ m :=
        (E3.conjSubgroup_commutator _ _ m).symm
      _ = ⊥ := by rw [h63'.1, E3.conjSubgroup_bot]
  · rw [hW, ← E3.conjSubgroup_normalizer]
    exact (E3.conjSubgroup_mono_left m h63'.2).trans
      (le_of_eq (conjSubgroup_eq_iff_mem_normalizer.mpr
        (Subgroup.le_normalizer (H := D.M) hm)))

theorem c23ne_odd_relIndex_centralizer (D : Data G) (h63 : R16_63 D) {V₀ V L : Subgroup G}
    {hV : IsElemAbelian 2 V} (hS : Sect16 D V₀ V L hV) (hsit : Sit1663 D V₀ V hV L)
    {v : G} (hv : v ∈ V) (hv1 : v ≠ 1) :
    Odd (D.M.relIndex (centralizer ({v} : Set G))) := by
  classical
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set H : Subgroup G := centralizer ({v} : Set G) with hH
  obtain ⟨S, hSCM⟩ := CFSG.ABGLocalTools.exists_isSylowOf (p := 2) (H ⊓ D.M)
  have hSH : S ≤ H := hSCM.le.trans inf_le_left
  have hSM : S ≤ D.M := hSCM.le.trans inf_le_right
  obtain ⟨Q, hQle⟩ := (hSCM.isPGroup.comap_subtype (K := D.M)).exists_le_sylow
  let T' : Subgroup G := Q.map D.M.subtype
  have hT'M : CFSG.ABGLocalTools.IsSylowOf 2 T' D.M := ⟨Q, rfl⟩
  have hST' : S ≤ T' := by
    intro x hx
    exact ⟨⟨x, hSM hx⟩, hQle (Subgroup.mem_subgroupOf.mpr hx), rfl⟩
  obtain ⟨k, hk, hT'eq⟩ := uc22p22f_exists_conj_sylow D.sylowM hT'M
  have hT'conj : T' = conjSubgroup D.T k⁻¹ := by
    rw [hT'eq]
    simp only [conjSubgroup, inv_inv]
  have hT'prop : ⁅E3.wClos V 0 T', V⁆ = ⊥ ∧
      Subgroup.normalizer (E3.wClos V 0 T' : Set G) ≤ D.M := by
    have h := c23ne_conj_wClos_prop D h63 hS hsit (m := k⁻¹) (D.M.inv_mem hk)
    rwa [← hT'conj] at h
  have hP2 : IsPGroup 2 ↥(T' ⊓ H) := hT'M.isPGroup.to_inf_left
  have hPCM : T' ⊓ H ≤ H ⊓ D.M := le_inf inf_le_right (inf_le_left.trans hT'M.le)
  have hPS : T' ⊓ H = S := hSCM.eq_of_le (le_inf hST' hSH) hPCM hP2
  have hW_le : E3.wClos V 0 T' ≤ E3.wClos V 0 S := by
    refine E3.wClos_le_of_forall fun A hA => ?_
    obtain ⟨hAT', g, hAg, hmg⟩ := hA
    have hAle : A ≤ E3.wClos V 0 T' :=
      E3.le_wClos (E3.mem_gammaSet_iff.mpr ⟨hAT', g, hAg, hmg⟩)
    have hAcent : A ≤ Subgroup.centralizer (V : Set G) :=
      hAle.trans
        ((Subgroup.commutator_eq_bot_iff_le_centralizer).1 hT'prop.1)
    have hAH : A ≤ H :=
      hAcent.trans (Subgroup.centralizer_le (Set.singleton_subset_iff.mpr hv))
    have hAS : A ≤ S := by
      have h1 : A ≤ T' ⊓ H := le_inf hAT' hAH
      rwa [hPS] at h1
    exact E3.le_wClos ⟨hAS, ⟨g, hAg, hmg⟩⟩
  have hWeq : E3.wClos V 0 S = E3.wClos V 0 T' :=
    le_antisymm (E3.wClos_mono hST') hW_le
  have hNS_le : Subgroup.normalizer (E3.wClos V 0 S) ≤ D.M := by
    rw [hWeq]
    exact hT'prop.2
  have hNS : Subgroup.normalizer (S : Set G) ≤ D.M :=
    (E3.normalizer_le_normalizer_wClos (V := V) (i := 0) S).trans hNS_le
  have hSHsylow : CFSG.ABGLocalTools.IsSylowOf 2 S H := by
    obtain ⟨QH, hQHle⟩ := (hSCM.isPGroup.comap_subtype (K := H)).exists_le_sylow
    let R : Subgroup G := QH.map H.subtype
    have hRH : CFSG.ABGLocalTools.IsSylowOf 2 R H := ⟨QH, rfl⟩
    have hSR : S ≤ R := by
      intro x hx
      exact ⟨⟨x, hSH hx⟩, hQHle (Subgroup.mem_subgroupOf.mpr hx), rfl⟩
    have hRS : R = S := by
      by_contra hne
      obtain ⟨x, hxR, hxS, hxN⟩ :=
        c23ne_exists_mem_normalizer_of_lt hRH.isPGroup hSR (fun h => hne h.symm)
      have hxH : x ∈ H := hRH.le hxR
      have hxM : x ∈ D.M := hNS hxN
      have hxCM : x ∈ H ⊓ D.M := Subgroup.mem_inf.mpr ⟨hxH, hxM⟩
      have hxp : IsPGroup 2 (Subgroup.zpowers x) :=
        hRH.isPGroup.to_le (Subgroup.zpowers_le.mpr hxR)
      have hzs : Subgroup.zpowers x ≤ Subgroup.normalizer (S : Set G) :=
        Subgroup.zpowers_le.mpr hxN
      have hQp : IsPGroup 2 ↥(Subgroup.zpowers x ⊔ S) :=
        IsPGroup.to_sup_of_normal_right' hxp hSCM.isPGroup hzs
      have hQCM : Subgroup.zpowers x ⊔ S ≤ H ⊓ D.M :=
        sup_le (Subgroup.zpowers_le.mpr hxCM) (le_inf hSH hSM)
      have heq : Subgroup.zpowers x ⊔ S = S := hSCM.eq_of_le le_sup_right hQCM hQp
      have hxS' : x ∈ Subgroup.zpowers x ⊔ S :=
        (le_sup_left : Subgroup.zpowers x ≤ Subgroup.zpowers x ⊔ S)
          (Subgroup.mem_zpowers x)
      exact hxS (heq ▸ hxS')
    rwa [hRS] at hRH
  have hoddS : Odd (S.relIndex H) := by
    rw [← Nat.not_even_iff_odd, even_iff_two_dvd]
    exact (CFSG.ABGLocalTools.isSylowOf_iff.mp hSHsylow).2.2
  have hrel : (H ⊓ D.M).relIndex H * S.relIndex (H ⊓ D.M) = S.relIndex H := by
    rw [mul_comm]
    exact Subgroup.relIndex_mul_relIndex S (H ⊓ D.M) H (le_inf hSH hSM) inf_le_left
  have hdvd : (H ⊓ D.M).relIndex H ∣ S.relIndex H :=
    ⟨S.relIndex (H ⊓ D.M), hrel.symm⟩
  have hoddCM : Odd ((H ⊓ D.M).relIndex H) := hoddS.of_dvd_nat hdvd
  rw [← Subgroup.inf_relIndex_right D.M H]
  simpa [inf_comm] using hoddCM

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
