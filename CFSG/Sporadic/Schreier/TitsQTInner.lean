module

public import CFSG.Sporadic.Schreier.TitsQTInnerLocal
public import CFSG.Sporadic.Schreier.TitsOuter
public import CFSG.LocalAnalysis.QuasithinUnique.K1.EvenClassicalStrong
public import CFSG.LocalAnalysis.QuasithinUnique.K1.Interface

public noncomputable section

namespace CFSG.Sporadic.Schreier.TitsQT

open CFSG.QuasithinUnique.K1 CFSG.Sporadic.Schreier.Tits CFSG.ComponentClassification

theorem titsD_sylow_pointwise_inner
    (β : titsD ≃* titsD)
    (hβ : ∀ q ∈ (titsSylow : Subgroup titsD), β q = q) :
    ∃ b : titsD, (∀ s ∈ (titsSylow : Subgroup titsD), b * s = s * b) ∧
      ∀ y : titsD, β y = b * y * b⁻¹ := by
  obtain ⟨⟨P, hP⟩, hH, hN, hHN, hJ2, -, hJn, -, hJS, hKS, hCJ, hCK⟩ := AT_Tits_intrinsic_local_pair
  have hZ : ((Subgroup.center (P : Subgroup titsD)).map (P : Subgroup titsD).subtype).map
      titsD.subtype = (Subgroup.center titsS).map titsS.subtype := by
    rw [map_center_map_subtype, hP, subgroupOf_map_titsD titsS_le_titsD]
  have hH' : titsH.subgroupOf titsD = Subgroup.centralizer
      (((Subgroup.center (P : Subgroup titsD)).map (P : Subgroup titsD).subtype :
        Subgroup titsD) : Set titsD) := by
    rw [← subgroupOf_centralizer_map, hZ, hH, Subgroup.inf_subgroupOf_left]
  have hN' : titsN.subgroupOf titsD =
      Subgroup.normalizer ((titsK.subgroupOf titsD : Subgroup titsD) : Set titsD) := by
    rw [hN, Subgroup.inf_subgroupOf_left, Subgroup.subgroupOf_normalizer_eq titsK_le_titsD]
  have hKS' : titsK.subgroupOf titsD ≤ P := hP ▸ titsSubD_le hKS
  have hJS' : titsJ.subgroupOf titsD ≤ P := hP ▸ titsSubD_le hJS
  have hSN' : (P : Subgroup titsD) ≤ titsN.subgroupOf titsD := by
    rw [hP]
    exact titsSubD_le titsS_le_titsN
  have hJH' : titsJ.subgroupOf titsD ≤ titsH.subgroupOf titsD := titsSubD_le titsJ_le_titsH
  have hJp : IsPGroup 2 (titsJ.subgroupOf titsD) :=
    hJ2.of_equiv (Subgroup.subgroupOfEquivOfLe titsJ_le_titsD).symm
  have hJn' : ((titsJ.subgroupOf titsD).subgroupOf (titsH.subgroupOf titsD)).Normal := by
    rw [Subgroup.normal_subgroupOf_iff_le_normalizer hJH',
      ← Subgroup.subgroupOf_normalizer_eq titsJ_le_titsD]
    exact titsSubD_le ((Subgroup.normal_subgroupOf_iff_le_normalizer titsJ_le_titsH).1 hJn)
  have hCJ' : titsH.subgroupOf titsD ⊓
      Subgroup.centralizer ((titsJ.subgroupOf titsD : Subgroup titsD) : Set titsD) ≤
        titsJ.subgroupOf titsD := by
    rw [← centralizer_subgroupOf_eq titsJ_le_titsD]
    exact fun g hg => hCJ ⟨hg.1, hg.2⟩
  have hCK' : titsN.subgroupOf titsD ⊓
      Subgroup.centralizer ((titsK.subgroupOf titsD : Subgroup titsD) : Set titsD) ≤
        titsK.subgroupOf titsD := by
    rw [← centralizer_subgroupOf_eq titsK_le_titsD]
    exact fun g hg => hCK ⟨hg.1, hg.2⟩
  have hgen : titsH.subgroupOf titsD ⊔ titsN.subgroupOf titsD = ⊤ := by
    apply Subgroup.map_injective titsD.subtype_injective
    rw [Subgroup.map_sup, subgroupOf_map_titsD titsH_le_titsD, subgroupOf_map_titsD titsN_le_titsD,
      hHN, map_top_titsD]
  have hPS : (P : Subgroup titsD) = (titsSylow : Subgroup titsD) := hP.trans coe_titsSylow.symm
  have hmemP : ∀ s : titsD, s ∈ (P : Subgroup titsD) ↔ s ∈ (titsSylow : Subgroup titsD) :=
    fun s => by rw [hPS]
  obtain ⟨b, hbS, hb⟩ := sylow_local_pointwise_inner P (titsH.subgroupOf titsD) hH'
    (titsK.subgroupOf titsD) hKS' (titsN.subgroupOf titsD) hN' hSN' (titsJ.subgroupOf titsD) hJp
    hJS' hJH' hJn' hCJ' hCK' hgen β (fun s hs => hβ s ((hmemP s).1 hs))
  exact ⟨b, fun s hs => hbS s ((hmemP s).2 hs), hb⟩

theorem titsD_sylowCentralizingAutInner :
    SylowCentralizingAutInner titsD := by
  refine sylowCentralizingAutInner_of_sylow (titsSylow : Subgroup titsD)
    (isSylowTwoOf_top_iff.mpr ⟨titsSylow.isPGroup', titsSylow.not_dvd_index⟩) fun β hβ => ?_
  obtain ⟨b, -, hb⟩ := titsD_sylow_pointwise_inner β hβ
  exact ⟨b⁻¹, fun y => by rw [hb y, inv_inv]⟩

theorem tits_model_sylowCentralizingAutInner
    (X : Type) [Group X]
    (h : CFSG.Blueprint.ReeTitsModel X .Tits 2 1) : SylowCentralizingAutInner X := by
  obtain ⟨e⟩ := titsModelEquiv X 2 1 h
  exact SylowCentralizingAutInner.of_mulEquiv e titsD_sylowCentralizingAutInner

end CFSG.Sporadic.Schreier.TitsQT
