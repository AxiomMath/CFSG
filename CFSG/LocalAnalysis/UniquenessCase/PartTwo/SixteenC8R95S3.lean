module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC8R95B1
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC8R95S1
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC8R95S2D
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC8R95A1
import CFSG.RankThree.GroupTheory.SteinbergBMCrossPrimeLocalCore
public import CFSG.LocalAnalysis.UniquenessCase.UCKInputs

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22.F09

open CFSG.Open CFSG.LocalAnalysis.RankThreeUC Subgroup
open CFSG.LocalAnalysis.UniquenessCase.PartOne.Section9 (xbar9 wbar9)
open CFSG.Blueprint (LieModel)

variable {G : Type} [Group G] [Finite G]

theorem r95_index_hbar {D : Data G} {Y H : Subgroup G} (hYH : Y ≤ H)
    (hH : H = L9 Y H ⊔ (H ⊓ D.M)) :
    ((H ⊓ D.M) ⊔ I9 H).relIndex H = (wbar9 D Y H).index := by
  let π : ↥H →* Hbar9 H := QuotientGroup.mk' (CFSG.pPrimeCore 3 ↥H)
  have hπ : Function.Surjective π := QuotientGroup.mk'_surjective _
  have hLH : L9 Y H ≤ H :=
    CFSG.LocalAnalysis.UniquenessCase.PartOne.Section9.L9_le_of_le hYH
  set V : Subgroup (Hbar9 H) := img9 H (H ⊓ D.M) with hV
  set Lb : Subgroup (Hbar9 H) := img9 H (L9 Y H) with hLb
  have hIker : ((CFSG.pPrimeCore 3 ↥H).map H.subtype).subgroupOf H = π.ker := by
    rw [QuotientGroup.ker_mk']
    show ((CFSG.pPrimeCore 3 ↥H).map H.subtype).comap H.subtype = CFSG.pPrimeCore 3 ↥H
    exact Subgroup.comap_map_eq_self_of_injective H.subtype_injective _
  have hcomap : ((H ⊓ D.M) ⊔ I9 H).subgroupOf H = V.comap π := by
    change ((H ⊓ D.M) ⊔ (CFSG.pPrimeCore 3 ↥H).map H.subtype).subgroupOf H =
      (((H ⊓ D.M).subgroupOf H).map π).comap π
    rw [Subgroup.subgroupOf_sup inf_le_left (Subgroup.map_subtype_le _), hIker,
      Subgroup.comap_map_eq]
  have hLbN : Lb.Normal := by
    rw [hLb]
    exact ((Subgroup.normal_subgroupOf_iff_le_normalizer hLH).2
      (CFSG.LocalAnalysis.UniquenessCase.PartOne.Section9.le_normalizer_L9 Y H)).map π hπ
  have hsupV : Lb ⊔ V = ⊤ := by
    have h1 : (L9 Y H ⊔ (H ⊓ D.M)).subgroupOf H = ⊤ := by
      rw [← hH, Subgroup.subgroupOf_self]
    have h2 : ((L9 Y H).subgroupOf H ⊔ (H ⊓ D.M).subgroupOf H).map π = ⊤ := by
      rw [← Subgroup.subgroupOf_sup hLH inf_le_left, h1,
        Subgroup.map_top_of_surjective π hπ]
    rw [Subgroup.map_sup] at h2
    rw [hLb, hV]
    exact h2
  haveI : Lb.Normal := hLbN
  have hVindex : V.index = V.relIndex Lb := by
    rw [← Subgroup.relIndex_top_right (H := V), ← hsupV]
    exact CFSG.ABGLocalTools.relIndex_sup_eq_relIndex_of_normal Lb V
  change (((H ⊓ D.M) ⊔ I9 H).subgroupOf H).index = (wbar9 D Y H).index
  rw [hcomap, Subgroup.index_comap_of_surjective (H := V) (f := π) hπ]
  exact hVindex.trans rfl

theorem r95_sylow_clause (hK461 : UCK.K461)
    (hSch : CFSG.AGLEmbedding.KFactCatalogSchreier) {D : Data G} {Y H D₃ : Subgroup G}
    (hyp : Hyp91 D Y H D₃) (hH : H ≠ ⊤) (h92 : R92 D)
    (hX : LieModel (BarO3 (Opp 3 Y)) .PSL 3 2 1) :
    ∃ S : Subgroup G, CFSG.ABGLocalTools.IsSylowOf 2 S H ∧ S ≤ D.M := by
  have hI : ¬ 2 ∣ (I9 H ⊓ D.M).relIndex (I9 H) := r95_I_odd_index hK461 hSch hyp hH hX
  have hIH : I9 H ≤ H := Subgroup.map_subtype_le _
  have hHI : H ≤ normalizer (I9 H : Set G) := by
    simpa only [I9, CFSG.inSubgroup] using
      CFSG.RankThree.GroupTheory.SteinbergBM.le_normalizer_inSubgroup_pPrimeCore 3 H
  have hB : ¬ 2 ∣ ((H ⊓ D.M) ⊔ I9 H).relIndex H := by
    by_cases hLM : img9 H (L9 Y H) ≤ img9 H (H ⊓ D.M)
    · rw [← r95_prod_of_lbar_le hyp hH h92 hLM, Subgroup.relIndex_self]
      norm_num
    · rw [r95_index_hbar hyp.2.1.1 ((h92 Y H D₃ hyp hH).1)]
      exact (r95_caseB hyp hH h92 hX hLM).choose_spec.2.2.2
  exact r95s_sylow_of_odd_index hIH hHI hI hB

end CFSG.LocalAnalysis.UniquenessCase.UC22.F09
