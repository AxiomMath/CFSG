module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.ConjClosureSimple
public import CFSG.Quasithin.Vol2.Ch11SecFO2L

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22
open scoped Pointwise

variable {G : Type} [Group G] [Finite G]

namespace ElevenNine

theorem eq_top_of_sup_eq_top_of_components {A : Type} [Group A] [Finite A] {W X₀ : Subgroup A}
    [W.Normal] (hperf : ⁅(⊤ : Subgroup A), (⊤ : Subgroup A)⁆ = ⊤) (hsup : W ⊔ X₀ = ⊤)
    {S : Set (Subgroup A)} (hS : ∀ K ∈ S, CFSG.IsComponent K) (hgen : sSup S = ⊤)
    (hnot : ∀ K ∈ S, ¬ K ≤ W) : X₀ = ⊤ := by
  have htopcent : (⊤ : Subgroup A) ≤ Subgroup.centralizer (W : Set A) := by
    rw [← hgen]
    refine sSup_le fun K hK => ?_
    rcases CFSG.LocalCores.component_normal_subgroup (hS K hK) (inferInstance : W.Normal) with
      h | h
    · exact absurd h (hnot K hK)
    · exact (Subgroup.commutator_eq_bot_iff_le_centralizer).1 h
  have hWcomm : ∀ w ∈ W, ∀ a : A, w * a = a * w := fun w hw a =>
    Subgroup.mem_centralizer_iff.1 (htopcent (Subgroup.mem_top a)) w hw
  have hX₀n : X₀.Normal := by
    rw [← Subgroup.normalizer_eq_top_iff, eq_top_iff, ← hsup]
    refine sup_le ?_ Subgroup.le_normalizer
    intro w hw
    rw [Subgroup.mem_normalizer_iff]
    intro x
    constructor
    · intro hx
      rwa [hWcomm w hw x, mul_assoc, mul_inv_cancel, mul_one]
    · intro hx
      rwa [hWcomm w hw x, mul_assoc, mul_inv_cancel, mul_one] at hx
  haveI : X₀.Normal := hX₀n
  haveI : IsMulCommutative W :=
    IsMulCommutative.of_comm fun a b => Subtype.ext (hWcomm (b : A) b.2 (a : A)).symm
  have hcomm : commutator A ≤ X₀ :=
    Subgroup.Normal.commutator_le_of_self_sup_commutative_eq_top (N := X₀) (H := W)
      (by rw [sup_comm]; exact hsup) inferInstance
  refine le_antisymm le_top ?_
  rw [← hperf]
  exact hcomm

theorem sSup_barImage_conjSetOf_eq_top (M K : Subgroup G) :
    sSup ((barImage (conjClosure M K)) '' (conjSetOf M K)) = ⊤ := by
  set Y := conjClosure M K with hYdef
  set S := conjSetOf M K with hSdef
  have hle : ∀ K' ∈ S, K' ≤ Y := by
    intro K' hK'
    rw [hYdef]
    exact le_iSup₂_of_le K' (by rwa [← hSdef]) le_rfl
  have hgen : (⨆ K' ∈ S, K'.subgroupOf Y) = ⊤ := by
    apply Subgroup.map_injective Y.subtype_injective
    simp only [Subgroup.map_iSup, Subgroup.map_top, Subgroup.range_subtype]
    refine le_antisymm ?_ ?_
    · refine iSup₂_le fun K' hK' => ?_
      rw [Subgroup.map_subgroupOf_eq_of_le (hle K' hK')]
      exact hle K' hK'
    · rw [hYdef]
      unfold conjClosure
      refine iSup₂_le fun K' hK' => ?_
      have hK'S : K' ∈ S := by rwa [hSdef]
      rw [← Subgroup.map_subgroupOf_eq_of_le (hle K' hK'S)]
      exact le_iSup₂_of_le K' hK'S le_rfl
  rw [sSup_image]
  simp only [barImage]
  rw [show (⨆ K' ∈ S, (K'.subgroupOf Y).map (QuotientGroup.mk' (CFSG.pCore 2 ↥Y))) =
      (⨆ K' ∈ S, K'.subgroupOf Y).map (QuotientGroup.mk' (CFSG.pCore 2 ↥Y)) by
    simp only [Subgroup.map_iSup]]
  rw [hgen, Subgroup.map_top_of_surjective _ (QuotientGroup.mk'_surjective _)]

theorem le_of_barImage_le {K W Y : Subgroup G} (hKY : K ≤ Y) (hWY : W ≤ Y)
    (hW : (W.subgroupOf Y).Normal) (hperf : ⁅K, K⁆ = K)
    (h : barImage Y K ≤ barImage Y W) : K ≤ W := by
  have hWn : Y ≤ normalizer (W : Set G) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hWY).1 hW
  have hstep : K ≤ W ⊔ pCoreOf 2 Y := by
    intro k hk
    have hkY : k ∈ Y := hKY hk
    have hmem : uc22p21cPi Y ⟨k, hkY⟩ ∈ barImage Y W :=
      h (uc22p21c_mem_barImage.2 ⟨⟨k, hkY⟩, hk, rfl⟩)
    obtain ⟨w, hwW, hw⟩ := uc22p21c_mem_barImage.1 hmem
    have hz : ((w : ↥Y)⁻¹ * ⟨k, hkY⟩ : ↥Y) ∈ CFSG.pCore 2 ↥Y := by
      have h1 : uc22p21cPi Y ((w : ↥Y)⁻¹ * ⟨k, hkY⟩) = 1 := by
        rw [map_mul, map_inv, hw, inv_mul_cancel]
      exact (QuotientGroup.eq_one_iff _).1 h1
    have hWS : pCoreOf 2 Y ≤ normalizer (W : Set G) := (uc22p21c_pCoreOf_le Y).trans hWn
    have hkprod : k ∈ (W : Set G) * (pCoreOf 2 Y : Set G) :=
      ⟨w, hwW, ((w : ↥Y)⁻¹ * ⟨k, hkY⟩ : ↥Y), ⟨_, hz, rfl⟩,
        by simp only [Subgroup.coe_mul, Subgroup.coe_inv]; group⟩
    rwa [← Subgroup.coe_mul_of_right_le_normalizer_left W (pCoreOf 2 Y) hWS] at hkprod
  exact CFSG.Quasithin.Vol2.Ch11.SecF.le_of_le_sup_of_perfect hperf
    (uc22p21c_isPGroup_pCoreOf Y) ((uc22p21c_pCoreOf_le Y).trans hWn) hstep

theorem sup_pCoreOf_eq_of_components {M Y W X₀ K : Subgroup G} (hK : K ∈ calC M)
    (hY : Y = conjClosure M K) (hWn : M ≤ normalizer (W : Set G)) (hWY : W ≤ Y) (hX₀Y : X₀ ≤ Y)
    (hsup : Y ≤ W ⊔ X₀) (hnot : ¬ K ≤ W) : X₀ ⊔ pCoreOf 2 Y = Y := by
  obtain ⟨hYM, -, hcalc⟩ := conjSetOf_subset_calC_conjClosure hK
  have hKM : K ≤ M := CFSG.Quasithin.A3.subnormal_le hK.1
  have hcalcY : ∀ K' ∈ conjSetOf M K, K' ∈ calC Y :=
    fun K' hK' => hY.symm ▸ hcalc K' hK'
  have hWnY : Y ≤ normalizer (W : Set G) := (hY.symm ▸ hYM).trans hWn
  have hWnorm : (W.subgroupOf Y).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hWY).2 hWnY
  have hsup_eq : W ⊔ X₀ = Y := le_antisymm (sup_le hWY hX₀Y) hsup
  have hsup' : barImage Y W ⊔ barImage Y X₀ = ⊤ := by
    have h1 : barImage Y W ⊔ barImage Y X₀ = barImage Y (W ⊔ X₀) := by
      unfold barImage
      rw [← Subgroup.map_sup, ← Subgroup.subgroupOf_sup hWY hX₀Y]
    rw [h1, hsup_eq]
    unfold barImage
    rw [Subgroup.subgroupOf_self,
      Subgroup.map_top_of_surjective _ (QuotientGroup.mk'_surjective _)]
  have hS' : ∀ K' ∈ (barImage Y '' conjSetOf M K), CFSG.IsComponent K' := by
    rintro K' ⟨K₀, hK₀, rfl⟩
    exact uc22p22l_barImage_isComponent (hcalcY K₀ hK₀)
  have hgen' : sSup (barImage Y '' conjSetOf M K) = ⊤ := by
    rw [hY]
    exact sSup_barImage_conjSetOf_eq_top M K
  have hperf' : ⁅(⊤ : Subgroup (Bar2 Y)), (⊤ : Subgroup (Bar2 Y))⁆ = ⊤ := by
    refine le_antisymm le_top ?_
    have hle : sSup (barImage Y '' conjSetOf M K) ≤
        ⁅(⊤ : Subgroup (Bar2 Y)), (⊤ : Subgroup (Bar2 Y))⁆ := by
      refine sSup_le fun K' hK' => ?_
      rw [← Subgroup.isPerfect_iff.mp (hS' K' hK').1.1]
      exact Subgroup.commutator_mono le_top le_top
    simpa only [hgen'] using hle
  have hnot' : ∀ K' ∈ (barImage Y '' conjSetOf M K), ¬ K' ≤ barImage Y W := by
    rintro K' ⟨K₀, hK₀, rfl⟩ hle
    have hK₀Y : K₀ ≤ Y := by
      rw [hY]
      exact le_iSup₂_of_le K₀ hK₀ le_rfl
    have hK₀W : K₀ ≤ W :=
      le_of_barImage_le hK₀Y hWY hWnorm (hcalcY K₀ hK₀).2.1 hle
    obtain ⟨g, hg, hgK⟩ := hK₀
    apply hnot
    rw [hgK] at hK₀W
    intro x hx
    exact (Subgroup.mem_normalizer_iff.1 (hWn hg) x).2
      (by simpa only [MulAut.conj_apply] using
        hK₀W ⟨x, hx, by simp [MulAut.conj_apply]⟩)
  haveI : (barImage Y W).Normal :=
    hWnorm.map (QuotientGroup.mk' (CFSG.pCore 2 ↥Y)) (QuotientGroup.mk'_surjective _)
  have htop : barImage Y X₀ = ⊤ :=
    eq_top_of_sup_eq_top_of_components (A := Bar2 Y) hperf' hsup' hS' hgen' hnot'
  apply le_antisymm (sup_le hX₀Y (uc22p21c_pCoreOf_le Y))
  intro y hy
  have hy' : uc22p21cPi Y ⟨y, hy⟩ ∈ barImage Y X₀ := by
    rw [htop]
    exact Subgroup.mem_top _
  obtain ⟨x, hxX₀, hx⟩ := uc22p21c_mem_barImage.1 hy'
  have hpc : (x : G)⁻¹ * y ∈ pCoreOf 2 Y := by
    refine ⟨(x : ↥Y)⁻¹ * ⟨y, hy⟩, ?_, rfl⟩
    have h1 : uc22p21cPi Y ((x : ↥Y)⁻¹ * ⟨y, hy⟩) = 1 := by
      rw [map_mul, map_inv, hx, inv_mul_cancel]
    exact (QuotientGroup.eq_one_iff _).1 h1
  have hmul : (x : G) * ((x : G)⁻¹ * y) = y := by group
  rw [← hmul]
  exact Subgroup.mul_mem _ (Subgroup.mem_sup_left hxX₀) (Subgroup.mem_sup_right hpc)

end ElevenNine

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
