module

public import CFSG.LocalAnalysis.StandardType.GGSixLayerPDivBasic
public import CFSG.LocalAnalysis.StandardType.GGSixLayerFactsSL

public section

namespace CFSG.StandardType

namespace LayerPDiv

open CFSG.Assembly CFSG.RankThree.PartOne.KCLinComm Matrix LayerFacts

variable {m : ℕ} {F : Type} [Field F] {G : Type*} [Group G]

theorem dvd_card_of_isComponentOf_sl [Finite G] [Finite F] [CharP F 2]
    {ψ : SpecialLinearGroup (Fin (m + 1)) F →* G}
    (hker : ψ.ker ≤ Subgroup.center (SpecialLinearGroup (Fin (m + 1)) F)) {p : ℕ}
    (hp : p.Prime) (hp2 : p ≠ 2) (hpF : p ∣ Nat.card F ^ 2 - 1) {E : Subgroup G}
    (hE : IsPGroup p E) (hEA : ∀ e ∈ E, ∃ A, (e, A) ∈ LinFusion.ggInducedPairs ψ)
    {K : Subgroup G} (hK : IsComponentOf K (ψ.range ⊓ Subgroup.centralizer (E : Set G))) :
    p ∣ Nat.card K := by
  classical
  obtain ⟨r, D, d, _, _, _, θ, hθinj, hθrange⟩ :=
    exists_piGL_centralizer (LinTorus.inducedMatrices ψ E)
      (natCast_card_inducedMatrices_ne_zero hker hp hp2 hE)
  have : ∀ i, CharP (D i) 2 := fun i =>
    charP_of_injective_algebraMap (algebraMap F (D i)).injective 2
  set ι : SpecialLinearGroup (Fin (m + 1)) F →* GL (Fin (m + 1)) F :=
    SpecialLinearGroup.toGL with hιdef
  have hιinj : Function.Injective ι := SpecialLinearGroup.toGL_injective
  have hC₀θ : ggCentSL ψ E = θ.range.comap ι := by rw [hθrange]; rfl
  set S : {b : Fin r // GoodBlock D d b} → Subgroup (SpecialLinearGroup (Fin (m + 1)) F) :=
    fun b => ((blockSL D d b.1).map θ).comap ι with hSdef
  have hSrange : ∀ b : {b : Fin r // GoodBlock D d b}, (blockSL D d b.1).map θ ≤ ι.range := by
    intro b
    have hperf : ⁅blockSL D d b.1, blockSL D d b.1⁆ = blockSL D d b.1 :=
      CFSG.RankThree.PartOne.KCUnitary.commutator_eq_of_isPerfect
        (isPerfect_blockSL b.1 b.2.1 b.2.2)
    rw [← hperf, Subgroup.map_commutator]
    refine (Subgroup.commutator_mono le_top le_top).trans ?_
    rw [← _root_.commutator_def, hιdef, SpecialLinearGroup.range_toGL_eq_ker_det]
    exact Abelianization.commutator_subset_ker _
  have hSmap : ∀ b, (S b).map ι = (blockSL D d b.1).map θ := fun b =>
    Subgroup.map_comap_eq_self (hSrange b)
  have hÑmap : (⨆ b, S b).map ι = (goodSL D d).map θ := by
    rw [Subgroup.map_iSup, goodSL, Subgroup.map_iSup]
    exact iSup_congr hSmap
  have hSC : ∀ b, S b ≤ ggCentSL ψ E := fun b => by
    rw [hC₀θ]
    exact Subgroup.comap_mono (Subgroup.map_le_range θ _)
  have hSn : ∀ b, ∀ c ∈ ggCentSL ψ E, ∀ s ∈ S b, c * s * c⁻¹ ∈ S b := by
    intro b c hc s hs
    rw [hC₀θ] at hc
    obtain ⟨w, hw⟩ := hc
    obtain ⟨g, hg, hgs⟩ := hs
    refine ⟨w * g * w⁻¹, conj_mem_blockSL b.1 w hg, ?_⟩
    rw [map_mul, map_mul, map_inv, hw, hgs, map_mul, map_mul, map_inv]
  have hSq : ∀ b, CFSG.IsQuasisimple (S b) := fun b =>
    CFSG.LocalCores.isQuasisimple_of_mulEquiv
      (((Subgroup.equivMapOfInjective _ θ hθinj).trans
        (MulEquiv.subgroupCongr (hSmap b)).symm).trans
          (Subgroup.equivMapOfInjective _ ι hιinj).symm)
      (isQuasisimple_blockSL b.1 b.2.1 b.2.2)
  have hder : ∃ k, ggDer (ggCentSL ψ E) k ≤ ⨆ b, S b := by
    obtain ⟨k, hk⟩ := exists_derivedSeries_le_goodSL (E := D) (m := d)
    refine ⟨k, ?_⟩
    rw [← Subgroup.map_le_map_iff_of_injective hιinj, map_ggDer, hÑmap]
    calc ggDer ((ggCentSL ψ E).map ι) k ≤ ggDer θ.range k :=
          ggDer_mono (by rw [hC₀θ]; exact Subgroup.map_comap_le _ _) k
      _ = (ggDer ⊤ k).map θ := by rw [map_ggDer, ← MonoidHom.range_eq_map]
      _ = (derivedSeries _ k).map θ := by rw [ggDer_top]
      _ ≤ (goodSL D d).map θ := Subgroup.map_mono hk
  obtain ⟨b, rfl⟩ := exists_eq_map_of_isComponentOf ψ hker (map_ggCentSL_le hEA)
    (normal_map_ggCentSL hker) (commutator_le_map_ggCentSL hker) S hSC hSn hSq hder hK
  have hcardS : Nat.card (S b) = Nat.card (SpecialLinearGroup (Fin (d b.1)) (D b.1)) := by
    rw [← Subgroup.card_map_of_injective hιinj, hSmap, Subgroup.card_map_of_injective hθinj]
    exact (Nat.card_congr (MonoidHom.ofInjective (blockEmbed_injective (E := D) (m := d)
      b.1)).toEquiv).symm
  have hdvd : p ∣ Nat.card (S b) := by
    rw [hcardS]
    exact hpF.trans ((sq_sub_one_dvd_of_algebra (F := F) (D := D b.1)).trans
      (sq_sub_one_dvd_card_SL b.2.1))
  exact dvd_card_map_of_perfect ψ hker (ggCommutator_eq_of_isQuasisimple (hSq b)) hp hdvd

end LayerPDiv

end CFSG.StandardType
