module

public import CFSG.LocalAnalysis.SeitzReduction.TwistedE6PilotEnd
public import CFSG.LocalAnalysis.SeitzReduction.CrossCharCert
public import CFSG.LocalAnalysis.SeitzReduction.TwistedE6PilotQ2Neighbour

public section

set_option linter.unusedSectionVars false

namespace CFSG.SeitzReduction.TwistedE6Pilot

open Subgroup CFSG.Open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.EvenSmallLie CFSG.LieType.Chevalley.E6GraphLevi
open CFSG.ComponentClassification.CatLeaf (GLS3OddLieAutComponentsInput MonsterInnerInput
  MonsterLocalComponentsInput)
open CFSG.SeitzReduction.UnitaryPilot (SUmNotOddLieInputAt NeighbourOvergroupSUm
  SUmNeighbourAlternative SUmOvergroup)
open CFSG.SeitzReduction.OmegaPilot (OmegaNotOddLieInputAt)

theorem sumCatalogueClausesAtF_six_one (hGLS : GLS3OddLieAutComponentsInput)
    (hres : CatSUmSporadicAtF 6 1) : SUmCatalogueClausesAtF 6 1 :=
  ⟨UnitaryPilot.catSUmAlternating, UnitaryPilot.catSUmEvenInner,
    UnitaryPilot.catSUmEvenOuterAt (by norm_num),
    UnitaryPilot.catSUmOddLieAt_of_inputs hGLS (by norm_num) (CrossChar.sUmNotOddLieInputAt 6),
    hres, UnitaryPilot.catSUmCovers⟩

@[expose] def TwistedE6TwoPositionInput : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (L : Subgroup G) (k K : Type) [Field k] [Field K]
    [Algebra k K], SeitzSetting G L → Nat.card k = 2 ^ 1 → Nat.card K = (2 ^ 1) ^ 2 →
    ∀ (σ : K →+* K), (∀ c, σ c = c ^ 2 ^ 1) →
    ∀ (e : L ≃* graphFixedRootGroup TwistTag.E6 K σ) (t : G), t ∈ centralizer (L : Set G) →
      orderOf t = 2 →
      ∀ A : Subgroup (ModGL TwistTag.E6.tag K), A ≤ thetaRankOneGroup (algebraMap k K) →
        Nat.card A = 2 ^ 1 + 1 → IsCyclic A →
        ¬ (((modelToG e (su6Levi σ)).subgroupOf (centralizer (modelToG e A : Set G))).map
          (QuotientGroup.mk' (oddCore (centralizer (modelToG e A : Set G))))).Normal

@[expose] def TwistedE6TwoRowsInput : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (L : Subgroup G) (k K : Type) [Field k] [Field K]
    [Algebra k K], SeitzSetting G L → Nat.card k = 2 ^ 1 → Nat.card K = (2 ^ 1) ^ 2 →
    ∀ (σ : K →+* K), (∀ c, σ c = c ^ 2 ^ 1) →
    ∀ (e : L ≃* graphFixedRootGroup TwistTag.E6 K σ) (t : G), t ∈ centralizer (L : Set G) →
      orderOf t = 2 →
      ∀ A : Subgroup (ModGL TwistTag.E6.tag K), A ≤ thetaRankOneGroup (algebraMap k K) →
        Nat.card A = 2 ^ 1 + 1 → IsCyclic A →
        ∀ htX : t ∈ centralizer (modelToG e A : Set G),
          NeighbourOvergroupSUm
            (QuotientGroup.mk' (oddCore (centralizer (modelToG e A : Set G))) ⟨t, htX⟩)
            (((modelToG e (su6Levi σ)).subgroupOf (centralizer (modelToG e A : Set G))).map
              (QuotientGroup.mk' (oddCore (centralizer (modelToG e A : Set G))))) 6 1 → False

@[expose] def TwistedE6TwoFieldRowInput : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (L : Subgroup G) (k K : Type) [Field k] [Field K]
    [Algebra k K], SeitzSetting G L → Nat.card k = 2 ^ 1 → Nat.card K = (2 ^ 1) ^ 2 →
    ∀ (σ : K →+* K), (∀ c, σ c = c ^ 2 ^ 1) →
    ∀ (e : L ≃* graphFixedRootGroup TwistTag.E6 K σ) (t : G), t ∈ centralizer (L : Set G) →
      orderOf t = 2 →
      ∀ A : Subgroup (ModGL TwistTag.E6.tag K), A ≤ thetaRankOneGroup (algebraMap k K) →
        Nat.card A = 2 ^ 1 + 1 → IsCyclic A →
        ∀ htX : t ∈ centralizer (modelToG e A : Set G),
        ∀ Kc : Subgroup (centralizer (modelToG e A : Set G) ⧸
          oddCore (centralizer (modelToG e A : Set G))), IsComponent Kc →
        Kc.map (MulAut.conj (QuotientGroup.mk' (oddCore (centralizer (modelToG e A : Set G)))
          ⟨t, htX⟩)).toMonoidHom = Kc →
        ((modelToG e (su6Levi σ)).subgroupOf (centralizer (modelToG e A : Set G))).map
          (QuotientGroup.mk' (oddCore (centralizer (modelToG e A : Set G)))) < Kc →
        QuotientGroup.mk' (oddCore (centralizer (modelToG e A : Set G))) ⟨t, htX⟩ ∉ Kc →
        ∀ hsN : QuotientGroup.mk' (oddCore (centralizer (modelToG e A : Set G))) ⟨t, htX⟩ ∈
          normalizer (Kc : Set (centralizer (modelToG e A : Set G) ⧸
            oddCore (centralizer (modelToG e A : Set G)))),
        SUmOvergroup Kc (Kc.normalizerMonoidHom ⟨_, hsN⟩) 6 1 → False

@[expose] def TwistedE6TwoSwapRowInput : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (L : Subgroup G) (k K : Type) [Field k] [Field K]
    [Algebra k K], SeitzSetting G L → Nat.card k = 2 ^ 1 → Nat.card K = (2 ^ 1) ^ 2 →
    ∀ (σ : K →+* K), (∀ c, σ c = c ^ 2 ^ 1) →
    ∀ (e : L ≃* graphFixedRootGroup TwistTag.E6 K σ) (t : G), t ∈ centralizer (L : Set G) →
      orderOf t = 2 →
      ∀ A : Subgroup (ModGL TwistTag.E6.tag K), A ≤ thetaRankOneGroup (algebraMap k K) →
        Nat.card A = 2 ^ 1 + 1 → IsCyclic A →
        ∀ htX : t ∈ centralizer (modelToG e A : Set G),
        ∀ Kc : Subgroup (centralizer (modelToG e A : Set G) ⧸
          oddCore (centralizer (modelToG e A : Set G))), IsComponent Kc →
        ((modelToG e (su6Levi σ)).subgroupOf (centralizer (modelToG e A : Set G))).map
            (QuotientGroup.mk' (oddCore (centralizer (modelToG e A : Set G)))) ≤
          Kc ⊔ Kc.map (MulAut.conj (QuotientGroup.mk'
            (oddCore (centralizer (modelToG e A : Set G))) ⟨t, htX⟩)).toMonoidHom →
        Kc.map (MulAut.conj (QuotientGroup.mk' (oddCore (centralizer (modelToG e A : Set G)))
          ⟨t, htX⟩)).toMonoidHom ≠ Kc →
        ⁅Kc, Kc.map (MulAut.conj (QuotientGroup.mk'
          (oddCore (centralizer (modelToG e A : Set G))) ⟨t, htX⟩)).toMonoidHom⁆ = ⊥ →
        center Kc = ⊥ →
        Nonempty (Kc ≃* ((modelToG e (su6Levi σ)).subgroupOf
          (centralizer (modelToG e A : Set G))).map
            (QuotientGroup.mk' (oddCore (centralizer (modelToG e A : Set G))))) → False

theorem twistedE6TwoRowsInput_of_rows (hF : TwistedE6TwoFieldRowInput)
    (hS : TwistedE6TwoSwapRowInput) : TwistedE6TwoRowsInput := by
  intro G _ _ L k K _ _ _ hset hk hK σ hσ e t htC ht A hAJ hA hcyc htX hNO
  obtain ⟨Kc, hKc, hDKK, hcase⟩ := hNO
  rcases hcase with ⟨hKt, hDK, htK, hsN, hov⟩ | ⟨hKt, hcomm, hZ, hφ⟩
  · exact hF G L k K hset hk hK σ hσ e t htC ht A hAJ hA hcyc htX Kc hKc hKt hDK htK hsN hov
  · exact hS G L k K hset hk hK σ hσ e t htC ht A hAJ hA hcyc htX Kc hKc hDKK hKt hcomm hZ hφ

section HR8

variable {G : Type} [Group G] [Finite G] {L : Subgroup G} {k K : Type} [Field k] [Field K]
  [Algebra k K]

theorem neighbour_data_2E6_nonsplit_two (hset : SeitzSetting G L) (hk : Nat.card k = 2 ^ 1)
    (hK : Nat.card K = (2 ^ 1) ^ 2) {σ : K →+* K} (hσ : ∀ c, σ c = c ^ 2 ^ 1)
    (e : L ≃* graphFixedRootGroup TwistTag.E6 K σ) {A : Subgroup (ModGL TwistTag.E6.tag K)}
    (hAJ : A ≤ thetaRankOneGroup (algebraMap k K)) (hA : Nat.card A = 2 ^ 1 + 1)
    (hcyc : IsCyclic A) :
    modelToG e A ≠ ⊥ ∧ centralizer (modelToG e A : Set G) ≠ ⊤ ∧
      modelToG e (su6Levi σ) ≤ centralizer (modelToG e A : Set G) ∧
      CFSG.IsQuasisimple (modelToG e (su6Levi σ)) ∧ center (modelToG e (su6Levi σ)) = ⊥ ∧
      LieModel (modelToG e (su6Levi σ)) .PSU 6 2 1 := by
  have hf : 1 ≤ 1 := le_rfl
  obtain ⟨-, -, hXD, hAC⟩ := centralizer_nonsplit_twistedE6 hf hk hK hσ hAJ hA hcyc
  have hAne : A ≠ ⊥ := by
    intro h
    rw [h, Subgroup.card_bot] at hA
    norm_num at hA
  have hXne : modelToG e A ≠ ⊥ := map_symm_subgroupOf_ne_bot hAC e hAne
  obtain ⟨hDs, hDp, hDo⟩ := su6Levi_subgroupOf_facts hf hk hK hσ
  obtain ⟨-, hZD, -⟩ := lemmaA_data_of_simple (G := G) e hDo
  have hlie : LieModel (modelToG e (su6Levi σ)) .PSU 6 2 1 := lieModel_of_mulEquiv
    ((subgroupOfEquivOfLe (su6Levi_le_graphFixedRootGroup σ)).symm.trans
      ((((su6Levi σ).subgroupOf (graphFixedRootGroup TwistTag.E6 K σ)).equivMapOfInjective
        e.symm.toMonoidHom e.symm.injective).trans
        ((((su6Levi σ).subgroupOf (graphFixedRootGroup TwistTag.E6 K σ)).map
          e.symm.toMonoidHom).equivMapOfInjective L.subtype L.subtype_injective)))
    (lieModel_su6Levi hf hk hK hσ)
  exact ⟨hXne, F4Pilot.centralizer_ne_top_of_ne_bot hset.standardSetting.simple
      hset.standardSetting.nonab hXne,
    le_centralizer_iff.1 (F4Pilot.map_le_centralizer_map _ (F4Pilot.map_le_centralizer_map _
      (subgroupOf_le_centralizer_subgroupOf hXD))),
    (neighbour_layer_2E6_nonsplit_two hk hK hσ e hAJ hA hcyc rfl rfl).2, hZD, hlie⟩

theorem neighbour_overgroup_2E6_nonsplit_two (hcat : SUmCatalogueClausesAtF 6 1)
    (hpos : TwistedE6TwoPositionInput) (hset : SeitzSetting G L) (hk : Nat.card k = 2 ^ 1)
    (hK : Nat.card K = (2 ^ 1) ^ 2) {σ : K →+* K} (hσ : ∀ c, σ c = c ^ 2 ^ 1)
    (e : L ≃* graphFixedRootGroup TwistTag.E6 K σ) {t : G} (htC : t ∈ centralizer (L : Set G))
    (ht : orderOf t = 2) {A : Subgroup (ModGL TwistTag.E6.tag K)}
    (hAJ : A ≤ thetaRankOneGroup (algebraMap k K)) (hA : Nat.card A = 2 ^ 1 + 1)
    (hcyc : IsCyclic A) (htX : t ∈ centralizer (modelToG e A : Set G)) :
    NeighbourOvergroupSUm
      (QuotientGroup.mk' (oddCore (centralizer (modelToG e A : Set G))) ⟨t, htX⟩)
      (((modelToG e (su6Levi σ)).subgroupOf (centralizer (modelToG e A : Set G))).map
        (QuotientGroup.mk' (oddCore (centralizer (modelToG e A : Set G))))) 6 1 := by
  obtain ⟨-, hXG, hDX, hDq, hZD, hlie⟩ :=
    neighbour_data_2E6_nonsplit_two hset hk hK hσ e hAJ hA hcyc
  obtain ⟨hcomp, hsyl, hstd⟩ :=
    neighbour_standard_2E6_nonsplit_two hset hk hK hσ e htC ht hAJ hA hcyc rfl htX rfl
  have hnn := hpos G L k K hset hk hK σ hσ e t htC ht A hAJ hA hcyc
  exact (neighbour_overgroup_sumF (by norm_num) (six_ne_four_one 1) hcat
    hset.standardSetting.kProper hXG htX ht hDX hDq
    (LinearPilot.lieModel_quotient_center_of_center_eq_bot hZD hlie)
    (OmegaPilot.odd_card_center_of_center_eq_bot hZD) hcomp hsyl hstd hnn).1

end HR8

section Reduction

variable {G : Type} [Group G] [Finite G] {L : Subgroup G}

theorem false_of_seitzSetting_twistedE6_two_of_mulEquiv (hcat : SUmCatalogueClausesAtF 6 1)
    (hpos : TwistedE6TwoPositionInput) (hrows : TwistedE6TwoRowsInput)
    (hset : SeitzSetting G L) {k K : Type} [Field k] [Field K] [Algebra k K]
    (hk : Nat.card k = 2 ^ 1) (hK : Nat.card K = (2 ^ 1) ^ 2) {σ : K →+* K}
    (hσ : ∀ c, σ c = c ^ 2 ^ 1) (e : L ≃* graphFixedRootGroup TwistTag.E6 K σ) : False := by
  obtain ⟨t, htC, ht⟩ := F4Pilot.exists_orderOf_eq_two_mem_centralizer hset.standardSetting
  obtain ⟨A, hAJ, hcyc, hA⟩ := exists_nonsplit_le_thetaRankOneGroup (f := 1) le_rfl hk hK
  have htX : t ∈ centralizer (modelToG e A : Set G) := centralizer_le (map_subtype_le _) htC
  exact hrows G L k K hset hk hK σ hσ e t htC ht A hAJ hA hcyc htX
    (neighbour_overgroup_2E6_nonsplit_two hcat hpos hset hk hK hσ e htC ht hAJ hA hcyc htX)

theorem false_of_twistedE6_two_of_inputs (hGLS : GLS3OddLieAutComponentsInput)
    (hres : CatSUmSporadicAtF 6 1) (hpos : TwistedE6TwoPositionInput)
    (hrows : TwistedE6TwoRowsInput) (hset : SeitzSetting G L)
    (hL : LieModel L .twistedE6 0 2 1) : False := by
  obtain ⟨hf, K, _, _, σ, hK, hσ, ⟨e⟩⟩ := exists_mulEquiv_graphFixedRootGroup_of_lieModel hL
  obtain ⟨σE, hσE⟩ := exists_ringEquiv_toRingHom_eq σ
  exact false_of_seitzSetting_twistedE6_two_of_mulEquiv (k := LieType.Chevalley.fixSubfield σE)
    (sumCatalogueClausesAtF_six_one hGLS hres) hpos hrows hset
    (natCard_fixSubfield_of_card_sq hf hK hσ hσE) hK hσ e

end Reduction

end CFSG.SeitzReduction.TwistedE6Pilot
