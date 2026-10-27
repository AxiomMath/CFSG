module

public import CFSG.LocalAnalysis.SeitzReduction.TwistedE6PilotHR8Basic
public import CFSG.LocalAnalysis.SeitzReduction.TwistedE6PilotCatU6Assembly
public import CFSG.LocalAnalysis.SeitzReduction.TwistedE6PilotCatOmegaMinus
public import CFSG.LocalAnalysis.SeitzReduction.TwistedE6PilotPositionHolds
public import CFSG.LocalAnalysis.SeitzReduction.TwistedE6PilotLeviAutTorus
import CFSG.LocalAnalysis.SeitzReduction.F4PilotHR8Instances
public import CFSG.LocalAnalysis.SeitzReduction.OmegaPilotHR8Field

public section

set_option linter.unusedSectionVars false

namespace CFSG.SeitzReduction.TwistedE6Pilot

open Subgroup CFSG.Open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.EvenSmallLie
open CFSG.ComponentClassification.CatLeaf (GLS3OddLieAutComponentsInput MonsterInnerInput
  MonsterLocalComponentsInput)
open CFSG.SeitzReduction.UnitaryPilot (NeighbourOvergroupSUm SUmNeighbourAlternative
  SUmNotOddLieInputAt)
open CFSG.SeitzReduction.OmegaPilot (NeighbourOvergroupOmega OmegaNeighbourAlternative
  OmegaCatalogueClausesAt OmegaNotOddLieInputAt)

section Transport

variable {G : Type*} [Group G] {L : Subgroup G} {M : Type*} [Group M]

theorem map_symm_subgroupOf_ne_bot {C A : Subgroup M} (hAC : A ≤ C) (e : L ≃* C)
    (hA : A ≠ ⊥) : ((A.subgroupOf C).map e.symm.toMonoidHom).map L.subtype ≠ ⊥ := by
  intro h
  apply hA
  rw [← Subgroup.card_eq_one, ← card_map_symm_subgroupOf hAC e, h, Subgroup.card_bot]

end Transport

section Tori

variable {k K : Type} [Field k] [Field K] [Algebra k K]

theorem thetaTorus_ne_bot [CharP K 2] [Finite k] (hq : 4 ≤ Nat.card k) :
    E6GraphLevi.thetaTorus (algebraMap k K) ≠ ⊥ := by
  obtain ⟨c, hc⟩ := F4Pilot.exists_three_le_orderOf hq
  intro h
  have hmem := rootDiagUnit_highDiag_mem_thetaTorus (algebraMap k K) c
  rw [h, mem_bot] at hmem
  have h1 : Units.map (algebraMap k K).toMonoidHom c = 1 :=
    EPilot.eq_one_of_commute_pinnedX_highRoot (Or.inl rfl) (ringChar.eq K 2)
      (by rw [show CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley.rootDiagUnit Tag.E6
            (EPilot.highDiag .E6 (Units.map (algebraMap k K).toMonoidHom c)) = 1 from hmem]
          exact Commute.one_left _)
  have hc1 : c = 1 := Units.map_injective (algebraMap k K).injective (by rw [h1, map_one])
  rw [hc1, orderOf_one] at hc
  omega

theorem shortRootTorus_ne_bot [CharP K 2] [Finite k] (hq : 4 ≤ Nat.card k) :
    shortRootTorus (algebraMap k K) ≠ ⊥ := by
  intro h
  have h1 := card_shortRootTorus (algebraMap k K)
  rw [h, Subgroup.card_bot] at h1
  omega

end Tori

section Data

variable {G : Type} [Group G] [Finite G] {L : Subgroup G} {f : ℕ} {k K : Type} [Field k]
  [Field K] [Algebra k K]

theorem neighbour_data_2E6_X (hset : SeitzSetting G L) (hf2 : 2 ≤ f) (hk : Nat.card k = 2 ^ f)
    (hK : Nat.card K = (2 ^ f) ^ 2) {σ : K →+* K} (hσ : ∀ c, σ c = c ^ 2 ^ f)
    (e : L ≃* graphFixedRootGroup TwistTag.E6 K σ) {t : G} (htC : t ∈ centralizer (L : Set G))
    (ht : orderOf t = 2) {X : Subgroup G}
    (hX : X = (((E6GraphLevi.thetaTorus (algebraMap k K)).subgroupOf
      (graphFixedRootGroup TwistTag.E6 K σ)).map e.symm.toMonoidHom).map L.subtype)
    {D : Subgroup G} (hDe : D = (((su6Levi σ).subgroupOf
      (graphFixedRootGroup TwistTag.E6 K σ)).map e.symm.toMonoidHom).map L.subtype) :
    X ≠ ⊥ ∧ centralizer (X : Set G) ≠ ⊤ ∧ D ≤ centralizer (X : Set G) ∧ CFSG.IsQuasisimple D ∧
      center D = ⊥ ∧ LieModel D .PSU 6 2 f := by
  have hf : 1 ≤ f := by omega
  have : Finite k := Nat.finite_of_card_ne_zero (by rw [hk]; positivity)
  have := finite_of_card hK
  have := charP_two_of_card hf hK
  have hq : 4 ≤ Nat.card k := by
    rw [hk]
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ f := Nat.pow_le_pow_right (by norm_num) hf2
  have hXne : X ≠ ⊥ := hX ▸ map_symm_subgroupOf_ne_bot (thetaTorus_le_C0 hf hk hK hσ) e
    (thetaTorus_ne_bot hq)
  obtain ⟨hDs, hDp, hDo⟩ := su6Levi_subgroupOf_facts hf hk hK hσ
  obtain ⟨-, hZD, -⟩ := lemmaA_data_of_simple (G := G) e hDo
  obtain ⟨X', D', hX', hD', -, -, hDXt, -, hlie, -⟩ :=
    exists_neighbour_standard_2E6_X hset hf2 hk hK hσ e htC ht
  subst hX hDe hX' hD'
  exact ⟨hXne, F4Pilot.centralizer_ne_top_of_ne_bot hset.standardSetting.simple
      hset.standardSetting.nonab hXne, hDXt.trans inf_le_left,
    (neighbour_layer_2E6_X hf2 hk hK hσ e rfl rfl).2, hZD, hlie⟩

theorem neighbour_data_2E6_Y (hset : SeitzSetting G L) (hf2 : 2 ≤ f) (hk : Nat.card k = 2 ^ f)
    (hK : Nat.card K = (2 ^ f) ^ 2) {σ : K →+* K} (hσ : ∀ c, σ c = c ^ 2 ^ f)
    (e : L ≃* graphFixedRootGroup TwistTag.E6 K σ) {t : G} (htC : t ∈ centralizer (L : Set G))
    (ht : orderOf t = 2) {X : Subgroup G}
    (hX : X = (((shortRootTorus (algebraMap k K)).subgroupOf
      (graphFixedRootGroup TwistTag.E6 K σ)).map e.symm.toMonoidHom).map L.subtype)
    {D : Subgroup G} (hDe : D = (((omegaMinusLevi σ).subgroupOf
      (graphFixedRootGroup TwistTag.E6 K σ)).map e.symm.toMonoidHom).map L.subtype) :
    X ≠ ⊥ ∧ centralizer (X : Set G) ≠ ⊤ ∧ D ≤ centralizer (X : Set G) ∧ CFSG.IsQuasisimple D ∧
      center D = ⊥ ∧ LieModel D .POmegaMinus 4 2 f := by
  have hf : 1 ≤ f := by omega
  have : Finite k := Nat.finite_of_card_ne_zero (by rw [hk]; positivity)
  have := finite_of_card hK
  have := charP_two_of_card hf hK
  have hq : 4 ≤ Nat.card k := by
    rw [hk]
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ f := Nat.pow_le_pow_right (by norm_num) hf2
  have hσι : ∀ c : k, σ (algebraMap k K c) = algebraMap k K c :=
    E6GraphLevi.fixed_algebraMap (sigma_eq_pow_card hk hσ)
  have hXne : X ≠ ⊥ := hX ▸ map_symm_subgroupOf_ne_bot (shortRootTorus_le_C0 hσι) e
    (shortRootTorus_ne_bot hq)
  obtain ⟨hDs, hDp, hDo⟩ := omegaMinusLevi_subgroupOf_facts hf hK hσ
  obtain ⟨-, hZD, -⟩ := lemmaA_data_of_simple (G := G) e hDo
  obtain ⟨X', D', hX', hD', -, -, hDXt, -, hlie, -⟩ :=
    exists_neighbour_standard_2E6_Y hset hf2 hk hK hσ e htC ht
  subst hX hDe hX' hD'
  exact ⟨hXne, F4Pilot.centralizer_ne_top_of_ne_bot hset.standardSetting.simple
      hset.standardSetting.nonab hXne, hDXt.trans inf_le_left,
    (neighbour_layer_2E6_Y hf2 hk hK hσ e rfl rfl).2, hZD, hlie⟩

end Data

section Clauses

variable {G : Type} [Group G] [Finite G] {L : Subgroup G} {f : ℕ} {k K : Type} [Field k]
  [Field K] [Algebra k K]

theorem neighbour_overgroup_2E6_X_of_clauses (hcat : SUmCatalogueClausesAtF 6 f)
    (hset : SeitzSetting G L) [CharP K 2] (hf2 : 2 ≤ f) (hk : Nat.card k = 2 ^ f)
    (hK : Nat.card K = (2 ^ f) ^ 2) {σ : K →+* K} (hσ : ∀ c, σ c = c ^ 2 ^ f)
    (e : L ≃* graphFixedRootGroup TwistTag.E6 K σ) {t : G} (htC : t ∈ centralizer (L : Set G))
    (ht : orderOf t = 2)
    (hξ : TwistedFusionIn (xiAut σ (apply_apply_eq hK hσ)) (classTU (apply_apply_eq hK hσ)))
    {X : Subgroup G} (hX : X = (((E6GraphLevi.thetaTorus (algebraMap k K)).subgroupOf
      (graphFixedRootGroup TwistTag.E6 K σ)).map e.symm.toMonoidHom).map L.subtype)
    (htX : t ∈ centralizer (X : Set G)) {D : Subgroup G} (hDe : D = (((su6Levi σ).subgroupOf
      (graphFixedRootGroup TwistTag.E6 K σ)).map e.symm.toMonoidHom).map L.subtype) :
    NeighbourOvergroupSUm (QuotientGroup.mk' (oddCore (centralizer (X : Set G))) ⟨t, htX⟩)
        ((D.subgroupOf (centralizer (X : Set G))).map
          (QuotientGroup.mk' (oddCore (centralizer (X : Set G))))) 6 f ∧
      ∀ Lc : Subgroup (centralizer (X : Set G) ⧸ oddCore (centralizer (X : Set G))),
        IsComponent Lc →
        ⁅(D.subgroupOf (centralizer (X : Set G))).map
            (QuotientGroup.mk' (oddCore (centralizer (X : Set G)))), Lc⁆ ≠ ⊥ →
        SUmNeighbourAlternative (QuotientGroup.mk' (oddCore (centralizer (X : Set G))) ⟨t, htX⟩)
          ((D.subgroupOf (centralizer (X : Set G))).map
            (QuotientGroup.mk' (oddCore (centralizer (X : Set G))))) Lc 6 f := by
  obtain ⟨-, hXG, hDX, hDq, hZD, hlie⟩ := neighbour_data_2E6_X hset hf2 hk hK hσ e htC ht hX hDe
  obtain ⟨hcomp, hsyl, hstd⟩ := neighbour_standard_2E6_X hset hf2 hk hK hσ e htC ht hX htX hDe
  have hnn := not_normal_neighbour_2E6_X_holds hset hf2 hk hK hσ e htC ht hξ hX hDe
  exact neighbour_overgroup_sumF (by norm_num) (six_ne_four_one f) hcat
    hset.standardSetting.kProper hXG htX ht hDX hDq
    (LinearPilot.lieModel_quotient_center_of_center_eq_bot hZD hlie)
    (OmegaPilot.odd_card_center_of_center_eq_bot hZD) hcomp hsyl hstd hnn

end Clauses

section ClassY

variable {G : Type} [Group G] [Finite G] {L : Subgroup G} {f : ℕ} {k K : Type} [Field k]
  [Field K] [Algebra k K]

theorem omegaHR8FieldAt_2E6_Y_of_clauses (hcat : OmegaCatalogueClausesAt 4)
    (hset : SeitzSetting G L) [CharP K 2] (hf2 : 2 ≤ f) (hk : Nat.card k = 2 ^ f)
    (hK : Nat.card K = (2 ^ f) ^ 2) {σ : K →+* K} (hσ : ∀ c, σ c = c ^ 2 ^ f)
    (e : L ≃* graphFixedRootGroup TwistTag.E6 K σ) {t : G} (htC : t ∈ centralizer (L : Set G))
    (ht : orderOf t = 2)
    (hξ : TwistedFusionIn (xiAut σ (apply_apply_eq hK hσ)) (classTU (apply_apply_eq hK hσ)))
    (hT : TorusConjY k σ)
    {X : Subgroup G} (hX : X = (((shortRootTorus (algebraMap k K)).subgroupOf
      (graphFixedRootGroup TwistTag.E6 K σ)).map e.symm.toMonoidHom).map L.subtype)
    {D : Subgroup G} (hDe : D = (((omegaMinusLevi σ).subgroupOf
      (graphFixedRootGroup TwistTag.E6 K σ)).map e.symm.toMonoidHom).map L.subtype) :
    OmegaPilot.OmegaHR8FieldAt t 4 f .POmegaMinus X D := by
  have hXL : X ≤ L := hX ▸ map_subtype_le _
  have htX : t ∈ centralizer (X : Set G) := centralizer_le hXL htC
  obtain ⟨hXne, -, hDX, hDq, hZD, hlie⟩ :=
    neighbour_data_2E6_Y hset hf2 hk hK hσ e htC ht hX hDe
  obtain ⟨hcomp, hsyl, hstd⟩ := neighbour_standard_2E6_Y hset hf2 hk hK hσ e htC ht hX htX hDe
  have hnn := not_normal_neighbour_2E6_Y_holds hset hf2 hk hK hσ e htC ht hξ hT hX hDe
  exact OmegaPilot.omegaHR8FieldAt_of_seitzSetting hset (four_ne_four_one hf2) hcat
    (OmegaPilot.omegaEvenTypeDetAt 4) hXne htX ht hDX hDq hZD (Or.inr rfl) hlie hcomp hsyl hstd hnn

end ClassY

section LeafInputs

variable {G : Type} [Group G] [Finite G] {L : Subgroup G} {f : ℕ} {k K : Type} [Field k]
  [Field K] [Algebra k K]

theorem neighbour_overgroup_2E6_X (hGLS : GLS3OddLieAutComponentsInput)
    (hXodd : SUmNotOddLieInputAt 6) (hMinn : MonsterInnerInput)
    (hMcomp : MonsterLocalComponentsInput) (hset : SeitzSetting G L) [CharP K 2] (hf2 : 2 ≤ f)
    (hk : Nat.card k = 2 ^ f) (hK : Nat.card K = (2 ^ f) ^ 2) {σ : K →+* K}
    (hσ : ∀ c, σ c = c ^ 2 ^ f) (e : L ≃* graphFixedRootGroup TwistTag.E6 K σ) {t : G}
    (htC : t ∈ centralizer (L : Set G)) (ht : orderOf t = 2)
    (hξ : TwistedFusionIn (xiAut σ (apply_apply_eq hK hσ)) (classTU (apply_apply_eq hK hσ)))
    {X : Subgroup G} (hX : X = (((E6GraphLevi.thetaTorus (algebraMap k K)).subgroupOf
      (graphFixedRootGroup TwistTag.E6 K σ)).map e.symm.toMonoidHom).map L.subtype)
    (htX : t ∈ centralizer (X : Set G)) {D : Subgroup G} (hDe : D = (((su6Levi σ).subgroupOf
      (graphFixedRootGroup TwistTag.E6 K σ)).map e.symm.toMonoidHom).map L.subtype) :
    NeighbourOvergroupSUm (QuotientGroup.mk' (oddCore (centralizer (X : Set G))) ⟨t, htX⟩)
        ((D.subgroupOf (centralizer (X : Set G))).map
          (QuotientGroup.mk' (oddCore (centralizer (X : Set G))))) 6 f ∧
      ∀ Lc : Subgroup (centralizer (X : Set G) ⧸ oddCore (centralizer (X : Set G))),
        IsComponent Lc →
        ⁅(D.subgroupOf (centralizer (X : Set G))).map
            (QuotientGroup.mk' (oddCore (centralizer (X : Set G)))), Lc⁆ ≠ ⊥ →
        SUmNeighbourAlternative (QuotientGroup.mk' (oddCore (centralizer (X : Set G))) ⟨t, htX⟩)
          ((D.subgroupOf (centralizer (X : Set G))).map
            (QuotientGroup.mk' (oddCore (centralizer (X : Set G))))) Lc 6 f :=
  neighbour_overgroup_2E6_X_of_clauses
    (sumCatalogueClausesAtF_six_of_leafInputs hGLS hXodd hMinn hMcomp hf2) hset hf2 hk hK hσ e
    htC ht hξ hX htX hDe

theorem omegaHR8FieldAt_2E6_Y (hGLS : GLS3OddLieAutComponentsInput)
    (hXodd : OmegaNotOddLieInputAt 4) (hMinn : MonsterInnerInput)
    (hMcomp : MonsterLocalComponentsInput) (hset : SeitzSetting G L) [CharP K 2] (hf2 : 2 ≤ f)
    (hk : Nat.card k = 2 ^ f) (hK : Nat.card K = (2 ^ f) ^ 2) {σ : K →+* K}
    (hσ : ∀ c, σ c = c ^ 2 ^ f) (e : L ≃* graphFixedRootGroup TwistTag.E6 K σ) {t : G}
    (htC : t ∈ centralizer (L : Set G)) (ht : orderOf t = 2)
    (hξ : TwistedFusionIn (xiAut σ (apply_apply_eq hK hσ)) (classTU (apply_apply_eq hK hσ)))
    (hT : TorusConjY k σ)
    {X : Subgroup G} (hX : X = (((shortRootTorus (algebraMap k K)).subgroupOf
      (graphFixedRootGroup TwistTag.E6 K σ)).map e.symm.toMonoidHom).map L.subtype)
    {D : Subgroup G} (hDe : D = (((omegaMinusLevi σ).subgroupOf
      (graphFixedRootGroup TwistTag.E6 K σ)).map e.symm.toMonoidHom).map L.subtype) :
    OmegaPilot.OmegaHR8FieldAt t 4 f .POmegaMinus X D :=
  omegaHR8FieldAt_2E6_Y_of_clauses
    (omegaCatalogueClausesAt_four_of_leafInputs hGLS hXodd hMinn hMcomp) hset hf2 hk hK hσ e htC
    ht hξ hT hX hDe

end LeafInputs

end CFSG.SeitzReduction.TwistedE6Pilot
