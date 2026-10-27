module

public import CFSG.LocalAnalysis.SeitzReduction.TwistedE6PilotPositionBasic
public import CFSG.LocalAnalysis.SeitzReduction.TwistedE6PilotBLift
public import CFSG.LocalAnalysis.SeitzReduction.UnitaryPilotSetup
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalPointSchreier
public import CFSG.LocalAnalysis.ComponentClassification.EvenOrthSelector
public import CFSG.LocalAnalysis.SeitzReduction.TwistedE6PilotInnerAction
public import CFSG.LocalAnalysis.SeitzReduction.TwistedE6PilotRouteBBasic

public section

set_option linter.unusedSectionVars false

namespace CFSG.SeitzReduction.TwistedE6Pilot

open Subgroup CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.EvenSmallLie
open CFSG.ComponentClassification.OuterAutomorphisms
open CFSG.ComponentClassification
open CFSG.Quasithin (perfectCore perfectCore_le)

variable {G : Type} [Group G] [Finite G] {L : Subgroup G} {f : ℕ} {k K : Type} [Field k]
  [Field K] [Algebra k K]

section LemmaAData

noncomputable def mapSymmEquiv {C : Type*} [Group C] (e : L ≃* C) (DC : Subgroup C) :
    DC ≃* ((DC.map e.symm.toMonoidHom).map L.subtype : Subgroup G) :=
  (DC.equivMapOfInjective _ e.symm.injective).trans
    ((DC.map e.symm.toMonoidHom).equivMapOfInjective _ L.subtype_injective)

theorem lemmaA_data_of_simple {C : Type*} [Group C] (e : L ≃* C) {DC : Subgroup C}
    [IsSimpleGroup DC] [Group.IsPerfect DC] (hOut : Group.IsSolvable (Outer DC)) :
    CFSG.Open.IsQuasisimple ((DC.map e.symm.toMonoidHom).map L.subtype) ∧
      center ((DC.map e.symm.toMonoidHom).map L.subtype) = ⊥ ∧
      Group.IsSolvable (Outer ((DC.map e.symm.toMonoidHom).map L.subtype)) := by
  have eD := mapSymmEquiv (G := G) e DC
  have hZ : center DC = ⊥ := center_eq_bot_of_isSimpleGroup_of_isPerfect
  have hQ : IsSimpleGroup (DC ⧸ center DC) :=
    ((QuotientGroup.quotientMulEquivOfEq hZ).trans QuotientGroup.quotientBot).isSimpleGroup
  refine ⟨F4Pilot.isQuasisimple_open_of_mulEquiv eD ⟨Group.IsPerfect.commutator_eq_top, hQ⟩,
    F4Pilot.center_eq_bot_congr eD hZ,
    (CFSG.LocalAnalysis.ComponentInitial.outer_isomorphism eD).2.1 hOut⟩

theorem su6Levi_subgroupOf_facts (hf : 1 ≤ f) (hk : Nat.card k = 2 ^ f)
    (hK : Nat.card K = (2 ^ f) ^ 2) {σ : K →+* K} (hσ : ∀ c, σ c = c ^ 2 ^ f) :
    IsSimpleGroup ((su6Levi σ).subgroupOf (graphFixedRootGroup TwistTag.E6 K σ)) ∧
      Group.IsPerfect ((su6Levi σ).subgroupOf (graphFixedRootGroup TwistTag.E6 K σ)) ∧
      Group.IsSolvable (Outer ((su6Levi σ).subgroupOf (graphFixedRootGroup TwistTag.E6 K σ))) := by
  have eD := (subgroupOfEquivOfLe (su6Levi_le_graphFixedRootGroup σ)).symm
  have := isSimpleGroup_su6Levi hf hk hK hσ
  have := isPerfect_su6Levi hf hk hK hσ
  exact ⟨eD.symm.isSimpleGroup, Group.IsPerfect.ofSurjective (f := eD.toMonoidHom) eD.surjective,
    UnitaryPilot.isSolvable_outer_of_lieModel (lieModel_su6Levi_subgroupOf hf hk hK hσ)⟩

theorem omegaMinusLevi_subgroupOf_facts (hf : 1 ≤ f) (hK : Nat.card K = (2 ^ f) ^ 2)
    {σ : K →+* K} (hσ : ∀ c, σ c = c ^ 2 ^ f) :
    IsSimpleGroup ((omegaMinusLevi σ).subgroupOf (graphFixedRootGroup TwistTag.E6 K σ)) ∧
      Group.IsPerfect ((omegaMinusLevi σ).subgroupOf (graphFixedRootGroup TwistTag.E6 K σ)) ∧
      Group.IsSolvable
        (Outer ((omegaMinusLevi σ).subgroupOf (graphFixedRootGroup TwistTag.E6 K σ))) := by
  have eD := (subgroupOfEquivOfLe (omegaMinusLevi_le_graphFixedRootGroup σ)).symm
  have := isSimpleGroup_omegaMinusLevi hf hK hσ
  have := isPerfect_omegaMinusLevi hf hK hσ
  have hLie : LieModel ((omegaMinusLevi σ).subgroupOf (graphFixedRootGroup TwistTag.E6 K σ))
      .POmegaMinus 4 2 f :=
    CFSG.LieType.CurtisTits.lieModel_of_mulEquiv eD (lieModel_omegaMinusLevi hf hK hσ)
  exact ⟨eD.symm.isSimpleGroup, Group.IsPerfect.ofSurjective (f := eD.toMonoidHom) eD.surjective,
    (CatalogueBOrthogonalPointSchreier.orthogonal_geometry_classical_model_Schreier
      .POmegaMinus (Or.inr (Or.inr rfl))
      (CFSG.ComponentClassification.EvenOrthSelector.statedModel_of_lieModel (by decide)
        hLie)).2.2⟩

end LemmaAData

section X

theorem not_normal_neighbour_2E6_X_of_fusion (hset : StandardSetting G L) [CharP K 2]
    (hf2 : 2 ≤ f) (hk : Nat.card k = 2 ^ f) (hK : Nat.card K = (2 ^ f) ^ 2) {σ : K →+* K}
    (hσ : ∀ c, σ c = c ^ 2 ^ f) (e : L ≃* graphFixedRootGroup TwistTag.E6 K σ) {t : G}
    (ht : orderOf t = 2) (hKt : centralizer (L : Set G) ⊓ centralizer ({t} : Set G) = zpowers t)
    (hfus : ∃ (κ : Fin 2) (h : G), h⁻¹ * t * h = t * (e.symm (repXC (apply_apply_eq hK hσ) κ) : G))
    (hF5 : LeviAutConj (leviX σ) (thetaJ k σ))
    {X : Subgroup G} (hXodd : Odd (Nat.card X))
    (hXJ : X ≤ ((thetaJ k σ).map e.symm.toMonoidHom).map L.subtype)
    {D : Subgroup G} (hDe : D = (((su6Levi σ).subgroupOf
      (graphFixedRootGroup TwistTag.E6 K σ)).map e.symm.toMonoidHom).map L.subtype)
    (hsyl : ∀ U : Subgroup (centralizer (X : Set G) ⧸ oddCore (centralizer (X : Set G))),
      IsPGroup 2 U →
      U ≤ centralizer ((D.subgroupOf (centralizer (X : Set G))).map
          (QuotientGroup.mk' (oddCore (centralizer (X : Set G)))) :
        Set (centralizer (X : Set G) ⧸ oddCore (centralizer (X : Set G)))) →
      Nat.card U ≤ 2) :
    ¬ ((D.subgroupOf (centralizer (X : Set G))).map
        (QuotientGroup.mk' (oddCore (centralizer (X : Set G))))).Normal := by
  subst hDe
  have hf : 1 ≤ f := by omega
  have := finite_of_card hK
  have : Finite (ModGL TwistTag.E6.tag K) := finite_modGL
  have htC := EPilot.mem_centralizer_of_inf_centralizer_eq_zpowers hKt
  obtain ⟨hOut, -⟩ := outer_solvable_and_center_eq_bot_twistedE6 hK σ e
  obtain ⟨κ, h, hh⟩ := hfus
  have hinner := exists_inner_repXC_twistedE6 hset hf2 hk hK hσ e ht hKt hh
  have hord : orderOf (repXC (apply_apply_eq hK hσ) κ) = 2 := by
    rw [← Subgroup.orderOf_coe]
    exact orderOf_repX κ
  have hne : h⁻¹ * t * h ≠ t := hh ▸ mul_ne_self_of_ne_one (coe_symm_ne_one_of_orderOf e hord)
  choose Q hQ using exists_isCoreLeviDecomp_repXC (k := k) hf hk hK hσ
  obtain ⟨hDs, hDp, hDo⟩ := su6Levi_subgroupOf_facts hf hk hK hσ
  obtain ⟨hDq, hZD, hOutD⟩ := lemmaA_data_of_simple (G := G) e hDo
  have hXL : X ≤ L := hXJ.trans (map_subtype_le _)
  have htX : t ∈ centralizer (X : Set G) := centralizer_le hXL htC
  have hDJ : (su6Levi σ).subgroupOf (graphFixedRootGroup TwistTag.E6 K σ) ≤
      centralizer (thetaJ k σ : Set (graphFixedRootGroup TwistTag.E6 K σ)) :=
    (centralizer_thetaJ hf2 hk hK hσ).ge
  have hDX := (F4Pilot.map_le_centralizer_map L.subtype
    (F4Pilot.map_le_centralizer_map e.symm.toMonoidHom hDJ)).trans (centralizer_le hXJ)
  exact not_normal_map_oddCore_of_inner_of_classes hset hOut e ht hKt
    (repXC (apply_apply_eq hK hσ)) (k := κ) (Or.inr hh) hne hinner Q (leviX σ)
    (fun κ => (hQ κ).1) (fun κ => (hQ κ).2.1) (fun κ => (hQ κ).2.2.1) (fun κ => (hQ κ).2.2.2.1)
    (fun κ => (hQ κ).2.2.2.2) (classPredicate_repXC hf hk hK hσ hQ κ)
    (thetaJ_le_leviX hf hk hK hσ) (mem_subgroupOf.2 (repX_mem_su6Levi (apply_apply_eq hK hσ) κ))
    hXodd hXJ (fun κ' ι X'' hX'' _ => step7_X hf2 hk hK hσ hF5 κ κ' ι X'' hX'') htX hDX hDq hZD
    hOutD hsyl

theorem not_normal_neighbour_2E6_X_of_inputs (hset : StandardSetting G L) [CharP K 2]
    (hf2 : 2 ≤ f) (hk : Nat.card k = 2 ^ f) (hK : Nat.card K = (2 ^ f) ^ 2) {σ : K →+* K}
    (hσ : ∀ c, σ c = c ^ 2 ^ f) (e : L ≃* graphFixedRootGroup TwistTag.E6 K σ) {t : G}
    (ht : orderOf t = 2) (hKt : centralizer (L : Set G) ⊓ centralizer ({t} : Set G) = zpowers t)
    (hξ : TwistedFusionIn (xiAut σ (apply_apply_eq hK hσ)) (classTU (apply_apply_eq hK hσ)))
    (hF5 : LeviAutConj (leviX σ) (thetaJ k σ))
    {X : Subgroup G} (hXodd : Odd (Nat.card X))
    (hXJ : X ≤ ((thetaJ k σ).map e.symm.toMonoidHom).map L.subtype)
    {D : Subgroup G} (hDe : D = (((su6Levi σ).subgroupOf
      (graphFixedRootGroup TwistTag.E6 K σ)).map e.symm.toMonoidHom).map L.subtype)
    (hsyl : ∀ U : Subgroup (centralizer (X : Set G) ⧸ oddCore (centralizer (X : Set G))),
      IsPGroup 2 U →
      U ≤ centralizer ((D.subgroupOf (centralizer (X : Set G))).map
          (QuotientGroup.mk' (oddCore (centralizer (X : Set G)))) :
        Set (centralizer (X : Set G) ⧸ oddCore (centralizer (X : Set G)))) →
      Nat.card U ≤ 2) :
    ¬ ((D.subgroupOf (centralizer (X : Set G))).map
        (QuotientGroup.mk' (oddCore (centralizer (X : Set G))))).Normal :=
  not_normal_neighbour_2E6_X_of_fusion hset hf2 hk hK hσ e ht hKt
    (exists_conj_eq_mul_repXC_twistedE6 hset (by omega) hk hK σ hσ e
      (exists_perfect_le_of_mulEquiv_twistedE6 (k := k) hf2 hk hK hσ e) hξ ht hKt)
    hF5 hXodd hXJ hDe hsyl

end X

section Y

theorem odd_card_shortRootTorus (hf : 1 ≤ f) (hk : Nat.card k = 2 ^ f) :
    Odd (Nat.card (shortRootTorus (algebraMap k K))) := by
  have : Finite k := Nat.finite_of_card_ne_zero (by rw [hk]; positivity)
  have hodd : Odd (Nat.card kˣ) := by
    rw [Nat.card_units, hk]
    have h2 : 2 ∣ 2 ^ f := dvd_pow_self 2 (by omega)
    have hpos : 1 ≤ 2 ^ f := Nat.one_le_two_pow
    obtain ⟨m, hm⟩ := h2
    rw [Nat.odd_iff]
    omega
  exact hodd.of_dvd_nat (Subgroup.card_range_dvd _)

theorem card_map_symm_w1C (hf : 1 ≤ f) (hk : Nat.card k = 2 ^ f) {σ : K →+* K}
    (hσ : ∀ c, σ c = c ^ 2 ^ f) (e : L ≃* graphFixedRootGroup TwistTag.E6 K σ) :
    Nat.card (((w1C k σ).map e.symm.toMonoidHom).map L.subtype) = Nat.card (w1C k σ) ∧
      Odd (Nat.card (w1C k σ)) := by
  have : Finite k := Nat.finite_of_card_ne_zero (by rw [hk]; positivity)
  have hσι : ∀ c : k, σ (algebraMap k K c) = algebraMap k K c :=
    E6GraphLevi.fixed_algebraMap (sigma_eq_pow_card hk hσ)
  refine ⟨by rw [card_map_of_injective L.subtype_injective,
    card_map_of_injective e.symm.injective], ?_⟩
  rw [w1C, Nat.card_congr (subgroupOfEquivOfLe (shortRootTorus_le_C0 hσι)).toEquiv]
  exact odd_card_shortRootTorus hf hk

theorem not_normal_neighbour_2E6_Y_of_fusion (hset : StandardSetting G L) [CharP K 2]
    (hf2 : 2 ≤ f) (hk : Nat.card k = 2 ^ f) (hK : Nat.card K = (2 ^ f) ^ 2) {σ : K →+* K}
    (hσ : ∀ c, σ c = c ^ 2 ^ f) (e : L ≃* graphFixedRootGroup TwistTag.E6 K σ) {t : G}
    (ht : orderOf t = 2) (hKt : centralizer (L : Set G) ⊓ centralizer ({t} : Set G) = zpowers t)
    (hfus : ∃ (κ : Fin 2) (h : G), h⁻¹ * t * h = t * (e.symm (repYC (apply_apply_eq hK hσ) κ) : G))
    (hF5 : LeviAutConj (leviY σ) (shortJ k σ)) (hT : TorusConjY k σ)
    {X : Subgroup G} (hX : X = ((w1C k σ).map e.symm.toMonoidHom).map L.subtype)
    {D : Subgroup G} (hDe : D = (((omegaMinusLevi σ).subgroupOf
      (graphFixedRootGroup TwistTag.E6 K σ)).map e.symm.toMonoidHom).map L.subtype)
    (hsyl : ∀ U : Subgroup (centralizer (X : Set G) ⧸ oddCore (centralizer (X : Set G))),
      IsPGroup 2 U →
      U ≤ centralizer ((D.subgroupOf (centralizer (X : Set G))).map
          (QuotientGroup.mk' (oddCore (centralizer (X : Set G)))) :
        Set (centralizer (X : Set G) ⧸ oddCore (centralizer (X : Set G)))) →
      Nat.card U ≤ 2) :
    ¬ ((D.subgroupOf (centralizer (X : Set G))).map
        (QuotientGroup.mk' (oddCore (centralizer (X : Set G))))).Normal := by
  subst hDe
  have hf : 1 ≤ f := by omega
  have := finite_of_card hK
  have : Finite (ModGL TwistTag.E6.tag K) := finite_modGL
  have htC := EPilot.mem_centralizer_of_inf_centralizer_eq_zpowers hKt
  obtain ⟨hOut, -⟩ := outer_solvable_and_center_eq_bot_twistedE6 hK σ e
  obtain ⟨hXc, hWodd⟩ := card_map_symm_w1C hf hk hσ e (L := L)
  have hXodd : Odd (Nat.card X) := by rw [hX, hXc]; exact hWodd
  have hXJ : X ≤ ((shortJ k σ).map e.symm.toMonoidHom).map L.subtype := by
    rw [hX]
    exact map_mono (map_mono (w1C_le_shortJ σ))
  have hXcard : Nat.card X = Nat.card (w1C k σ) := by rw [hX, hXc]
  obtain ⟨κ, h, hh⟩ := hfus
  have hinner := exists_inner_repYC_twistedE6 hset hf2 hk hK hσ e ht hKt hh
  have hord : orderOf (repYC (apply_apply_eq hK hσ) κ) = 2 := by
    rw [← Subgroup.orderOf_coe]
    exact orderOf_repY κ
  have hne : h⁻¹ * t * h ≠ t := hh ▸ mul_ne_self_of_ne_one (coe_symm_ne_one_of_orderOf e hord)
  choose Q hQ using exists_isCoreLeviDecomp_repYC (k := k) hf hk hK hσ
  obtain ⟨hDs, hDp, hDo⟩ := omegaMinusLevi_subgroupOf_facts hf hK hσ
  obtain ⟨hDq, hZD, hOutD⟩ := lemmaA_data_of_simple (G := G) e hDo
  have hXL : X ≤ L := hXJ.trans (map_subtype_le _)
  have htX : t ∈ centralizer (X : Set G) := centralizer_le hXL htC
  have hDW : (omegaMinusLevi σ).subgroupOf (graphFixedRootGroup TwistTag.E6 K σ) ≤
      centralizer (w1C k σ : Set (graphFixedRootGroup TwistTag.E6 K σ)) := by
    rw [w1C, centralizer_shortRootTorus_subgroupOf hf2 hk hK hσ]
    exact le_sup_right
  have hDX : (((omegaMinusLevi σ).subgroupOf (graphFixedRootGroup TwistTag.E6 K σ)).map
      e.symm.toMonoidHom).map L.subtype ≤ centralizer (X : Set G) := by
    rw [hX]
    exact F4Pilot.map_le_centralizer_map L.subtype
      (F4Pilot.map_le_centralizer_map e.symm.toMonoidHom hDW)
  exact not_normal_map_oddCore_of_inner_of_classes hset hOut e ht hKt
    (repYC (apply_apply_eq hK hσ)) (k := κ) (Or.inr hh) hne hinner Q (leviY σ)
    (fun κ => (hQ κ).1) (fun κ => (hQ κ).2.1) (fun κ => (hQ κ).2.2.1) (fun κ => (hQ κ).2.2.2.1)
    (fun κ => (hQ κ).2.2.2.2) (classPredicate_repYC hf hk hK hσ hQ κ)
    (shortJ_le_leviY hk hK hσ)
    (mem_subgroupOf.2 (repY_mem_omegaMinusLevi (apply_apply_eq hK hσ) κ)) hXodd hXJ
    (fun κ' ι X'' hX'' hc => step7_Y hf2 hk hK hσ hF5 hT κ κ' ι X'' hX'' (hc.trans hXcard))
    htX hDX hDq hZD hOutD hsyl

theorem not_normal_neighbour_2E6_Y_of_inputs (hset : StandardSetting G L) [CharP K 2]
    (hf2 : 2 ≤ f) (hk : Nat.card k = 2 ^ f) (hK : Nat.card K = (2 ^ f) ^ 2) {σ : K →+* K}
    (hσ : ∀ c, σ c = c ^ 2 ^ f) (e : L ≃* graphFixedRootGroup TwistTag.E6 K σ) {t : G}
    (ht : orderOf t = 2) (hKt : centralizer (L : Set G) ⊓ centralizer ({t} : Set G) = zpowers t)
    (hξ : TwistedFusionIn (xiAut σ (apply_apply_eq hK hσ)) (classTU (apply_apply_eq hK hσ)))
    (hF5 : LeviAutConj (leviY σ) (shortJ k σ)) (hT : TorusConjY k σ)
    {X : Subgroup G} (hX : X = ((w1C k σ).map e.symm.toMonoidHom).map L.subtype)
    {D : Subgroup G} (hDe : D = (((omegaMinusLevi σ).subgroupOf
      (graphFixedRootGroup TwistTag.E6 K σ)).map e.symm.toMonoidHom).map L.subtype)
    (hsyl : ∀ U : Subgroup (centralizer (X : Set G) ⧸ oddCore (centralizer (X : Set G))),
      IsPGroup 2 U →
      U ≤ centralizer ((D.subgroupOf (centralizer (X : Set G))).map
          (QuotientGroup.mk' (oddCore (centralizer (X : Set G)))) :
        Set (centralizer (X : Set G) ⧸ oddCore (centralizer (X : Set G)))) →
      Nat.card U ≤ 2) :
    ¬ ((D.subgroupOf (centralizer (X : Set G))).map
        (QuotientGroup.mk' (oddCore (centralizer (X : Set G))))).Normal :=
  not_normal_neighbour_2E6_Y_of_fusion hset hf2 hk hK hσ e ht hKt
    (exists_conj_eq_mul_repYC_twistedE6 hset (by omega) hk hK σ hσ e
      (exists_perfect_le_of_mulEquiv_twistedE6 (k := k) hf2 hk hK hσ e) hξ ht hKt)
    hF5 hT hX hDe hsyl

end Y

section Seitz

theorem not_normal_neighbour_2E6_X (hset : SeitzSetting G L) [CharP K 2] (hf2 : 2 ≤ f)
    (hk : Nat.card k = 2 ^ f) (hK : Nat.card K = (2 ^ f) ^ 2) {σ : K →+* K}
    (hσ : ∀ c, σ c = c ^ 2 ^ f) (e : L ≃* graphFixedRootGroup TwistTag.E6 K σ) {t : G}
    (htC : t ∈ centralizer (L : Set G)) (ht : orderOf t = 2)
    (hξ : TwistedFusionIn (xiAut σ (apply_apply_eq hK hσ)) (classTU (apply_apply_eq hK hσ)))
    (hF5 : LeviAutConj (leviX σ) (thetaJ k σ))
    {X : Subgroup G} (hX : X = (((E6GraphLevi.thetaTorus (algebraMap k K)).subgroupOf
      (graphFixedRootGroup TwistTag.E6 K σ)).map e.symm.toMonoidHom).map L.subtype)
    {D : Subgroup G} (hDe : D = (((su6Levi σ).subgroupOf
      (graphFixedRootGroup TwistTag.E6 K σ)).map e.symm.toMonoidHom).map L.subtype) :
    ¬ ((D.subgroupOf (centralizer (X : Set G))).map
        (QuotientGroup.mk' (oddCore (centralizer (X : Set G))))).Normal := by
  have hf : 1 ≤ f := by omega
  have : Finite k := Nat.finite_of_card_ne_zero (by rw [hk]; positivity)
  have hKt := inf_centralizer_eq_zpowers_twistedE6 hset hf hK hσ e htC ht
  have hW : E6GraphLevi.thetaTorus (algebraMap k K) ≤ graphFixedRootGroup TwistTag.E6 K σ :=
    thetaTorus_le_C0 hf hk hK hσ
  have hXL : X ≤ L := by
    rw [hX]
    exact map_subtype_le _
  have htX : t ∈ centralizer (X : Set G) := centralizer_le hXL htC
  have hXodd : Odd (Nat.card X) := by
    rw [hX, card_map_of_injective L.subtype_injective, card_map_of_injective e.symm.injective,
      Nat.card_congr (subgroupOfEquivOfLe hW).toEquiv]
    exact odd_card_thetaTorus hf hk
  have hXJ : X ≤ ((thetaJ k σ).map e.symm.toMonoidHom).map L.subtype := by
    rw [hX]
    refine map_mono (map_mono fun x hx => ?_)
    exact mem_subgroupOf.2 (thetaTorus_le_thetaRankOneGroup' hf hK (mem_subgroupOf.1 hx))
  exact not_normal_neighbour_2E6_X_of_inputs hset.standardSetting hf2 hk hK hσ e ht hKt hξ hF5
    hXodd hXJ hDe (neighbour_standard_2E6_X hset hf2 hk hK hσ e htC ht hX htX hDe).2.1

theorem not_normal_neighbour_2E6_Y (hset : SeitzSetting G L) [CharP K 2] (hf2 : 2 ≤ f)
    (hk : Nat.card k = 2 ^ f) (hK : Nat.card K = (2 ^ f) ^ 2) {σ : K →+* K}
    (hσ : ∀ c, σ c = c ^ 2 ^ f) (e : L ≃* graphFixedRootGroup TwistTag.E6 K σ) {t : G}
    (htC : t ∈ centralizer (L : Set G)) (ht : orderOf t = 2)
    (hξ : TwistedFusionIn (xiAut σ (apply_apply_eq hK hσ)) (classTU (apply_apply_eq hK hσ)))
    (hF5 : LeviAutConj (leviY σ) (shortJ k σ)) (hT : TorusConjY k σ)
    {X : Subgroup G} (hX : X = (((shortRootTorus (algebraMap k K)).subgroupOf
      (graphFixedRootGroup TwistTag.E6 K σ)).map e.symm.toMonoidHom).map L.subtype)
    {D : Subgroup G} (hDe : D = (((omegaMinusLevi σ).subgroupOf
      (graphFixedRootGroup TwistTag.E6 K σ)).map e.symm.toMonoidHom).map L.subtype) :
    ¬ ((D.subgroupOf (centralizer (X : Set G))).map
        (QuotientGroup.mk' (oddCore (centralizer (X : Set G))))).Normal := by
  have hf : 1 ≤ f := by omega
  have hKt := inf_centralizer_eq_zpowers_twistedE6 hset hf hK hσ e htC ht
  have hXL : X ≤ L := by
    rw [hX]
    exact map_subtype_le _
  have htX : t ∈ centralizer (X : Set G) := centralizer_le hXL htC
  exact not_normal_neighbour_2E6_Y_of_inputs hset.standardSetting hf2 hk hK hσ e ht hKt hξ hF5 hT
    hX hDe (neighbour_standard_2E6_Y hset hf2 hk hK hσ e htC ht hX htX hDe).2.1

end Seitz

end CFSG.SeitzReduction.TwistedE6Pilot
