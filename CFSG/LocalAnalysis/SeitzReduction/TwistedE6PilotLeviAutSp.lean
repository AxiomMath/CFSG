module

public import CFSG.LocalAnalysis.SeitzReduction.TwistedE6PilotLeviAutSU
public import CFSG.LocalAnalysis.SeitzReduction.E6PilotLeviAutSp
public import CFSG.LocalAnalysis.SeitzReduction.TwistedE6PilotCentralizerUDescent

public section

set_option linter.unusedSectionVars false

namespace CFSG.SeitzReduction.TwistedE6Pilot

open Subgroup CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType CFSG.LieType.Chevalley
  CFSG.LieType.Steinberg.Adjoint CFSG.LieType.Universal CFSG.LieType.Universal.Symplectic
  CFSG.LieType.RootSystem CFSG.Assembly.LowTwoRank CFSG.Timmesfeld.LieEmbed
open CFSG.LieType.Ree (ReeTag)
open CFSG.SeitzReduction.E6Pilot (IsAutConj IsAutConjIn)

local instance twistedE6PilotLeviAutSpNeZeroF4 : NeZero Tag.F4.rank := ⟨by decide⟩

local instance twistedE6PilotLeviAutSpNeZeroE6 : NeZero Tag.E6.rank := ⟨by decide⟩

local instance twistedE6PilotLeviAutSpNeZeroFolded : NeZero TwistTag.E6.foldedTag.rank :=
  ⟨by decide⟩

section Model

variable {k : Type} [Field k] [Finite k] [CharP k 2]

variable (k) in
@[expose] noncomputable def yLeviF4SpHom : ↥(StatedSp 3 k) →* ModGL .E6 k :=
  (E6Pilot.yGamma k).subtype.comp ((E6Pilot.yPsi k).symm.toMonoidHom.comp
    ((F4Pilot.graphAutF4 k).toMonoidHom.comp (F4Pilot.c3LeviHom k)))

theorem yLeviF4SpHom_injective : Function.Injective (yLeviF4SpHom k) :=
  (E6Pilot.yGamma k).subtype_injective.comp ((E6Pilot.yPsi k).symm.injective.comp
    ((F4Pilot.graphAutF4 k).injective.comp F4Pilot.c3LeviHom_injective))

theorem range_yLeviF4SpHom : (yLeviF4SpHom k).range = E6Pilot.yLeviF4 k := by
  have hid : (((E6Pilot.yLeviF4 k).subgroupOf (E6Pilot.yGamma k)).map
      (E6Pilot.yPsi k).toMonoidHom).map (E6Pilot.yPsi k).symm.toMonoidHom =
      (E6Pilot.yLeviF4 k).subgroupOf (E6Pilot.yGamma k) := by
    rw [Subgroup.map_map]
    convert Subgroup.map_id _
    ext x
    simp
  rw [yLeviF4SpHom, MonoidHom.range_comp, MonoidHom.range_comp, MonoidHom.range_comp,
    F4Pilot.range_c3LeviHom, F4Pilot.map_graphAutF4_C3Levi (K := k),
    ← E6Pilot.map_yPsi_yLeviF4, hid, subgroupOf_map_subtype,
    inf_of_le_left E6Pilot.yLeviF4_le_yGamma]

theorem map_yLeviF4SpHom_spRootSL2_one {v : Fin 3 → ℤ}
    (hv : v ∈ roots (isFiniteType_cartanC 3) ∅)
    (hvβ : F4Pilot.psiF4 (c3ToF4 v) = Pi.single 1 1) :
    (F4Pilot.spRootSL2 3 k v).map (yLeviF4SpHom k) =
      rootSubgroup .E6 k (Pi.single 3 1) ⊔ rootSubgroup .E6 k (-Pi.single 3 1) := by
  have hβ : IsRoot .F4 (Pi.single (1 : Fin Tag.F4.rank) 1) := isRoot_single .F4 1
  have hγ : IsRoot .F4 (c3ToF4 v) := isRoot_c3ToF4 hv
  rw [yLeviF4SpHom, ← Subgroup.map_map, ← Subgroup.map_map, ← Subgroup.map_map,
    F4Pilot.spRootSL2, Subgroup.map_sup, F4Pilot.map_c3LeviHom_rootGroup hv,
    F4Pilot.map_c3LeviHom_rootGroup (F4Pilot.neg_mem_roots_cartanC hv), map_neg,
    Subgroup.map_sup, F4Pilot.map_graphAutF4_rootGroup (K := k) hγ,
    F4Pilot.map_graphAutF4_rootGroup (K := k) (IsRoot.neg hγ), F4Pilot.psiF4_neg hγ, hvβ,
    F4Pilot.rootGroup_eq_subgroupOf hβ, F4Pilot.rootGroup_eq_subgroupOf (IsRoot.neg hβ),
    Subgroup.map_sup, Subgroup.map_sup, E6Pilot.map_yPsi_symm_rootSubgroup_single_one,
    E6Pilot.map_yPsi_symm_rootSubgroup_neg_single_one]

theorem map_yPsi_symm_rootSubgroup_single_two :
    (((rootSubgroup .F4 k (Pi.single 2 1)).subgroupOf (adjointGroup .F4 k)).map
      (E6Pilot.yPsi k).symm.toMonoidHom).map (E6Pilot.yGamma k).subtype =
      closure (Set.range fun c : k => xUnit .E6 k 2 c * xUnit .E6 k 4 c) := by
  have hS : Set.range (pinnedX .F4 k (Pi.single (2 : Fin Tag.F4.rank) 1)) ⊆
      adjointGroup .F4 k := by
    rintro _ ⟨c, rfl⟩
    exact pinnedX_mem_adjointGroup _ c
  have hval : ∀ c : k, (E6Pilot.yPsi k).symm ⟨xUnit .F4 k 2 c, xUnit_mem_adjointGroup 2 c⟩ =
      ⟨f4OrbitXUnit k 2 c, f4OrbitXUnit_mem 2 c⟩ := fun c => by
    rw [MulEquiv.symm_apply_eq]
    exact Subtype.ext (E6Pilot.coe_yPsi_f4OrbitXUnit 2 c).symm
  rw [rootSubgroup, E6Pilot.closure_subgroupOf_eq hS, MonoidHom.map_closure,
    MonoidHom.map_closure]
  congr 1
  ext g
  constructor
  · rintro ⟨_, ⟨x, ⟨c, hc⟩, rfl⟩, rfl⟩
    have hx : x = ⟨xUnit .F4 k 2 c, xUnit_mem_adjointGroup 2 c⟩ :=
      Subtype.ext (hc.symm.trans (by rw [pinnedX_single]))
    subst hx
    refine ⟨c, ?_⟩
    change xUnit .E6 k 2 c * xUnit .E6 k 4 c =
      (((E6Pilot.yPsi k).symm ⟨xUnit .F4 k 2 c, xUnit_mem_adjointGroup 2 c⟩ :
        E6Pilot.yGamma k) : ModGL .E6 k)
    rw [hval]
    exact (E6Pilot.f4OrbitXUnit_two c).symm
  · rintro ⟨c, rfl⟩
    refine ⟨_, ⟨⟨xUnit .F4 k 2 c, xUnit_mem_adjointGroup 2 c⟩,
      ⟨c, by rw [pinnedX_single]; rfl⟩, rfl⟩, ?_⟩
    change (((E6Pilot.yPsi k).symm ⟨xUnit .F4 k 2 c, xUnit_mem_adjointGroup 2 c⟩ :
      E6Pilot.yGamma k) : ModGL .E6 k) = xUnit .E6 k 2 c * xUnit .E6 k 4 c
    rw [hval]
    exact E6Pilot.f4OrbitXUnit_two c

theorem map_yPsi_symm_rootSubgroup_neg_single_two :
    (((rootSubgroup .F4 k (-Pi.single 2 1)).subgroupOf (adjointGroup .F4 k)).map
      (E6Pilot.yPsi k).symm.toMonoidHom).map (E6Pilot.yGamma k).subtype =
      closure (Set.range fun c : k => yUnit .E6 k 2 c * yUnit .E6 k 4 c) := by
  have hS : Set.range (pinnedX .F4 k (-Pi.single (2 : Fin Tag.F4.rank) 1)) ⊆
      adjointGroup .F4 k := by
    rintro _ ⟨c, rfl⟩
    exact pinnedX_mem_adjointGroup _ c
  have hval : ∀ c : k, (E6Pilot.yPsi k).symm ⟨yUnit .F4 k 2 c, yUnit_mem_adjointGroup 2 c⟩ =
      ⟨f4OrbitYUnit k 2 c, f4OrbitYUnit_mem 2 c⟩ := fun c => by
    rw [MulEquiv.symm_apply_eq]
    exact Subtype.ext (E6Pilot.coe_yPsi_f4OrbitYUnit 2 c).symm
  rw [rootSubgroup, E6Pilot.closure_subgroupOf_eq hS, MonoidHom.map_closure,
    MonoidHom.map_closure]
  congr 1
  ext g
  constructor
  · rintro ⟨_, ⟨x, ⟨c, hc⟩, rfl⟩, rfl⟩
    have hx : x = ⟨yUnit .F4 k 2 c, yUnit_mem_adjointGroup 2 c⟩ :=
      Subtype.ext (hc.symm.trans (by rw [pinnedX_neg_single]))
    subst hx
    refine ⟨c, ?_⟩
    change yUnit .E6 k 2 c * yUnit .E6 k 4 c =
      (((E6Pilot.yPsi k).symm ⟨yUnit .F4 k 2 c, yUnit_mem_adjointGroup 2 c⟩ :
        E6Pilot.yGamma k) : ModGL .E6 k)
    rw [hval]
    exact (E6Pilot.f4OrbitYUnit_two c).symm
  · rintro ⟨c, rfl⟩
    refine ⟨_, ⟨⟨yUnit .F4 k 2 c, yUnit_mem_adjointGroup 2 c⟩,
      ⟨c, by rw [pinnedX_neg_single]; rfl⟩, rfl⟩, ?_⟩
    change (((E6Pilot.yPsi k).symm ⟨yUnit .F4 k 2 c, yUnit_mem_adjointGroup 2 c⟩ :
      E6Pilot.yGamma k) : ModGL .E6 k) = yUnit .E6 k 2 c * yUnit .E6 k 4 c
    rw [hval]
    exact E6Pilot.f4OrbitYUnit_two c

theorem exists_psiF4_c3ToF4_eq_single_two :
    ∃ v ∈ roots (isFiniteType_cartanC 3) ∅,
      F4Pilot.psiF4 (c3ToF4 v) = Pi.single (2 : Fin Tag.F4.rank) 1 := by
  have hβ : IsRoot .F4 (Pi.single (2 : Fin Tag.F4.rank) 1) := isRoot_single .F4 2
  have h3 : (Pi.single (2 : Fin Tag.F4.rank) 1 : Fin Tag.F4.rank → ℤ) ⟨3, by decide⟩ = 0 :=
    Pi.single_eq_of_ne (by decide) _
  have hc : F4Pilot.psiF4 (Pi.single (2 : Fin Tag.F4.rank) 1) ∈ F4Pilot.c3LeviRoots := by
    rw [← F4Pilot.psiF4_mem_b3LeviRoots_iff (F4Pilot.isRoot_psiF4 hβ), F4Pilot.psiF4_psiF4 hβ]
    exact ⟨hβ, h3⟩
  obtain ⟨v, hv, hve⟩ := F4Pilot.exists_c3ToF4_eq_of_mem_c3LeviRoots hc
  exact ⟨v, hv, by rw [hve, F4Pilot.psiF4_psiF4 hβ]⟩

theorem map_yLeviF4SpHom_spRootSL2_two {v : Fin 3 → ℤ}
    (hv : v ∈ roots (isFiniteType_cartanC 3) ∅)
    (hvβ : F4Pilot.psiF4 (c3ToF4 v) = Pi.single 2 1) :
    (F4Pilot.spRootSL2 3 k v).map (yLeviF4SpHom k) =
      closure (Set.range fun c : k => xUnit .E6 k 2 c * xUnit .E6 k 4 c) ⊔
        closure (Set.range fun c : k => yUnit .E6 k 2 c * yUnit .E6 k 4 c) := by
  have hβ : IsRoot .F4 (Pi.single (2 : Fin Tag.F4.rank) 1) := isRoot_single .F4 2
  have hγ : IsRoot .F4 (c3ToF4 v) := isRoot_c3ToF4 hv
  rw [yLeviF4SpHom, ← Subgroup.map_map, ← Subgroup.map_map, ← Subgroup.map_map,
    F4Pilot.spRootSL2, Subgroup.map_sup, F4Pilot.map_c3LeviHom_rootGroup hv,
    F4Pilot.map_c3LeviHom_rootGroup (F4Pilot.neg_mem_roots_cartanC hv), map_neg,
    Subgroup.map_sup, F4Pilot.map_graphAutF4_rootGroup (K := k) hγ,
    F4Pilot.map_graphAutF4_rootGroup (K := k) (IsRoot.neg hγ), F4Pilot.psiF4_neg hγ, hvβ,
    F4Pilot.rootGroup_eq_subgroupOf hβ, F4Pilot.rootGroup_eq_subgroupOf (IsRoot.neg hβ),
    Subgroup.map_sup, Subgroup.map_sup, map_yPsi_symm_rootSubgroup_single_two,
    map_yPsi_symm_rootSubgroup_neg_single_two]

end Model

local instance twistedE6PilotLeviAutSpNeZeroTw : NeZero TwistTag.E6.tag.rank := ⟨by decide⟩

section BaseChange

variable {K : Type} [Field K]

@[expose] noncomputable def pairSL2A3 {k : Type} [Field k] (ι : k →+* K) :
    Subgroup (ModGL TwistTag.E6.tag K) :=
  closure {g | ∃ c : k, g = pinnedX TwistTag.E6.tag K (Pi.single 2 1) (ι c) *
      pinnedX TwistTag.E6.tag K (Pi.single 4 1) (ι c) ∨
    g = pinnedX TwistTag.E6.tag K (-Pi.single 2 1) (ι c) *
      pinnedX TwistTag.E6.tag K (-Pi.single 4 1) (ι c)}

variable {k : Type} [Field k] (ι : k →+* K)

theorem map_baseChangeGL_rootSubgroup_sup :
    (rootSubgroup .E6 k (Pi.single 3 1) ⊔ rootSubgroup .E6 k (-Pi.single 3 1)).map
      (baseChangeGL (τ := .E6) ι) = rootSL2A4 ι := by
  apply le_antisymm
  · refine Subgroup.map_le_iff_le_comap.mpr (sup_le ((closure_le _).mpr ?_)
      ((closure_le _).mpr ?_))
    · rintro _ ⟨c, rfl⟩
      exact subset_closure ⟨c, Or.inl (baseChangeGL_pinnedX ι _ c)⟩
    · rintro _ ⟨c, rfl⟩
      exact subset_closure ⟨c, Or.inr (baseChangeGL_pinnedX ι _ c)⟩
  · refine (closure_le _).mpr ?_
    rintro _ ⟨c, rfl | rfl⟩
    · exact ⟨_, mem_sup_left (subset_closure ⟨c, rfl⟩), baseChangeGL_pinnedX ι _ c⟩
    · exact ⟨_, mem_sup_right (subset_closure ⟨c, rfl⟩), baseChangeGL_pinnedX ι _ c⟩

theorem baseChangeGL_orbitTwo_x (c : k) :
    baseChangeGL (τ := .E6) ι (xUnit .E6 k 2 c * xUnit .E6 k 4 c) =
      pinnedX TwistTag.E6.tag K (Pi.single 2 1) (ι c) *
        pinnedX TwistTag.E6.tag K (Pi.single 4 1) (ι c) := by
  rw [map_mul, baseChangeGL_xUnit, baseChangeGL_xUnit, pinnedX_single, pinnedX_single]
  rfl

theorem baseChangeGL_orbitTwo_y (c : k) :
    baseChangeGL (τ := .E6) ι (yUnit .E6 k 2 c * yUnit .E6 k 4 c) =
      pinnedX TwistTag.E6.tag K (-Pi.single 2 1) (ι c) *
        pinnedX TwistTag.E6.tag K (-Pi.single 4 1) (ι c) := by
  rw [map_mul, baseChangeGL_yUnit, baseChangeGL_yUnit, pinnedX_neg_single, pinnedX_neg_single]
  rfl

theorem map_baseChangeGL_orbitTwo_sup :
    (closure (Set.range fun c : k => xUnit .E6 k 2 c * xUnit .E6 k 4 c) ⊔
        closure (Set.range fun c : k => yUnit .E6 k 2 c * yUnit .E6 k 4 c)).map
      (baseChangeGL (τ := .E6) ι) = pairSL2A3 ι := by
  apply le_antisymm
  · refine Subgroup.map_le_iff_le_comap.mpr (sup_le ((closure_le _).mpr ?_)
      ((closure_le _).mpr ?_))
    · rintro _ ⟨c, rfl⟩
      exact subset_closure ⟨c, Or.inl (baseChangeGL_orbitTwo_x ι c)⟩
    · rintro _ ⟨c, rfl⟩
      exact subset_closure ⟨c, Or.inr (baseChangeGL_orbitTwo_y ι c)⟩
  · refine (closure_le _).mpr ?_
    rintro _ ⟨c, rfl | rfl⟩
    · exact ⟨_, mem_sup_left (subset_closure ⟨c, rfl⟩), baseChangeGL_orbitTwo_x ι c⟩
    · exact ⟨_, mem_sup_right (subset_closure ⟨c, rfl⟩), baseChangeGL_orbitTwo_y ι c⟩

end BaseChange

section Standard

variable {f : ℕ} {k K : Type} [Field k] [Field K] [Algebra k K]

@[expose] noncomputable def uLeviSpHom [Finite k] [CharP k 2] :
    ↥(StatedSp 3 k) →* ModGL TwistTag.E6.tag K :=
  (baseChangeGL (τ := TwistTag.E6.tag) (algebraMap k K)).comp (yLeviF4SpHom k)

theorem uLeviSpHom_injective [Finite k] [CharP k 2] :
    Function.Injective (uLeviSpHom (k := k) (K := K)) :=
  (baseChangeGL_injective (τ := TwistTag.E6.tag) (algebraMap k K)).comp yLeviF4SpHom_injective

theorem range_uLeviSpHom [Finite k] [CharP k 2] (hf : 1 ≤ f) (hk : Nat.card k = 2 ^ f)
    (hK : Nat.card K = (2 ^ f) ^ 2) {σ : K →+* K} (hσ : ∀ c, σ c = c ^ 2 ^ f) :
    (uLeviSpHom (k := k) (K := K)).range = uLevi σ := by
  rw [uLevi_eq_map hf hk hK hσ]
  ext x
  constructor
  · rintro ⟨g, rfl⟩
    exact ⟨yLeviF4SpHom k g, by rw [← range_yLeviF4SpHom]; exact ⟨g, rfl⟩, rfl⟩
  · rintro ⟨y, hy, rfl⟩
    rw [← range_yLeviF4SpHom] at hy
    obtain ⟨g, rfl⟩ := hy
    exact ⟨g, rfl⟩

@[expose] noncomputable def uLeviSpEquiv [Finite k] [CharP k 2] (hf : 1 ≤ f)
    (hk : Nat.card k = 2 ^ f) (hK : Nat.card K = (2 ^ f) ^ 2) {σ : K →+* K}
    (hσ : ∀ c, σ c = c ^ 2 ^ f) :
    ↥(StatedSp 3 k) ≃* (uLevi σ).subgroupOf (graphFixedRootGroup TwistTag.E6 K σ) :=
  ((MonoidHom.ofInjective (uLeviSpHom_injective (k := k) (K := K))).trans
    (MulEquiv.subgroupCongr (range_uLeviSpHom hf hk hK hσ))).trans
    (subgroupOfEquivOfLe (inf_le_right : uLevi σ ≤ graphFixedRootGroup TwistTag.E6 K σ)).symm

theorem map_uLeviSpEquiv [Finite k] [CharP k 2] (hf : 1 ≤ f) (hk : Nat.card k = 2 ^ f)
    (hK : Nat.card K = (2 ^ f) ^ 2) {σ : K →+* K} (hσ : ∀ c, σ c = c ^ 2 ^ f)
    (H : Subgroup ↥(StatedSp 3 k)) :
    (H.map (uLeviSpEquiv hf hk hK hσ).toMonoidHom).map
        ((uLevi σ).subgroupOf (graphFixedRootGroup TwistTag.E6 K σ)).subtype =
      (H.map (uLeviSpHom (k := k) (K := K))).subgroupOf (graphFixedRootGroup TwistTag.E6 K σ) := by
  ext x
  rw [mem_subgroupOf]
  constructor
  · rintro ⟨_, ⟨g, hg, rfl⟩, rfl⟩
    exact ⟨g, hg, rfl⟩
  · rintro ⟨g, hg, hgx⟩
    refine ⟨uLeviSpEquiv hf hk hK hσ g, ⟨g, hg, rfl⟩, ?_⟩
    apply Subtype.ext
    exact hgx

theorem isAutConjIn_uLevi_rootSL2A4 (hf : 1 ≤ f) (hk : Nat.card k = 2 ^ f)
    (hK : Nat.card K = (2 ^ f) ^ 2) {σ : K →+* K} (hσ : ∀ c, σ c = c ^ 2 ^ f) :
    IsAutConjIn ((uLevi σ).subgroupOf (graphFixedRootGroup TwistTag.E6 K σ))
      ((rootSL2A4 (algebraMap k K)).subgroupOf (graphFixedRootGroup TwistTag.E6 K σ)) := by
  have := Nat.finite_of_card_ne_zero (show Nat.card k ≠ 0 by rw [hk]; positivity)
  have hk2 : (2 : k) = 0 := E6GraphHighestRoot.two_eq_zero_of_card hf hk
  have : CharP k 2 := CharTwo.of_one_ne_zero_of_two_eq_zero one_ne_zero hk2
  obtain ⟨v, hv, hvβ⟩ := E6Pilot.exists_psiF4_c3ToF4_eq_single_one
  have h1 := (E6Pilot.isAutConj_spRootSL2 (K := k) le_rfl v).isAutConjIn_map
    (uLeviSpEquiv hf hk hK hσ)
  have e : (F4Pilot.spRootSL2 3 k v).map (uLeviSpHom (k := k) (K := K)) =
      rootSL2A4 (algebraMap k K) := by
    have h2 := map_baseChangeGL_rootSubgroup_sup (k := k) (algebraMap k K)
    rw [← map_yLeviF4SpHom_spRootSL2_one hv hvβ, Subgroup.map_map] at h2
    exact h2
  rwa [map_uLeviSpEquiv, e] at h1

theorem isAutConjIn_uLevi_pairSL2A3 (hf : 1 ≤ f) (hk : Nat.card k = 2 ^ f)
    (hK : Nat.card K = (2 ^ f) ^ 2) {σ : K →+* K} (hσ : ∀ c, σ c = c ^ 2 ^ f) :
    IsAutConjIn ((uLevi σ).subgroupOf (graphFixedRootGroup TwistTag.E6 K σ))
      ((pairSL2A3 (algebraMap k K)).subgroupOf (graphFixedRootGroup TwistTag.E6 K σ)) := by
  have := Nat.finite_of_card_ne_zero (show Nat.card k ≠ 0 by rw [hk]; positivity)
  have hk2 : (2 : k) = 0 := E6GraphHighestRoot.two_eq_zero_of_card hf hk
  have : CharP k 2 := CharTwo.of_one_ne_zero_of_two_eq_zero one_ne_zero hk2
  obtain ⟨v, hv, hvβ⟩ := exists_psiF4_c3ToF4_eq_single_two
  have h1 := (E6Pilot.isAutConj_spRootSL2 (K := k) le_rfl v).isAutConjIn_map
    (uLeviSpEquiv hf hk hK hσ)
  have e : (F4Pilot.spRootSL2 3 k v).map (uLeviSpHom (k := k) (K := K)) =
      pairSL2A3 (algebraMap k K) := by
    have h2 := map_baseChangeGL_orbitTwo_sup (k := k) (algebraMap k K)
    rw [← map_yLeviF4SpHom_spRootSL2_two hv hvβ, Subgroup.map_map] at h2
    exact h2
  rwa [map_uLeviSpEquiv, e] at h1

theorem rootSL2A4_le_uLevi (hf : 1 ≤ f) (hk : Nat.card k = 2 ^ f)
    (hK : Nat.card K = (2 ^ f) ^ 2) {σ : K →+* K} (hσ : ∀ c, σ c = c ^ 2 ^ f) :
    rootSL2A4 (algebraMap k K) ≤ uLevi σ := by
  have := Nat.finite_of_card_ne_zero (show Nat.card k ≠ 0 by rw [hk]; positivity)
  have hk2 : (2 : k) = 0 := E6GraphHighestRoot.two_eq_zero_of_card hf hk
  have : CharP k 2 := CharTwo.of_one_ne_zero_of_two_eq_zero one_ne_zero hk2
  obtain ⟨v, hv, hvβ⟩ := E6Pilot.exists_psiF4_c3ToF4_eq_single_one
  have h2 := map_baseChangeGL_rootSubgroup_sup (k := k) (algebraMap k K)
  rw [← map_yLeviF4SpHom_spRootSL2_one hv hvβ, Subgroup.map_map] at h2
  have h3 : (F4Pilot.spRootSL2 3 k v).map (uLeviSpHom (k := k) (K := K)) ≤ uLevi σ := by
    rw [← range_uLeviSpHom hf hk hK hσ]
    exact map_le_range _ _
  exact h2 ▸ h3

theorem pairSL2A3_le_uLevi (hf : 1 ≤ f) (hk : Nat.card k = 2 ^ f)
    (hK : Nat.card K = (2 ^ f) ^ 2) {σ : K →+* K} (hσ : ∀ c, σ c = c ^ 2 ^ f) :
    pairSL2A3 (algebraMap k K) ≤ uLevi σ := by
  have := Nat.finite_of_card_ne_zero (show Nat.card k ≠ 0 by rw [hk]; positivity)
  have hk2 : (2 : k) = 0 := E6GraphHighestRoot.two_eq_zero_of_card hf hk
  have : CharP k 2 := CharTwo.of_one_ne_zero_of_two_eq_zero one_ne_zero hk2
  obtain ⟨v, hv, hvβ⟩ := exists_psiF4_c3ToF4_eq_single_two
  have h2 := map_baseChangeGL_orbitTwo_sup (k := k) (algebraMap k K)
  rw [← map_yLeviF4SpHom_spRootSL2_two hv hvβ, Subgroup.map_map] at h2
  have h3 : (F4Pilot.spRootSL2 3 k v).map (uLeviSpHom (k := k) (K := K)) ≤ uLevi σ := by
    rw [← range_uLeviSpHom hf hk hK hσ]
    exact map_le_range _ _
  exact h2 ▸ h3

end Standard

section Transport

theorem leviAutWordsU_check :
    twistedE6RelAct (relWordUX ++ [2, 3, 1]) (Pi.single 3 1) = e6HighestRoot ∧
      twistedE6RelAct (relWordUX ++ [2, 3, 1]) (-Pi.single 3 1) = -e6HighestRoot ∧
      twistedE6RelAct (relWordUY ++ [3, 2]) (Pi.single 2 1) = twistedE6ClassRootU ∧
      twistedE6RelAct (relWordUY ++ [3, 2]) (Pi.single 4 1) = twistedE6ClassRootU' ∧
      twistedE6RelAct (relWordUY ++ [3, 2]) (-Pi.single 2 1) = -twistedE6ClassRootU ∧
      twistedE6RelAct (relWordUY ++ [3, 2]) (-Pi.single 4 1) = -twistedE6ClassRootU' ∧
      ([2, 3, 1] : List (Fin TwistTag.E6.foldedTag.rank)).flatMap TwistTag.E6.orbitWord =
        [3, 1, 2, 4] ∧
      ([3, 2] : List (Fin TwistTag.E6.foldedTag.rank)).flatMap TwistTag.E6.orbitWord = [1, 3] := by
  decide +kernel

variable {K : Type} [Field K]

theorem twistedE6RelWeyl_two_three_one_mem_yLeviF4 :
    twistedE6RelWeyl K [2, 3, 1] ∈ E6Pilot.yLeviF4 K := by
  rw [twistedE6RelWeyl, leviAutWordsU_check.2.2.2.2.2.2.1]
  simp only [List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one]
  exact mul_mem (E6Pilot.weylElt_mem_yLeviF4 (Or.inr rfl))
    (mul_mem (E6Pilot.weylElt_mem_yLeviF4 (Or.inl rfl))
      E6Pilot.weylElt_two_mul_weylElt_four_mem_yLeviF4)

theorem twistedE6RelWeyl_three_two_mem_yLeviF4 :
    twistedE6RelWeyl K [3, 2] ∈ E6Pilot.yLeviF4 K := by
  rw [twistedE6RelWeyl, leviAutWordsU_check.2.2.2.2.2.2.2]
  simp only [List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one]
  exact mul_mem (E6Pilot.weylElt_mem_yLeviF4 (Or.inl rfl))
    (E6Pilot.weylElt_mem_yLeviF4 (Or.inr rfl))

variable [CharP K 2]

theorem map_conj_rootSL2A4_eq (ω : List (Fin TwistTag.E6.foldedTag.rank))
    (h1 : twistedE6RelAct ω (Pi.single 3 1) = e6HighestRoot)
    (h2 : twistedE6RelAct ω (-Pi.single 3 1) = -e6HighestRoot) {k : Type} [Field k]
    (ι : k →+* K) :
    (rootSL2A4 ι).map (MulAut.conj (twistedE6RelWeyl K ω)).toMonoidHom =
      E6GraphLevi.thetaRankOneGroup ι := by
  rw [rootSL2A4, MonoidHom.map_closure, E6GraphLevi.thetaRankOneGroup,
    E6GraphLevi.thetaRootGroup, E6GraphLevi.thetaNegRootGroup, ← Subgroup.closure_union]
  congr 1
  ext g
  constructor
  · rintro ⟨_, ⟨c, rfl | rfl⟩, rfl⟩
    · left
      refine ⟨c, ?_⟩
      change _ = twistedE6RelWeyl K _ * _ * (twistedE6RelWeyl K _)⁻¹
      rw [twistedE6RelWeyl_conj_pinnedX _ (isRoot_single _ _), h1]
    · right
      refine ⟨c, ?_⟩
      change _ = twistedE6RelWeyl K _ * _ * (twistedE6RelWeyl K _)⁻¹
      rw [twistedE6RelWeyl_conj_pinnedX _ (isRoot_neg_single _ _), h2]
  · rintro (⟨c, rfl⟩ | ⟨c, rfl⟩)
    · refine ⟨_, ⟨c, Or.inl rfl⟩, ?_⟩
      change twistedE6RelWeyl K _ * _ * (twistedE6RelWeyl K _)⁻¹ = _
      rw [twistedE6RelWeyl_conj_pinnedX _ (isRoot_single _ _), h1]
    · refine ⟨_, ⟨c, Or.inr rfl⟩, ?_⟩
      change twistedE6RelWeyl K _ * _ * (twistedE6RelWeyl K _)⁻¹ = _
      rw [twistedE6RelWeyl_conj_pinnedX _ (isRoot_neg_single _ _), h2]

theorem map_conj_pairSL2A3_eq (ω : List (Fin TwistTag.E6.foldedTag.rank))
    (h3 : twistedE6RelAct ω (Pi.single 2 1) = twistedE6ClassRootU)
    (h4 : twistedE6RelAct ω (Pi.single 4 1) = twistedE6ClassRootU')
    (h5 : twistedE6RelAct ω (-Pi.single 2 1) = -twistedE6ClassRootU)
    (h6 : twistedE6RelAct ω (-Pi.single 4 1) = -twistedE6ClassRootU') {k : Type} [Field k]
    (ι : k →+* K) :
    (pairSL2A3 ι).map (MulAut.conj (twistedE6RelWeyl K ω)).toMonoidHom = shortRankOneGroup ι := by
  rw [pairSL2A3, MonoidHom.map_closure, shortRankOneGroup]
  congr 1
  ext g
  constructor
  · rintro ⟨_, ⟨c, rfl | rfl⟩, rfl⟩
    · refine ⟨c, Or.inl ?_⟩
      change twistedE6RelWeyl K _ * (_ * _) * (twistedE6RelWeyl K _)⁻¹ = _
      rw [conj_mul_distrib, twistedE6RelWeyl_conj_pinnedX _ (isRoot_single _ _),
        twistedE6RelWeyl_conj_pinnedX _ (isRoot_single _ _), h3, h4]
    · refine ⟨c, Or.inr ?_⟩
      change twistedE6RelWeyl K _ * (_ * _) * (twistedE6RelWeyl K _)⁻¹ = _
      rw [conj_mul_distrib, twistedE6RelWeyl_conj_pinnedX _ (isRoot_neg_single _ _),
        twistedE6RelWeyl_conj_pinnedX _ (isRoot_neg_single _ _), h5, h6]
  · rintro ⟨c, rfl | rfl⟩
    · refine ⟨_, ⟨c, Or.inl rfl⟩, ?_⟩
      change twistedE6RelWeyl K _ * (_ * _) * (twistedE6RelWeyl K _)⁻¹ = _
      rw [conj_mul_distrib, twistedE6RelWeyl_conj_pinnedX _ (isRoot_single _ _),
        twistedE6RelWeyl_conj_pinnedX _ (isRoot_single _ _), h3, h4]
    · refine ⟨_, ⟨c, Or.inr rfl⟩, ?_⟩
      change twistedE6RelWeyl K _ * (_ * _) * (twistedE6RelWeyl K _)⁻¹ = _
      rw [conj_mul_distrib, twistedE6RelWeyl_conj_pinnedX _ (isRoot_neg_single _ _),
        twistedE6RelWeyl_conj_pinnedX _ (isRoot_neg_single _ _), h5, h6]

end Transport

section Final

variable {f : ℕ} {k K : Type} [Field k] [Field K] [Algebra k K]

theorem relWeylC_two_three_one_mem_uLevi (σ : K →+* K) :
    relWeylC σ [2, 3, 1] ∈ (uLevi σ).subgroupOf (graphFixedRootGroup TwistTag.E6 K σ) :=
  mem_subgroupOf.2 (mem_inf.2 ⟨twistedE6RelWeyl_two_three_one_mem_yLeviF4,
    twistedE6RelWeyl_mem σ _⟩)

theorem relWeylC_three_two_mem_uLevi (σ : K →+* K) :
    relWeylC σ [3, 2] ∈ (uLevi σ).subgroupOf (graphFixedRootGroup TwistTag.E6 K σ) :=
  mem_subgroupOf.2 (mem_inf.2 ⟨twistedE6RelWeyl_three_two_mem_yLeviF4,
    twistedE6RelWeyl_mem σ _⟩)

theorem isAutConjIn_levi_uX (hf : 1 ≤ f) (hk : Nat.card k = 2 ^ f)
    (hK : Nat.card K = (2 ^ f) ^ 2) {σ : K →+* K} (hσ : ∀ c, σ c = c ^ 2 ^ f) :
    IsAutConjIn (((uLevi σ).subgroupOf (graphFixedRootGroup TwistTag.E6 K σ)).map
        (MulAut.conj (relWeylC σ relWordUX)).toMonoidHom)
      ((E6GraphLevi.thetaRankOneGroup (algebraMap k K)).subgroupOf
        (graphFixedRootGroup TwistTag.E6 K σ)) := by
  have : CharP K 2 := charP_two_of_card hf hK
  obtain ⟨h1, h2, -⟩ := leviAutWordsU_check
  have hJD : (rootSL2A4 (algebraMap k K)).subgroupOf (graphFixedRootGroup TwistTag.E6 K σ) ≤
      (uLevi σ).subgroupOf (graphFixedRootGroup TwistTag.E6 K σ) := fun x hx =>
    mem_subgroupOf.2 (rootSL2A4_le_uLevi hf hk hK hσ (mem_subgroupOf.1 hx))
  have h0 := isAutConjIn_map_conj (isAutConjIn_uLevi_rootSL2A4 hf hk hK hσ) hJD
    (relWeylC σ (relWordUX ++ [2, 3, 1]))
  have hM : ((uLevi σ).subgroupOf (graphFixedRootGroup TwistTag.E6 K σ)).map
      (MulAut.conj (relWeylC σ (relWordUX ++ [2, 3, 1]))).toMonoidHom =
      ((uLevi σ).subgroupOf (graphFixedRootGroup TwistTag.E6 K σ)).map
        (MulAut.conj (relWeylC σ relWordUX)).toMonoidHom := by
    rw [relWeylC_append, ← E6Pilot.map_conj_map_conj_eq_conj_mul,
      map_conj_eq_self_of_mem (relWeylC_two_three_one_mem_uLevi σ)]
  have hJ : ((rootSL2A4 (algebraMap k K)).subgroupOf (graphFixedRootGroup TwistTag.E6 K σ)).map
      (MulAut.conj (relWeylC σ (relWordUX ++ [2, 3, 1]))).toMonoidHom =
      (E6GraphLevi.thetaRankOneGroup (algebraMap k K)).subgroupOf
        (graphFixedRootGroup TwistTag.E6 K σ) := by
    rw [← E6Pilot.subgroupOf_map_conj_eq_map_conj_subgroupOf
      ((rootSL2A4_le_uLevi hf hk hK hσ).trans inf_le_right)]
    exact congrArg (fun H => H.subgroupOf (graphFixedRootGroup TwistTag.E6 K σ))
      (map_conj_rootSL2A4_eq _ h1 h2 (algebraMap k K))
  rwa [hM, hJ] at h0

theorem isAutConjIn_levi_uY (hf : 1 ≤ f) (hk : Nat.card k = 2 ^ f)
    (hK : Nat.card K = (2 ^ f) ^ 2) {σ : K →+* K} (hσ : ∀ c, σ c = c ^ 2 ^ f) :
    IsAutConjIn (((uLevi σ).subgroupOf (graphFixedRootGroup TwistTag.E6 K σ)).map
        (MulAut.conj (relWeylC σ relWordUY)).toMonoidHom)
      ((shortRankOneGroup (algebraMap k K)).subgroupOf (graphFixedRootGroup TwistTag.E6 K σ)) := by
  have : CharP K 2 := charP_two_of_card hf hK
  obtain ⟨-, -, h3, h4, h5, h6, -⟩ := leviAutWordsU_check
  have hJD : (pairSL2A3 (algebraMap k K)).subgroupOf (graphFixedRootGroup TwistTag.E6 K σ) ≤
      (uLevi σ).subgroupOf (graphFixedRootGroup TwistTag.E6 K σ) := fun x hx =>
    mem_subgroupOf.2 (pairSL2A3_le_uLevi hf hk hK hσ (mem_subgroupOf.1 hx))
  have h0 := isAutConjIn_map_conj (isAutConjIn_uLevi_pairSL2A3 hf hk hK hσ) hJD
    (relWeylC σ (relWordUY ++ [3, 2]))
  have hM : ((uLevi σ).subgroupOf (graphFixedRootGroup TwistTag.E6 K σ)).map
      (MulAut.conj (relWeylC σ (relWordUY ++ [3, 2]))).toMonoidHom =
      ((uLevi σ).subgroupOf (graphFixedRootGroup TwistTag.E6 K σ)).map
        (MulAut.conj (relWeylC σ relWordUY)).toMonoidHom := by
    rw [relWeylC_append, ← E6Pilot.map_conj_map_conj_eq_conj_mul,
      map_conj_eq_self_of_mem (relWeylC_three_two_mem_uLevi σ)]
  have hJ : ((pairSL2A3 (algebraMap k K)).subgroupOf (graphFixedRootGroup TwistTag.E6 K σ)).map
      (MulAut.conj (relWeylC σ (relWordUY ++ [3, 2]))).toMonoidHom =
      (shortRankOneGroup (algebraMap k K)).subgroupOf (graphFixedRootGroup TwistTag.E6 K σ) := by
    rw [← E6Pilot.subgroupOf_map_conj_eq_map_conj_subgroupOf
      ((pairSL2A3_le_uLevi hf hk hK hσ).trans inf_le_right)]
    exact congrArg (fun H => H.subgroupOf (graphFixedRootGroup TwistTag.E6 K σ))
      (map_conj_pairSL2A3_eq _ h3 h4 h5 h6 (algebraMap k K))
  rwa [hM, hJ] at h0

end Final

end CFSG.SeitzReduction.TwistedE6Pilot
