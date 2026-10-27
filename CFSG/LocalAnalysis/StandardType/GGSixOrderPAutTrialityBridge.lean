module

public import CFSG.LocalAnalysis.StandardType.GGSixAutSteinbergTrialityModel
public import CFSG.LieType.Chevalley.EvenRootCommutatorD4
public import CFSG.LieType.Chevalley.GraphFixedHighestRoot
public import CFSG.LieType.Chevalley.RootCharacterConjugation
public import CFSG.LieType.Universal.SpinClause0
public import CFSG.LocalAnalysis.StandardType.GGTableBOrthRestOddEndMat
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalPointDataCoordinateRegular

public section

namespace CFSG.StandardType

namespace TriBridge

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Steinberg
  CFSG.LieType.Universal.Spin CFSG.StandardType.Triality
open scoped commutatorElement

set_option linter.unusedSectionVars false

@[expose] def bL0 : (Fin 4 → ℤ) →+ (Fin 4 → ℤ) where
  toFun v := ![v 1 - v 0, v 3 - v 0, v 2 + v 3 - v 0, v 3]
  map_zero' := by
    funext a
    fin_cases a <;> simp
  map_add' v w := by
    funext a
    fin_cases a <;> simp <;> ring

@[expose] def bL : (Fin 4 → ℤ) →+ (Fin TwistTag.D4.tag.rank → ℤ) := bL0

theorem bL_apply (v : Fin 4 → ℤ) : bL0 v = ![v 1 - v 0, v 3 - v 0, v 2 + v 3 - v 0, v 3] := rfl

@[expose] def bLinv0 (w : Fin 4 → ℤ) : Fin 4 → ℤ :=
  ![w 3 - w 1, w 0 + w 3 - w 1, w 2 - w 1, w 3]

@[expose] def bLinv (w : Fin TwistTag.D4.tag.rank → ℤ) : Fin 4 → ℤ := bLinv0 w

theorem bLinv_bL (v : Fin 4 → ℤ) : bLinv (bL v) = v := by
  show bLinv0 (bL0 v) = v
  funext a
  fin_cases a <;> simp [bLinv0, bL_apply]
  ring

theorem bL_bLinv (w : Fin TwistTag.D4.tag.rank → ℤ) : bL (bLinv w) = w := by
  show bL0 (bLinv0 w) = w
  funext a
  fin_cases a <;> simp [bLinv0, bL_apply]
  ring

theorem bL_injective : Function.Injective bL := fun v w h => by
  rw [← bLinv_bL v, ← bLinv_bL w, h]

theorem permLattice_D4 (w : Fin 4 → ℤ) :
    permLattice TwistTag.D4.perm w = ![w 3, w 0, w 2, w 1] := by
  funext a
  fin_cases a <;> rfl

theorem bL_tri (v : Fin 4 → ℤ) : bL (tri v) = permLattice TwistTag.D4.perm (bL v) := by
  show bL0 (tri v) = permLattice TwistTag.D4.perm (bL0 v)
  rw [permLattice_D4]
  funext a
  fin_cases a <;> simp [bL_apply, tri_apply] <;> ring

abbrev toTag (v : Fin 4 → ℤ) : Fin Tag.D4.rank → ℤ := v

theorem bL_roots_check : ∀ i j : Fin 4, ∀ s t : Bool, i ≠ j →
    ∃ k < Tag.D4.rootCertificate.roots.length,
      Tag.D4.rootCertificate.root k = toTag (bL0 (fromStd (lv i j s t))) := by
  decide

theorem bLinv_roots_check : ∀ k < Tag.D4.rootCertificate.roots.length,
    ∃ i j : Fin 4, ∃ s t : Bool, i ≠ j ∧
      toStdD 4 (bLinv0 (Tag.D4.rootCertificate.root k)) = lv i j s t := by
  decide

theorem add_self_check : ∀ k < Tag.D4.rootCertificate.roots.length,
    ∀ k' < Tag.D4.rootCertificate.roots.length,
      Tag.D4.rootCertificate.root k + Tag.D4.rootCertificate.root k ≠
        Tag.D4.rootCertificate.root k' := by
  decide


theorem isRoot_bL {γ : Fin 4 → ℤ} (hγ : γ ∈ rootsD4) : IsRoot TwistTag.D4.tag (bL γ) := by
  obtain ⟨i, j, s, t, hij, -, rfl⟩ := exists_eq_fromStd hγ
  exact (RootCertificate.isRoot_iff (Tag.rootCertificate_check _)).2 (bL_roots_check i j s t hij)

theorem bLinv_mem {w : Fin TwistTag.D4.tag.rank → ℤ} (hw : IsRoot TwistTag.D4.tag w) :
    bLinv w ∈ rootsD4 := by
  obtain ⟨k, hk, rfl⟩ := (RootCertificate.isRoot_iff (Tag.rootCertificate_check Tag.D4)).1 hw
  obtain ⟨i, j, s, t, hij, h⟩ := bLinv_roots_check k hk
  exact mem_rootsD4_iff.2 ⟨i, j, hij, s, t, h⟩

theorem isRoot_bL_iff {γ : Fin 4 → ℤ} : IsRoot TwistTag.D4.tag (bL γ) ↔ γ ∈ rootsD4 :=
  ⟨fun h => bLinv_bL γ ▸ bLinv_mem h, isRoot_bL⟩

theorem not_isRoot_add_self {w : Fin TwistTag.D4.tag.rank → ℤ} (hw : IsRoot TwistTag.D4.tag w) :
    ¬IsRoot TwistTag.D4.tag (w + w) := by
  obtain ⟨k, hk, rfl⟩ := (RootCertificate.isRoot_iff (Tag.rootCertificate_check Tag.D4)).1 hw
  intro h
  obtain ⟨k', hk', h'⟩ := (RootCertificate.isRoot_iff (Tag.rootCertificate_check Tag.D4)).1 h
  exact add_self_check k hk k' hk' h'.symm

theorem add_self_not_mem {γ : Fin 4 → ℤ} (hγ : γ ∈ rootsD4) : γ + γ ∉ rootsD4 := fun h => by
  rw [← isRoot_bL_iff, map_add] at h
  exact not_isRoot_add_self (isRoot_bL hγ) h

section Lift

variable {K : Type} [Field K]

noncomputable abbrev bridgeGen (g : ChevGen (Φ8 K) K) : ModGL TwistTag.D4.tag K :=
  pinnedX TwistTag.D4.tag K (bL g.1.1) g.2


theorem bridge_rels [CharP K 2] (O : CommOrder (Φ8 K)) :
    ∀ r ∈ relA (Φ8 K) K ∪ relB (Φ8 K) K O SpinPlus.commC,
      FreeGroup.lift (bridgeGen (K := K)) r = 1 := by
  rintro r (⟨γ, hγ, c, d, rfl⟩ | ⟨α, hα, β, hβ, hαβ, c, d, rfl⟩)
  · rw [map_mul, map_mul, map_inv, lift_chevOf _ hγ, lift_chevOf _ hγ, lift_chevOf _ hγ]
    change pinnedX TwistTag.D4.tag K (bL γ) c * pinnedX TwistTag.D4.tag K (bL γ) d *
      (pinnedX TwistTag.D4.tag K (bL γ) (c + d))⁻¹ = 1
    rw [pinnedX_add, mul_inv_cancel]
  · have hα' : α ∈ rootsD4 := hα
    have hβ' : β ∈ rootsD4 := hβ
    have hLα := isRoot_bL hα'
    have hLβ := isRoot_bL hβ'
    have hne' : bL α ≠ -bL β := by
      intro h
      apply hαβ
      apply bL_injective
      rw [map_add, h, neg_add_cancel, map_zero]
    by_cases hr : α + β ∈ (Φ8 K).roots
    · have hne : bL α ≠ bL β := by
        intro h
        have h' := bL_injective h
        subst h'
        exact add_self_not_mem hα' hr
      have hroot : IsRoot TwistTag.D4.tag (bL α + bL β) := by
        rw [← map_add]
        exact isRoot_bL hr
      rw [(SpinPlus.commOrder_list_eq three_le_four O hα hβ hαβ).1 hr]
      simp only [List.map_singleton, List.prod_singleton, one_smul, pow_one]
      rw [map_mul, map_commutatorElement, map_inv, lift_chevOf _ hα, lift_chevOf _ hβ,
        lift_chevOf _ hr]
      change ⁅pinnedX TwistTag.D4.tag K (bL α) c, pinnedX TwistTag.D4.tag K (bL β) d⁆ *
        (pinnedX TwistTag.D4.tag K (bL (α + β)) ((SpinPlus.commC α β (1, 1) : K) * c * d))⁻¹ = 1
      rw [intCast_commC, one_mul, map_add]
      have hrel := (d4_even_root_pair_relations (R := K) hLα hLβ hne hne' c d).1 hroot
      change ⁅pinnedX Tag.D4 K (bL α) c, pinnedX Tag.D4 K (bL β) d⁆ *
        (pinnedX Tag.D4 K (bL α + bL β) (c * d))⁻¹ = 1
      rw [hrel]
      exact mul_inv_cancel _
    · rw [(SpinPlus.commOrder_list_eq three_le_four O hα hβ hαβ).2 hr]
      simp only [List.map_nil, List.prod_nil, inv_one, mul_one]
      rw [map_commutatorElement, lift_chevOf _ hα, lift_chevOf _ hβ]
      change ⁅pinnedX TwistTag.D4.tag K (bL α) c, pinnedX TwistTag.D4.tag K (bL β) d⁆ = 1
      by_cases hab : α = β
      · subst hab
        refine commutatorElement_eq_one_iff_commute.2 ?_
        change pinnedX TwistTag.D4.tag K (bL α) c * pinnedX TwistTag.D4.tag K (bL α) d =
          pinnedX TwistTag.D4.tag K (bL α) d * pinnedX TwistTag.D4.tag K (bL α) c
        rw [← pinnedX_add, ← pinnedX_add, add_comm]
      · have hne : bL α ≠ bL β := fun h => hab (bL_injective h)
        have hnr : ¬IsRoot TwistTag.D4.tag (bL α + bL β) := by
          rw [← map_add, isRoot_bL_iff]
          exact hr
        exact (d4_even_root_pair_relations hLα hLβ hne hne' c d).2 hnr

variable [Finite K] [CharP K 2]

@[expose] noncomputable def bridgeSp : Sp8 K →* ModGL TwistTag.D4.tag K :=
  (PresentedGroup.toGroup (bridge_rels (ord8 K))).comp (presEquiv (ord8 K)).symm.toMonoidHom

theorem bridgeSp_xr {γ : Fin 4 → ℤ} (hγ : γ ∈ rootsD4) (c : K) :
    bridgeSp (xr γ c) = pinnedX TwistTag.D4.tag K (bL γ) c := by
  have hγ' : γ ∈ (Φ8 K).roots := hγ
  have h : (presEquiv (ord8 K)).symm (xr γ c) = PresentedGroup.of (⟨γ, hγ'⟩, c) := by
    rw [MulEquiv.symm_apply_eq, presEquiv_of]
  rw [bridgeSp, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, h]
  exact PresentedGroup.toGroup.of (bridge_rels (ord8 K))

theorem bridgeSp_mem (z : Sp8 K) : bridgeSp z ∈ adjointGroup TwistTag.D4.tag K := by
  have hle : ⨆ γ ∈ rootsD4, plusRootGroup 4 K three_le_four γ ≤
      (adjointGroup TwistTag.D4.tag K).comap (bridgeSp (K := K)) := by
    refine iSup₂_le fun γ hγ z hz => ?_
    obtain ⟨c, rfl⟩ := ((SpinPlus.isParametrization three_le_four γ hγ).1 z).1 hz
    rw [Subgroup.mem_comap]
    change bridgeSp (xr γ c) ∈ _
    rw [bridgeSp_xr hγ]
    exact pinnedX_mem_adjointGroup _ _
  rw [plusDatum_iSup_eq_top 4 K three_le_four] at hle
  exact hle (Subgroup.mem_top z)

@[expose] noncomputable def bridgeC : Sp8 K →* adjointGroup TwistTag.D4.tag K :=
  (bridgeSp (K := K)).codRestrict _ bridgeSp_mem

theorem coe_bridgeC (z : Sp8 K) : (bridgeC z : ModGL TwistTag.D4.tag K) = bridgeSp z := rfl

theorem adjointGroup_le_range_bridgeSp :
    adjointGroup TwistTag.D4.tag K ≤ (bridgeSp (K := K)).range := by
  refine (Subgroup.closure_le _).2 ?_
  rintro g ⟨i, c, hg | hg⟩
  · have hg' : g = xUnit TwistTag.D4.tag K i c := Units.ext hg
    subst hg'
    refine ⟨xr (bLinv (Pi.single i 1)) c, ?_⟩
    rw [bridgeSp_xr (bLinv_mem (isRoot_single _ i)), bL_bLinv, pinnedX_single]
  · have hg' : g = yUnit TwistTag.D4.tag K i c := Units.ext hg
    subst hg'
    refine ⟨xr (bLinv (-Pi.single i 1)) c, ?_⟩
    rw [bridgeSp_xr (bLinv_mem (isRoot_neg_single _ i)), bL_bLinv, pinnedX_neg_single]

theorem bridgeC_surjective : Function.Surjective (bridgeC (K := K)) := by
  rintro ⟨y, hy⟩
  obtain ⟨z, hz⟩ := adjointGroup_le_range_bridgeSp hy
  exact ⟨z, Subtype.ext hz⟩

theorem center_Sp8_eq_bot : Subgroup.center (Sp8 K) = ⊥ := by
  have hZ : Subgroup.center (Om8 K) = ⊥ := OrthRestOdd.center_matrixDerived_eq_bot
    (CFSG.ComponentClassification.CatalogueBOrthogonalPointData.regular_coordinateQuadPlus 4 K
      (by norm_num)).1 (by norm_num)
  refine eq_bot_iff.2 fun z hz => ?_
  have h1 : modelEquiv8 z ∈ Subgroup.center (Om8 K) := Subgroup.mem_center_iff.2 fun y => by
    obtain ⟨w, rfl⟩ := (modelEquiv8 (K := K)).surjective y
    rw [← map_mul, ← map_mul, Subgroup.mem_center_iff.1 hz w]
  rw [hZ, Subgroup.mem_bot] at h1
  exact Subgroup.mem_bot.2 ((modelEquiv8 (K := K)).injective (h1.trans (map_one _).symm))

theorem bridgeC_injective : Function.Injective (bridgeC (K := K)) := by
  have hQ := isQuasisimple_spinGroup_quadPlus (K := K) (n := 4) (by norm_num)
  have hne : ∃ k, bridgeC (K := K) k ≠ 1 := by
    refine ⟨xr rootA 1, fun h => ?_⟩
    have h1 := congrArg Subtype.val h
    rw [coe_bridgeC, bridgeSp_xr rootA_mem, OneMemClass.coe_one,
      ← pinnedX_zero TwistTag.D4.tag K (bL rootA)] at h1
    exact one_ne_zero (pinnedX_injective _ _ _ h1)
  have hker := CFSG.LieType.CurtisTits.ker_le_center_of_isQuasisimple hQ hne
  rw [center_Sp8_eq_bot, le_bot_iff] at hker
  exact (MonoidHom.ker_eq_bot_iff _).1 hker

@[expose] noncomputable def bridgeSpEquiv : Sp8 K ≃* adjointGroup TwistTag.D4.tag K :=
  MulEquiv.ofBijective (bridgeC (K := K)) ⟨bridgeC_injective, bridgeC_surjective⟩

@[expose] noncomputable def bridge : Om8 K ≃* adjointGroup TwistTag.D4.tag K :=
  (modelEquiv8 (K := K)).symm.trans bridgeSpEquiv

theorem coe_bridge_X8 {γ : Fin 4 → ℤ} (hγ : γ ∈ rootsD4) (c : K) :
    (bridge (X8 γ c) : ModGL TwistTag.D4.tag K) = pinnedX TwistTag.D4.tag K (bL γ) c := by
  have h : (modelEquiv8 (K := K)).symm (X8 γ c) = xr γ c := by
    rw [MulEquiv.symm_apply_eq, modelEquiv8_apply]
  rw [bridge, MulEquiv.trans_apply, h]
  exact bridgeSp_xr hγ c

theorem twistHom_pinnedX_two (σ : K →+* K) {γ : Fin TwistTag.D4.tag.rank → ℤ}
    (hγ : IsRoot TwistTag.D4.tag γ) (c : K) :
    twistHom TwistTag.D4 K σ (pinnedX TwistTag.D4.tag K γ c) =
      pinnedX TwistTag.D4.tag K (permLattice TwistTag.D4.perm γ) (σ c) := by
  have h2 : (2 : K) = 0 := CharP.cast_eq_zero K 2
  have e : twistHom TwistTag.D4 K σ (pinnedX TwistTag.D4.tag K γ c) =
      twistHom TwistTag.D4 K (RingHom.id K) (pinnedX TwistTag.D4.tag K γ (σ c)) := by
    rw [twistHom_id_eq, twistHom_apply]
    congr 2
    exact Units.ext (entrywise_pinnedX σ γ c)
  rw [e, twistHom_id_pinnedX h2 hγ]

theorem coe_bridge_theta_fieldAutP (σ : K ≃+* K) (x : Om8 K) :
    (bridge (theta (AutOm.fieldAutP 4 σ x)) : ModGL TwistTag.D4.tag K) =
      twistHom TwistTag.D4 K σ.toRingHom (bridge x) := by
  have h : ((adjointGroup TwistTag.D4.tag K).subtype.comp (bridge (K := K)).toMonoidHom).comp
      ((theta * AutOm.fieldAutP 4 σ : MulAut (Om8 K)).toMonoidHom) =
      (twistHom TwistTag.D4 K σ.toRingHom).comp
        ((adjointGroup TwistTag.D4.tag K).subtype.comp (bridge (K := K)).toMonoidHom) := by
    refine ext_X8 fun γ hγ c => ?_
    simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, Subgroup.coe_subtype,
      MulAut.mul_apply]
    rw [fieldAutP_X8 σ hγ, theta_X8 hγ, coe_bridge_X8 (tri_mem_roots hγ), coe_bridge_X8 hγ,
      twistHom_pinnedX_two _ (isRoot_bL hγ), bL_tri]
    rfl
  exact DFunLike.congr_fun h x

end Lift

end TriBridge

end CFSG.StandardType
