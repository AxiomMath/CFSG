module

public import CFSG.LocalAnalysis.StandardType.GGLieKnownR2TriD4BridgeIso
public import CFSG.LocalAnalysis.StandardType.GGLieKnownR2TriD4HighRootParabolic

public section

namespace CFSG.StandardType.LieKnownR2.TriD4.Inner

open CFSG.Open CFSG.StandardType CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Universal
  CFSG.LieType.RootSystem CFSG.LieType.Chevalley CFSG.LieType.Steinberg.Adjoint
  CFSG.LieType.Steinberg.TwistedD4 CFSG.SeitzReduction

private theorem tact_units_map_entrywiseHom_eltUnit
    {K : Type} [Field K] (σ : K →+* K) (α : Root d4) (t : K) :
    Units.map (entrywiseHom σ) ((rootOperatorFamily d4).eltUnit K α t) =
      (rootOperatorFamily d4).eltUnit K α (σ t) := by
  obtain ⟨γ, hγ⟩ := α
  have hs := (rootOperatorFamily d4).pinnedFamilySign_mul_self K γ
  have e1 : ∀ s : K, (rootOperatorFamily d4).eltUnit K ⟨γ, hγ⟩ s =
      pinnedX d4 K γ (((rootOperatorFamily d4).pinnedFamilySign γ : K) * s) := by
    intro s
    rw [(rootOperatorFamily d4).pinnedX_eq_eltUnit K hγ, ← mul_assoc, hs, one_mul]
  refine Units.ext ?_
  rw [Units.coe_map, e1 t, e1 (σ t)]
  change entrywise σ (pinnedX d4 K γ _ : Module.End K (RootModule d4 K)) = _
  rw [entrywise_pinnedX, map_mul, map_intCast]

private theorem tact_twistSign_highRoot
    {K : Type} [Field K] (σ : K →+* K) : twistSign σ (highRoot d4) = 1 := by
  have hθ : IsRoot d4 (highRoot d4) := isRoot_highRoot d4
  have hfix : rho (highRoot d4) = highRoot d4 := by decide
  have hε : twistSign σ (highRoot d4) = 1 ∨ twistSign σ (highRoot d4) = -1 :=
    (twistSign_spec σ hθ).1
  set x : adjointGroup d4 K := xPar (rootOperatorFamily d4) (highRoot d4) (1 : K) with hx
  have h1 := twistC_three_xPar σ hθ (1 : K)
  rw [hfix, hfix] at h1
  have hcoe : ((twistC .D4 K σ (twistC .D4 K σ (twistC .D4 K σ x))) : ModGL d4 K) =
      (twistHom .D4 K σ)^[3] (x : ModGL d4 K) := by
    simp only [coe_twistC]
    rfl
  have h2 : (twistHom .D4 K σ)^[3] (x : ModGL d4 K) = (x : ModGL d4 K) := by
    rw [show (3 : ℕ) = TwistTag.D4.order by decide]
    rw [twistHom_iterate_order]
    rw [show TwistTag.D4.order = 3 by decide]
    rw [hx, xPar_of_isRoot hθ, RootOperatorFamily.coe_eltElement]
    rw [tact_units_map_entrywiseHom_eltUnit (σ ^ 3) ⟨highRoot d4, hθ⟩ 1, map_one]
  have h3 : (xPar (rootOperatorFamily d4) (highRoot d4)
        (twistSign σ (highRoot d4) * twistSign σ (highRoot d4) * twistSign σ (highRoot d4) * 1) :
      adjointGroup d4 K) = xPar (rootOperatorFamily d4) (highRoot d4) 1 := by
    have hval : ((twistC .D4 K σ (twistC .D4 K σ (twistC .D4 K σ x))) : ModGL d4 K) =
        (x : ModGL d4 K) := by
      rw [hcoe, h2]
    rw [h1] at hval
    simp only [map_one] at hval
    rw [hx] at hval
    exact Subtype.ext hval
  have harg : twistSign σ (highRoot d4) * twistSign σ (highRoot d4) *
      twistSign σ (highRoot d4) = 1 := by
    have h' := xPar_injective hθ h3
    simpa using h'
  have hε3 : twistSign σ (highRoot d4) ^ 3 = 1 := by
    calc twistSign σ (highRoot d4) ^ 3
        = twistSign σ (highRoot d4) * twistSign σ (highRoot d4) *
            twistSign σ (highRoot d4) := by ring
      _ = 1 := harg
  rcases hε with h | h
  · exact h
  · rw [h] at hε3 ⊢
    ring_nf at hε3 ⊢
    exact hε3

theorem triD4C0Xtheta_mem
    {K : Type} [Field K] (σ : K →+* K) (t : K) (ht : σ t = t) :
    ((xPar (rootOperatorFamily d4) (highRoot d4) t : adjointGroup d4 K) : ModGL d4 K) ∈
      graphFixedRootGroup TwistTag.D4 K σ := by
  have hθ : IsRoot d4 (highRoot d4) := isRoot_highRoot d4
  refine Subgroup.mem_sup_left (Subgroup.mem_inf.2 ⟨?_, ?_⟩)
  · rw [show posUnipotent d4 K = rootSpan d4 K {α | IsRoot d4 α ∧ 0 < height α} from rfl]
    rw [xPar_of_isRoot hθ]
    exact Subgroup.mem_iSup_of_mem (highRoot d4) (Subgroup.mem_iSup_of_mem
      ⟨hθ, height_highRoot_pos d4⟩
      (Subgroup.mem_subgroupOf.1 (by
        rw [(rootOperatorFamily d4).subgroupOf_rootSubgroup_eq K ⟨highRoot d4, hθ⟩]
        exact (rootOperatorFamily d4).eltElement_mem_rootSubgroup _ t)))
  · rw [coe_mem_twistedFixedGroup_iff]
    rw [twistC_xPar σ hθ t, show rho (highRoot d4) = highRoot d4 by decide,
      tact_twistSign_highRoot σ, one_mul, ht]

@[expose] noncomputable def triD4C0Xtheta
    {K : Type} [Field K] (σ : K ≃+* K) :
    fixedField σ.toRingHom → graphFixedRootGroup TwistTag.D4 K σ.toRingHom :=
  fun t => ⟨xPar (rootOperatorFamily d4) (highRoot d4) (t : K),
    triD4C0Xtheta_mem σ.toRingHom (t : K) (by simpa using t.2)⟩

theorem fieldActor_triD4C0Xtheta
    {K : Type} [Field K] [Finite K] (σ : K ≃+* K) (δ : K ≃+* K)
    (t : fixedField σ.toRingHom) :
    fieldActor (t := TwistTag.D4) σ δ (triD4C0Xtheta σ t) =
      triD4C0Xtheta σ ⟨δ (t : K), by
        change σ (δ (t : K)) = δ (t : K)
        rw [← ringEquiv_comm_of_finite σ δ (t : K)]
        exact congrArg δ (show σ (t : K) = (t : K) from t.2)⟩ := by
  have hθ : IsRoot d4 (highRoot d4) := isRoot_highRoot d4
  apply Subtype.ext
  rw [coe_fieldActor]
  change Units.map (entrywiseHom δ.toRingHom)
      ((xPar (rootOperatorFamily d4) (highRoot d4) (t : K) : adjointGroup d4 K) :
        ModGL d4 K) =
    ((xPar (rootOperatorFamily d4) (highRoot d4) (δ (t : K)) : adjointGroup d4 K) :
      ModGL d4 K)
  rw [xPar_of_isRoot hθ, xPar_of_isRoot hθ]
  exact tact_units_map_entrywiseHom_eltUnit δ.toRingHom ⟨highRoot d4, hθ⟩ (t : K)

theorem triD4_pCore_le_centralizer
    {K : Type} [Field K] [Finite K] [CharP K 2] (σ : K ≃+* K) :
    pCoreOf 2 (Subgroup.normalizer (Bridge.triD4C0HighRoot K σ.toRingHom :
        Set (graphFixedRootGroup TwistTag.D4 K σ.toRingHom))) ≤
      Subgroup.centralizer (Bridge.triD4C0HighRoot K σ.toRingHom :
        Set (graphFixedRootGroup TwistTag.D4 K σ.toRingHom)) := by
  classical
  have hθ : IsRoot d4 (highRoot d4) := isRoot_highRoot d4
  let G : Subgroup (ModGL d4 K) := graphFixedRootGroup TwistTag.D4 K σ.toRingHom
  let H : Subgroup (ModGL d4 K) := rootSubgroup d4 K (highRoot d4) ⊓
    twistedFixedGroup TwistTag.D4 K σ.toRingHom
  let P : Subgroup (ModGL d4 K) := graphFixedParabolic TwistTag.D4 K σ.toRingHom
    ({(0 : Fin 2)} : Set (Fin 2))
  let QA : Subgroup (ModGL d4 K) := graphFixedParabolicRadical TwistTag.D4 K σ.toRingHom
    ({(0 : Fin 2)} : Set (Fin 2))
  have hPG : P ≤ G := graphFixedParabolic_le TwistTag.D4 K σ.toRingHom _
  have hHleG : H ≤ G := by
    have hroot_pos : rootSubgroup d4 K (highRoot d4) ≤ posUnipotent d4 K :=
      le_iSup₂_of_le (highRoot d4) ⟨hθ, height_highRoot_pos d4⟩ le_rfl
    intro x hx
    obtain ⟨hx1, hx2⟩ := Subgroup.mem_inf.1 hx
    exact Subgroup.mem_sup_left (Subgroup.mem_inf.2 ⟨hroot_pos hx1, hx2⟩)
  have hX : Bridge.triD4C0HighRoot K σ.toRingHom = H.subgroupOf G := rfl
  have hN : Subgroup.normalizer (Bridge.triD4C0HighRoot K σ.toRingHom : Set G) =
      P.subgroupOf G := by
    rw [hX, ← Subgroup.subgroupOf_normalizer_eq hHleG]
    have hkey : G ⊓ Subgroup.normalizer (H : Set (ModGL d4 K)) = P :=
      TriD4HighRootParabolic.graphFixedRootGroup_inf_normalizer_highRootFixed_D4 K σ
    ext x
    rw [Subgroup.mem_subgroupOf, Subgroup.mem_subgroupOf]
    constructor
    · intro hx
      have hx' : (x : ModGL d4 K) ∈ G ⊓ Subgroup.normalizer (H : Set (ModGL d4 K)) :=
        ⟨x.2, hx⟩
      rwa [hkey] at hx'
    · intro hx
      have hx' : (x : ModGL d4 K) ∈ G ⊓ Subgroup.normalizer (H : Set (ModGL d4 K)) := by
        rw [hkey]; exact hx
      exact hx'.2
  have hpCore_sub : pCoreOf 2 (P.subgroupOf G) = (pCoreOf 2 P).subgroupOf G := by
    apply Subgroup.map_injective (f := G.subtype) G.subtype_injective
    rw [Subgroup.map_subgroupOf_eq_of_le ((CFSG.LieType.BorelTits.pCoreOf_le 2 P).trans hPG)]
    rw [pCoreOf, Subgroup.map_map]
    rw [show G.subtype.comp (P.subgroupOf G).subtype =
        P.subtype.comp (Subgroup.subgroupOfEquivOfLe hPG).toMonoidHom from by ext x; rfl]
    rw [← Subgroup.map_map]
    rw [CFSG.pCore_map_iso 2 (Subgroup.subgroupOfEquivOfLe hPG)]
    rw [pCoreOf]
  have hcoreP : pCoreOf 2 P = QA := by
    have h := CFSG.StandardType.LieKnownR2.TriD4HighRootParabolic.pCore_graphFixedParabolic_D4 K σ
    rw [ringChar.eq K 2] at h
    exact h
  have hQA : QA ≤ Subgroup.centralizer (H : Set (ModGL d4 K)) := by
    have hQA_pos : QA ≤ posUnipotent d4 K :=
      (graphFixedParabolicRadical_le TwistTag.D4 K σ.toRingHom _).trans (by
        show graphFixedPosUnipotent TwistTag.D4 K σ.toRingHom ≤ posUnipotent d4 K
        exact inf_le_left)
    have hQA_root : QA ≤ Subgroup.centralizer
        (rootSubgroup d4 K (highRoot d4) : Set (ModGL d4 K)) := by
      rw [Subgroup.le_centralizer_iff]
      refine (Subgroup.closure_le _).2 ?_
      rintro _ ⟨b, rfl⟩
      change pinnedX d4 K (highRoot d4) b ∈ Subgroup.centralizer (QA : Set (ModGL d4 K))
      rw [Subgroup.mem_centralizer_iff]
      intro q hq
      exact (CFSG.StandardType.RootCentExc.commute_of_mem_posUnipotent
        (CFSG.HardMathSupport.Foote.Coordinator.SplitFrame.Heis.isMaxHeight_highRoot d4)
        (hQA_pos hq) b).eq
    exact hQA_root.trans (Subgroup.centralizer_le inf_le_left)
  rw [hN, hpCore_sub, hcoreP, hX]
  intro x hx
  rw [Subgroup.mem_centralizer_iff]
  intro y hy
  apply Subtype.ext
  have hx' : (x : ModGL d4 K) ∈ QA := Subgroup.mem_subgroupOf.mp hx
  have hy' : (y : ModGL d4 K) ∈ H := Subgroup.mem_subgroupOf.mp hy
  simpa only [Subgroup.coe_mul] using
    (Subgroup.mem_centralizer_iff.mp (hQA hx') (y : ModGL d4 K) hy')

end CFSG.StandardType.LieKnownR2.TriD4.Inner
