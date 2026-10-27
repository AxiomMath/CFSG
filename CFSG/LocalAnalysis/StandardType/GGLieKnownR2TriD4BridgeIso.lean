module

public import CFSG.HardMathSupport.Timmesfeld.CrossChar.TrialityA2TwoToral
public import CFSG.LocalAnalysis.SeitzReduction.LongRootPairsRoots

public section

namespace CFSG.StandardType.LieKnownR2.TriD4.Bridge

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Steinberg
  CFSG.LieType.Steinberg.Adjoint CFSG.LieType.Steinberg.TwistedD4 CFSG.SeitzReduction
  CFSG.HardMathSupport.Timmesfeld.CrossChar

@[expose] noncomputable def triD4C0HighRoot
    (K : Type) [Field K] (σ : K →+* K) :
    Subgroup (graphFixedRootGroup TwistTag.D4 K σ) :=
  (rootSubgroup TwistTag.D4.tag K (highRoot TwistTag.D4.tag) ⊓
      twistedFixedGroup TwistTag.D4 K σ).subgroupOf
    (graphFixedRootGroup TwistTag.D4 K σ)

@[expose] noncomputable def triD4BridgeEquiv
    {K : Type} [Field K] [Finite K] (σ : K →+* K) {f : ℕ} (hf : 1 ≤ f)
    (hK : Nat.card K = (2 ^ f) ^ 3) (hσ : ∀ c, σ c = c ^ (2 ^ f)) :
    twistedGroup σ ≃* graphFixedRootGroup TwistTag.D4 K σ := by
  have hσsurj : Function.Surjective σ := Finite.surjective_of_injective σ.injective
  let σ' : K ≃+* K := RingEquiv.ofBijective σ ⟨σ.injective, hσsurj⟩
  have hσ' : σ'.toRingHom = σ := rfl
  have hσ'' : ∀ c, σ' c = c ^ (2 ^ f) := by
    intro c
    rw [show σ' c = σ c from rfl]
    exact hσ c
  have hbridge := map_twistedGroup_eq_graphFixedRootGroup_two hf hK σ' hσ''
  rw [hσ'] at hbridge
  exact (Subgroup.equivMapOfInjective (twistedGroup σ) (adjointGroup d4 K).subtype
      Subtype.val_injective).trans (MulEquiv.subgroupCongr hbridge)

theorem triD4BridgeEquiv_coe
    {K : Type} [Field K] [Finite K] (σ : K →+* K) {f : ℕ} (hf : 1 ≤ f)
    (hK : Nat.card K = (2 ^ f) ^ 3) (hσ : ∀ c, σ c = c ^ (2 ^ f))
    (g : twistedGroup σ) :
    ((triD4BridgeEquiv σ hf hK hσ g : graphFixedRootGroup TwistTag.D4 K σ) : ModGL d4 K) =
      ((g : adjointGroup d4 K) : ModGL d4 K) := by
  rfl

private theorem tbridge_map_subtype_rootGroup
    {τ : Tag} {K : Type} [Field K]
    (F : RootOperatorFamily τ) {δ : Fin τ.rank → ℤ} (hδ : IsRoot τ δ) :
    (rootGroup F K δ).map (adjointGroup τ K).subtype = rootSubgroup τ K δ := by
  rw [rootGroup_of_isRoot hδ, ← F.subgroupOf_rootSubgroup_eq K ⟨δ, hδ⟩,
    Subgroup.subgroupOf_map_subtype, inf_of_le_left (rootSubgroup_le_adjointGroup δ)]

private theorem tbridge_twistedRootSubgroupD4_highRoot
    {K : Type} [Field K] (σ : K →+* K) (hσ : ∀ c, σ (σ (σ c)) = c) :
    (twistedRootSubgroupD4 σ (highRoot .G2)).map (adjointGroup d4 K).subtype =
      rootSubgroup d4 K (highRoot d4) ⊓ twistedFixedGroup TwistTag.D4 K σ := by
  have hθ : IsRoot d4 (highRoot d4) := isRoot_highRoot d4
  have hproj : proj (highRoot d4) = (highRoot .G2 : Fin (Tag.rank .G2) → ℤ) := by
    decide +kernel
  have hfix : rho (highRoot d4) = (highRoot d4 : Fin d4.rank → ℤ) := by
    ext j
    fin_cases j <;> rfl
  have hsign : twistSign σ (highRoot d4) = 1 := twistSign_of_rho_eq σ hσ hθ hfix
  ext y
  simp only [Subgroup.mem_map, Subgroup.mem_inf]
  constructor
  · rintro ⟨g, hg, rfl⟩
    obtain ⟨c, hc, rfl⟩ :=
      (mem_twistedRootSubgroupD4_iff_of_fixed (σ := σ) hσ hθ hproj hfix g).1 hg
    constructor
    · rw [← tbridge_map_subtype_rootGroup (rootOperatorFamily d4) (K := K) hθ]
      exact Subgroup.mem_map_of_mem _ (xPar_mem hθ c)
    · rw [mem_twistedFixedGroup_iff_twistHom]
      refine ⟨(xPar (rootOperatorFamily d4) (highRoot d4) c).2, ?_⟩
      have hfix2 : twistC .D4 K σ (xPar (rootOperatorFamily d4) (highRoot d4) c) =
          xPar (rootOperatorFamily d4) (highRoot d4) c := by
        rw [twistC_xPar σ hθ, hfix, hsign, one_mul, hc]
      calc (twistHom TwistTag.D4 K σ)
            ((adjointGroup d4 K).subtype (xPar (rootOperatorFamily d4) (highRoot d4) c))
          = ((twistC .D4 K σ (xPar (rootOperatorFamily d4) (highRoot d4) c) :
              adjointGroup d4 K) : ModGL d4 K) :=
            (coe_twistC .D4 K σ (xPar (rootOperatorFamily d4) (highRoot d4) c)).symm
        _ = (adjointGroup d4 K).subtype (xPar (rootOperatorFamily d4) (highRoot d4) c) :=
            congrArg Subtype.val hfix2
  · rintro ⟨h1, h2⟩
    rw [← tbridge_map_subtype_rootGroup (rootOperatorFamily d4) (K := K) hθ] at h1
    obtain ⟨x, hx, rfl⟩ := h1
    obtain ⟨c, rfl⟩ := (mem_rootGroup_iff hθ x).1 hx
    rw [mem_twistedFixedGroup_iff_twistHom] at h2
    have hc : σ c = c := by
      have hfix' : twistC .D4 K σ (xPar (rootOperatorFamily d4) (highRoot d4) c) =
          xPar (rootOperatorFamily d4) (highRoot d4) c := by
        apply Subtype.ext
        rw [coe_twistC]
        exact h2.2
      rw [twistC_xPar σ hθ, hfix, hsign, one_mul] at hfix'
      exact xPar_injective hθ hfix'
    exact ⟨xPar (rootOperatorFamily d4) (highRoot d4) c,
      (mem_twistedRootSubgroupD4_iff_of_fixed (σ := σ) hσ hθ hproj hfix _).2 ⟨c, hc, rfl⟩, rfl⟩

theorem triD4BridgeEquiv_twistedRootGroup_highRoot
    {K : Type} [Field K] [Finite K] (σ : K →+* K) {f : ℕ} (hf : 1 ≤ f)
    (hK : Nat.card K = (2 ^ f) ^ 3) (hσ : ∀ c, σ c = c ^ (2 ^ f)) :
    ((twistedDatum σ).rootGroup (highRoot .G2)).map
        (triD4BridgeEquiv σ hf hK hσ).toMonoidHom =
      triD4C0HighRoot K σ := by
  have hσ3 : ∀ c, σ (σ (σ c)) = c := by
    intro c
    have : Fintype K := Fintype.ofFinite K
    rw [hσ, hσ, hσ, ← pow_mul, ← pow_mul]
    rw [show (2 ^ f) * ((2 ^ f) * (2 ^ f)) = Nat.card K by
      rw [hK]; ring, Nat.card_eq_fintype_card]
    exact FiniteField.pow_card c
  have hkey := tbridge_twistedRootSubgroupD4_highRoot (K := K) σ hσ3
  have hθ : IsRoot d4 (highRoot d4) := isRoot_highRoot d4
  have hCsub : graphFixedRootGroup TwistTag.D4 K σ ≤ twistedFixedGroup TwistTag.D4 K σ :=
    graphFixedRootGroup_le TwistTag.D4 K σ
  have hσsurj : Function.Surjective σ := Finite.surjective_of_injective σ.injective
  let σ' : K ≃+* K := RingEquiv.ofBijective σ ⟨σ.injective, hσsurj⟩
  have hσ' : σ'.toRingHom = σ := rfl
  have hσ'' : ∀ c, σ' c = c ^ (2 ^ f) := by
    intro c
    rw [show σ' c = σ c from rfl]
    exact hσ c
  have hgraph := map_twistedGroup_eq_graphFixedRootGroup_two hf hK σ' hσ''
  rw [hσ'] at hgraph
  have hle_graph : (twistedRootSubgroupD4 σ (highRoot .G2)).map
      (adjointGroup d4 K).subtype ≤ graphFixedRootGroup TwistTag.D4 K σ :=
    (Subgroup.map_mono (twistedRootSubgroupD4_le_twistedGroup σ (isRoot_highRoot .G2))).trans
      (le_of_eq hgraph)
  have hL : ((twistedRootGroup σ (highRoot .G2)).map
        (triD4BridgeEquiv σ hf hK hσ).toMonoidHom).map
        (graphFixedRootGroup TwistTag.D4 K σ).subtype =
      rootSubgroup d4 K (highRoot d4) ⊓ twistedFixedGroup TwistTag.D4 K σ := by
    rw [Subgroup.map_map]
    have hfun : ((graphFixedRootGroup TwistTag.D4 K σ).subtype).comp
        (triD4BridgeEquiv σ hf hK hσ).toMonoidHom =
        ((adjointGroup d4 K).subtype).comp (twistedGroup σ).subtype :=
      MonoidHom.ext fun g => triD4BridgeEquiv_coe σ hf hK hσ g
    rw [hfun, ← Subgroup.map_map]
    change (((twistedRootSubgroupD4 σ (highRoot .G2)).subgroupOf (twistedGroup σ)).map
        (twistedGroup σ).subtype).map (adjointGroup d4 K).subtype =
      rootSubgroup d4 K (highRoot d4) ⊓ twistedFixedGroup TwistTag.D4 K σ
    rw [Subgroup.subgroupOf_map_subtype,
      inf_of_le_left (twistedRootSubgroupD4_le_twistedGroup σ (isRoot_highRoot .G2))]
    exact hkey
  change ((twistedRootGroup σ (highRoot .G2)).map
      (triD4BridgeEquiv σ hf hK hσ).toMonoidHom) = triD4C0HighRoot K σ
  refine Subgroup.map_injective (f := (graphFixedRootGroup TwistTag.D4 K σ).subtype)
    Subtype.val_injective ?_
  rw [hL]
  change _ = ((rootSubgroup d4 K (highRoot d4) ⊓ twistedFixedGroup TwistTag.D4 K σ).subgroupOf
    (graphFixedRootGroup TwistTag.D4 K σ)).map (graphFixedRootGroup TwistTag.D4 K σ).subtype
  rw [Subgroup.subgroupOf_map_subtype]
  refine le_antisymm ?_ inf_le_left
  refine le_inf le_rfl ?_
  rw [← hkey]
  exact hle_graph

end CFSG.StandardType.LieKnownR2.TriD4.Bridge
