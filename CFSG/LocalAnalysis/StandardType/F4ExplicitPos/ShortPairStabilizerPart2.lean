module

public import CFSG.LieType.AlgebraicGroups.ConvolutionPoints
public import CFSG.LocalAnalysis.StandardType.F4ExplicitPos.ShortPairStabilizerPart1

@[expose] public section

public noncomputable section

namespace CFSG.StandardType.F4ExplicitPos.ShortPairStabilizer
open CFSG CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType CFSG.LieType.Chevalley
  CFSG.LieType.Steinberg.Adjoint CFSG.SeitzReduction CFSG.LieType.AlgebraicGroups WithConv
  CFSG.LieType.Ree.ReeTag
open scoped CFSG.ConvolutionPoints
open CFSG.HardMathSupport.Foote.Coordinator.SplitFrame.Heis
open CFSG.StandardType.F4ExplicitPos.BruhatNo117 CFSG.StandardType.F4ExplicitPos.UnipotentNo117
open CFSG.StandardType.F4ExplicitPos.PairNormalizerNo117
open CFSG.StandardType.F4ExplicitPos.PairStabilizerNative
open CFSG.StandardType.F4ExplicitPos.B3Algebraic
open scoped Pointwise
variable (Ω : Type) [Field Ω] [CharP Ω 2] [Algebra (ZMod 2) Ω] [Algebra.IsAlgebraic (ZMod 2) Ω]

theorem KshortA_eq_MstarA :
    KshortA Ω = MstarA Ω := by
  let e : A Ω ≃* A Ω := MulEquiv.ofBijective sigmaA (sigmaΩ_bijective Ω)
  have he : e.toMonoidHom = sigmaΩ Ω := rfl
  have hKl : KlongA Ω = Subgroup.normalizer (UA Ω (highRoot Tag.F4)) ⊓
      Subgroup.normalizer (UA Ω (-highRoot Tag.F4)) := rfl
  have hKs : KshortA Ω = Subgroup.normalizer (UA Ω (δ)) ⊓
      Subgroup.normalizer (UA Ω (-δ)) := rfl
  have hmap : (KlongA Ω).map e.toMonoidHom = KshortA Ω := by
    rw [hKl, hKs, Subgroup.map_inf _ _ e.toMonoidHom e.injective,
      Subgroup.map_equiv_normalizer_eq (UA Ω (highRoot Tag.F4)) e,
      Subgroup.map_equiv_normalizer_eq (UA Ω (-highRoot Tag.F4)) e]
    have h1 : (UA Ω (highRoot Tag.F4)).map e.toMonoidHom = UA Ω δ := by
      rw [he]; exact UA_map_sigma Ω (isRoot_highRoot Tag.F4)
    have h2 : (UA Ω (-highRoot Tag.F4)).map e.toMonoidHom = UA Ω (-δ) := by
      rw [he, UA_map_sigma Ω (IsRoot.neg (isRoot_highRoot Tag.F4))]
      congr 1
      show F4.dualRoot (-highRoot Tag.F4) = -F4.dualRoot (highRoot Tag.F4)
      exact CFSG.SeitzReduction.F4Pilot.dualRoot_neg (t := .F4) (isRoot_highRoot Tag.F4)
    rw [h1, h2]
  have hM : (KlongA Ω).map e.toMonoidHom = MstarA Ω := by
    rw [KlongA_eq_LA, he, LA_map_sigma]
  rw [← hmap, hM]

theorem f4_short_pair_stabilizer_eq :
    adjointGroup Tag.F4 Ω ⊓
        Subgroup.normalizer (rootSubgroup Tag.F4 Ω (δ) : Set (ModGL Tag.F4 Ω)) ⊓
        Subgroup.normalizer (rootSubgroup Tag.F4 Ω (-δ) : Set (ModGL Tag.F4 Ω)) =
      Mstar Ω := by
  have h := congrArg (fun H : Subgroup (A Ω) => H.map (A Ω).subtype)
    (KshortA_eq_MstarA Ω)
  rw [Subgroup.map_inf _ _ (A Ω).subtype (A Ω).subtype_injective,
    normalizer_UA_map_incl Ω δ, normalizer_UA_map_incl Ω (-δ), MstarA_map_incl Ω] at h
  rw [← h]
  ac_rfl

theorem f4_isConnectedAlgebraicSubgroup_shortPairStabilizer
    [IsAlgClosed Ω] :
    IsConnectedAlgebraicSubgroup Ω
      ((adjointGroup Tag.F4 Ω ⊓
        Subgroup.normalizer (rootSubgroup Tag.F4 Ω (δ) : Set (ModGL Tag.F4 Ω)) ⊓
        Subgroup.normalizer (rootSubgroup Tag.F4 Ω (-δ) : Set (ModGL Tag.F4 Ω))).map
          (modGLPoint Tag.F4 Ω).toMonoidHom) := by
  rw [f4_short_pair_stabilizer_eq]
  exact ConnectedJoint.isConnectedAlgebraicSubgroup_torus_sup_rootSpan_no117
    (τ := Tag.F4) (k := Ω) (Sstar)

theorem f4_map_entrywiseFrobGL_torus_sup_rootSpan_le
    [IsAlgClosed Ω]
    (p : ℕ) [Fact p.Prime] [CharP Ω p] (e : ℕ) (S : Set (Fin Tag.F4.rank → ℤ)) :
    ((torusGroup Tag.F4 Ω ⊔ rootSpan Tag.F4 Ω S).map
        (entrywiseFrobGL Tag.F4 Ω p e)) ≤ torusGroup Tag.F4 Ω ⊔ rootSpan Tag.F4 Ω S := by
  rw [Subgroup.map_sup, map_entrywiseFrobGL_torusGroup (τ := Tag.F4) (k := Ω) (p := p) e]
  refine sup_le le_sup_left ?_
  have hroot : ∀ α ∈ S,
      (rootSubgroup Tag.F4 Ω α).map (entrywiseFrobGL Tag.F4 Ω p e) ≤
        rootSubgroup Tag.F4 Ω α := by
    intro α _
    rw [Subgroup.map_le_iff_le_comap]
    refine (Subgroup.closure_le _).2 ?_
    rintro _ ⟨c, rfl⟩
    change entrywiseFrobGL Tag.F4 Ω p e (pinnedX Tag.F4 Ω α c) ∈
      rootSubgroup Tag.F4 Ω α
    rw [LangPosition.entrywiseFrobGL_pinnedX_no117 (τ := Tag.F4) (k := Ω) p e α c]
    exact Subgroup.subset_closure ⟨iterateFrobenius Ω p e c, rfl⟩
  rw [rootSpan, Subgroup.map_iSup]
  refine iSup_le fun α => ?_
  rw [Subgroup.map_iSup]
  refine iSup_le fun hα => ?_
  exact le_trans (hroot α hα)
    (le_trans (le_iSup₂_of_le α hα le_rfl) le_sup_right)

end CFSG.StandardType.F4ExplicitPos.ShortPairStabilizer

end

end
