module

public import CFSG.LocalAnalysis.SeitzReduction.TwistedE6PilotQ2SwapRowInput
public import CFSG.LocalAnalysis.SeitzReduction.HypothesisOneTwistedE6ClassListBasic
public import CFSG.LocalAnalysis.SeitzReduction.HypothesisOneTwistedE6ClassesBasic
public import CFSG.LocalAnalysis.SeitzReduction.HypothesisOneTwistedE6ClassesReps

public section

set_option linter.unusedSectionVars false

namespace CFSG.SeitzReduction.TwistedE6Pilot

open Subgroup CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LieType.Steinberg.Adjoint
open CFSG.Quasithin (perfectCore map_perfectCore)
open scoped commutatorElement

local instance triRootsNeZeroE6 : NeZero TwistTag.E6.tag.rank := ⟨by decide⟩

local instance triRootsNeZeroFolded : NeZero TwistTag.E6.foldedTag.rank := ⟨by decide⟩

section Groups

variable {G : Type*} [Group G]

theorem map_centralizer_tri {G' : Type*} [Group G'] (e : G ≃* G') (J : Subgroup G) :
    (centralizer (J : Set G)).map e.toMonoidHom =
      centralizer ((J.map e.toMonoidHom : Subgroup G') : Set G') := by
  refine le_antisymm ?_ fun x hx => ?_
  · rintro _ ⟨y, hy, rfl⟩ _ ⟨h, hh, rfl⟩
    rw [← map_mul, ← map_mul, hy h hh]
  · refine ⟨e.symm x, fun h hh => e.injective ?_, e.apply_symm_apply x⟩
    rw [map_mul, map_mul, e.apply_symm_apply]
    exact hx (e h) ⟨h, hh, rfl⟩

theorem perfectCore_map_inf_centralizer_tri [Finite G] (e : G ≃* G) (H Y : Subgroup G) :
    perfectCore (H.map e.toMonoidHom ⊓ centralizer (Y.map e.toMonoidHom : Set G)) =
      (perfectCore (H ⊓ centralizer (Y : Set G))).map e.toMonoidHom := by
  rw [← map_centralizer_tri, ← map_inf _ _ _ e.injective, map_perfectCore]

theorem isSimpleGroup_map_tri {G' : Type*} [Group G'] {P : Subgroup G} (hP : IsSimpleGroup P)
    {f : G →* G'} (hf : Function.Injective f) : IsSimpleGroup (P.map f) := by
  have := hP
  exact (equivMapOfInjective P f hf).symm.isSimpleGroup

theorem commute_of_commute_conj_tri {g x y : G} (h : Commute (g * x * g⁻¹) (g * y * g⁻¹)) :
    Commute x y := by
  have e : g * (x * y) * g⁻¹ = g * (y * x) * g⁻¹ := by
    calc g * (x * y) * g⁻¹ = g * x * g⁻¹ * (g * y * g⁻¹) := by group
      _ = g * y * g⁻¹ * (g * x * g⁻¹) := h.eq
      _ = g * (y * x) * g⁻¹ := by group
  exact mul_left_cancel (mul_right_cancel e)

theorem commutatorElement_mem_tri {H : Subgroup G} {x y : G} (hx : x ∈ H) (hy : y ∈ H) :
    ⁅x, y⁆ ∈ H := by
  rw [commutatorElement_def]
  exact mul_mem (mul_mem (mul_mem hx hy) (inv_mem hx)) (inv_mem hy)

end Groups

@[expose] def triWord2 : List (Fin TwistTag.E6.foldedTag.rank) := [3, 1, 2, 0, 1, 2, 3]

@[expose] def triWord3 : List (Fin TwistTag.E6.foldedTag.rank) := [3, 2, 0, 1, 2, 3]

@[expose] def triRootA4 : Fin TwistTag.E6.tag.rank → ℤ := ![0, 0, 0, 1, 0, 0]

@[expose] def triRootG3 : Fin TwistTag.E6.tag.rank → ℤ := ![0, 0, 1, 1, 1, 0]

@[expose] def triRootEps : Fin TwistTag.E6.tag.rank → ℤ := ![1, 0, 1, 1, 1, 1]

@[expose] def triRootA1 : Fin TwistTag.E6.tag.rank → ℤ := ![1, 0, 0, 0, 0, 0]

@[expose] def triRootA6 : Fin TwistTag.E6.tag.rank → ℤ := ![0, 0, 0, 0, 0, 1]

@[expose] def triRootB234 : Fin TwistTag.E6.tag.rank → ℤ := ![0, 1, 1, 1, 0, 0]

@[expose] def triRootB245 : Fin TwistTag.E6.tag.rank → ℤ := ![0, 1, 0, 1, 1, 0]

theorem triTransport_check :
    (twistedE6RelAct triWord2 e6HighestRoot = triRootA4 ∧
      twistedE6RelAct triWord2 (-e6HighestRoot) = -triRootA4) ∧
    (twistedE6RelAct triWord3 e6HighestRoot = triRootG3 ∧
      twistedE6RelAct triWord3 (-e6HighestRoot) = -triRootG3) ∧
    (twistedE6RelAct triWord2 triRootEps = e6HighestRoot ∧
      twistedE6RelAct triWord2 (-triRootEps) = -e6HighestRoot) ∧
    (twistedE6RelAct triWord3 triRootEps = e6HighestRoot ∧
      twistedE6RelAct triWord3 (-triRootEps) = -e6HighestRoot) ∧
    (twistedE6RelAct triWord2 triRootA4 = triRootG3 ∧
      twistedE6RelAct triWord2 (-triRootA4) = -triRootG3) ∧
    (twistedE6RelAct triWord2 triRootG3 = triRootEps ∧
      twistedE6RelAct triWord2 (-triRootG3) = -triRootEps) ∧
    (twistedE6RelAct triWord3 triRootA4 = triRootA4 ∧
      twistedE6RelAct triWord3 (-triRootA4) = -triRootA4) ∧
    (twistedE6RelAct triWord2 triRootA6 = triRootB234 ∧
      twistedE6RelAct triWord2 (-triRootA6) = -triRootB234) ∧
    (twistedE6RelAct triWord2 triRootA1 = triRootB245 ∧
      twistedE6RelAct triWord2 (-triRootA1) = -triRootB245) := by
  decide +kernel

theorem triRoots_check :
    triRootA4 ∈ perpFixedRoots ∧ triRootG3 ∈ perpFixedRoots ∧
    permLattice TwistTag.E6.perm triRootA4 = triRootA4 ∧
    permLattice TwistTag.E6.perm triRootG3 = triRootG3 ∧
    permLattice TwistTag.E6.perm triRootEps = triRootEps ∧
    triRootA4 1 = 0 ∧ triRootG3 1 = 0 ∧ triRootEps 1 = 0 ∧
    permLattice TwistTag.E6.perm triRootA6 = triRootA1 ∧
    permLattice TwistTag.E6.perm triRootB234 = triRootB245 ∧
    triRootA4 = Pi.single 3 1 := by
  decide +kernel

theorem isRoot_of_triRootB {v : Fin TwistTag.E6.tag.rank → ℤ}
    (h : twistedE6TwoRootB v = true) : IsRoot TwistTag.E6.tag v :=
  isRoot_iff_twistedE6TwoRootB.2 h

theorem triIsRoot_check :
    twistedE6TwoRootB triRootA4 = true ∧ twistedE6TwoRootB triRootG3 = true ∧
    twistedE6TwoRootB triRootEps = true ∧ twistedE6TwoRootB triRootA1 = true ∧
    twistedE6TwoRootB triRootA6 = true := by
  decide +kernel

@[expose] def triOverlapB (δ β : Fin TwistTag.E6.tag.rank → ℤ) : Bool :=
  twistedE6TwoRootB β && decide (iform e6HighestRoot β = 0) && decide (iform δ β = 0)

@[expose] def triPairB (δ ε γ : Fin TwistTag.E6.tag.rank → ℤ) : Bool :=
  twistedE6TwoVecB (δ + ε) γ && twistedE6TwoRootB δ && twistedE6TwoRootB ε &&
    twistedE6TwoRootB (δ + ε) && !twistedE6TwoVecB δ ε &&
    !twistedE6TwoRootB (δ + permLattice TwistTag.E6.perm ε) &&
    !twistedE6TwoVecB (δ + permLattice TwistTag.E6.perm ε) 0 &&
    !twistedE6TwoRootB (permLattice TwistTag.E6.perm (δ + ε) + δ) &&
    !twistedE6TwoVecB (permLattice TwistTag.E6.perm (δ + ε) + δ) 0 &&
    !twistedE6TwoRootB (permLattice TwistTag.E6.perm (δ + ε) + ε) &&
    !twistedE6TwoVecB (permLattice TwistTag.E6.perm (δ + ε) + ε) 0

@[expose] def triFixedB (δ ε γ : Fin TwistTag.E6.tag.rank → ℤ) : Bool :=
  twistedE6TwoVecB (δ + ε) γ && twistedE6TwoRootB δ && twistedE6TwoRootB ε &&
    twistedE6TwoRootB (δ + ε) &&
    twistedE6TwoVecB (permLattice TwistTag.E6.perm (δ + ε)) (δ + ε) && !twistedE6TwoVecB δ ε &&
    !twistedE6TwoRootB (δ + permLattice TwistTag.E6.perm ε) &&
    !twistedE6TwoVecB (δ + permLattice TwistTag.E6.perm ε) 0 &&
    !twistedE6TwoVecB δ (permLattice TwistTag.E6.perm ε) &&
    !twistedE6TwoRootB (δ + ε + δ) && !twistedE6TwoRootB (δ + ε + ε) &&
    !twistedE6TwoVecB (δ + ε) (-δ) && !twistedE6TwoVecB (δ + ε) (-ε)

variable {K : Type} [Field K]


theorem commutator_twistedE6PairX_of_triPairB [CharP K 2] (σ : K →+* K)
    {δ ε γ : Fin TwistTag.E6.tag.rank → ℤ} (h : triPairB δ ε γ = true) (s u : K) :
    ⁅twistedE6PairX σ δ s, twistedE6PairX σ ε u⁆ = twistedE6PairX σ γ (s * u) := by
  simp only [triPairB, Bool.and_eq_true, Bool.not_eq_true', Bool.eq_false_iff, ne_eq,
    twistedE6TwoVecB_iff, ← isRoot_iff_twistedE6TwoRootB, and_assoc] at h
  obtain ⟨rfl, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10⟩ := h
  exact commutator_twistedE6PairX_pairSum σ h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 s u

theorem commutator_twistedE6PairX_of_triFixedB [CharP K 2] (σ : K →+* K)
    {δ ε γ : Fin TwistTag.E6.tag.rank → ℤ} (h : triFixedB δ ε γ = true) (s u : K) :
    ⁅twistedE6PairX σ δ s, twistedE6PairX σ ε u⁆ =
      pinnedX TwistTag.E6.tag K γ (s * u + σ (s * u)) := by
  simp only [triFixedB, Bool.and_eq_true, Bool.not_eq_true', Bool.eq_false_iff, ne_eq,
    twistedE6TwoVecB_iff, ← isRoot_iff_twistedE6TwoRootB, and_assoc] at h
  obtain ⟨rfl, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12⟩ := h
  exact commutator_twistedE6PairX σ h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 s u

@[expose] def TriOverlapRoots (σ : K →+* K) (δ : Fin TwistTag.E6.tag.rank → ℤ)
    (O : Subgroup (ModGL TwistTag.E6.tag K)) : Prop :=
  ∀ β : Fin TwistTag.E6.tag.rank → ℤ, IsRoot TwistTag.E6.tag β →
    iform e6HighestRoot β = 0 → iform δ β = 0 →
      (permLattice TwistTag.E6.perm β = β → ∀ s : K, σ s = s →
        pinnedX TwistTag.E6.tag K β s ∈ O) ∧
      (permLattice TwistTag.E6.perm β ≠ β → ∀ s : K, twistedE6PairX σ β s ∈ O)

theorem pinnedX_mem_of_triOverlapB {σ : K →+* K} {δ : Fin TwistTag.E6.tag.rank → ℤ}
    {O : Subgroup (ModGL TwistTag.E6.tag K)} (hO : TriOverlapRoots σ δ O)
    {β : Fin TwistTag.E6.tag.rank → ℤ} (h : triOverlapB δ β = true)
    (hρ : permLattice TwistTag.E6.perm β = β) {s : K} (hs : σ s = s) :
    pinnedX TwistTag.E6.tag K β s ∈ O := by
  simp only [triOverlapB, Bool.and_eq_true, decide_eq_true_eq] at h
  exact (hO β (isRoot_of_triRootB h.1.1) h.1.2 h.2).1 hρ s hs

theorem twistedE6PairX_mem_of_triOverlapB {σ : K →+* K} {δ : Fin TwistTag.E6.tag.rank → ℤ}
    {O : Subgroup (ModGL TwistTag.E6.tag K)} (hO : TriOverlapRoots σ δ O)
    {β : Fin TwistTag.E6.tag.rank → ℤ} (h : triOverlapB δ β = true)
    (hρ : permLattice TwistTag.E6.perm β ≠ β) (s : K) :
    twistedE6PairX σ β s ∈ O := by
  simp only [triOverlapB, Bool.and_eq_true, decide_eq_true_eq] at h
  exact (hO β (isRoot_of_triRootB h.1.1) h.1.2 h.2).2 hρ s

section Transport

variable {k : Type} [Field k]

theorem thetaRankOneGroup_eq_rootRankOneGroup_tri (ι : k →+* K) :
    E6GraphLevi.thetaRankOneGroup ι = TwistedE6Pilot.rootRankOneGroup ι e6HighestRoot :=
  rfl

theorem map_conj_rootRankOneGroup_tri [CharP K 2] (ι : k →+* K)
    (ω : List (Fin TwistTag.E6.foldedTag.rank)) {β β' : Fin TwistTag.E6.tag.rank → ℤ}
    (hβ : IsRoot TwistTag.E6.tag β) (h₁ : twistedE6RelAct ω β = β')
    (h₂ : twistedE6RelAct ω (-β) = -β') :
    (TwistedE6Pilot.rootRankOneGroup ι β).map
        (MulAut.conj (twistedE6RelWeyl K ω)).toMonoidHom =
      TwistedE6Pilot.rootRankOneGroup ι β' := by
  have e₁ : ⇑(MulAut.conj (twistedE6RelWeyl K ω)).toMonoidHom ∘
      (fun c : k => pinnedX TwistTag.E6.tag K β (ι c)) =
        fun c : k => pinnedX TwistTag.E6.tag K β' (ι c) := by
    funext c
    simp only [Function.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    rw [twistedE6RelWeyl_conj_pinnedX ω hβ, h₁]
  have e₂ : ⇑(MulAut.conj (twistedE6RelWeyl K ω)).toMonoidHom ∘
      (fun c : k => pinnedX TwistTag.E6.tag K (-β) (ι c)) =
        fun c : k => pinnedX TwistTag.E6.tag K (-β') (ι c) := by
    funext c
    simp only [Function.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    rw [twistedE6RelWeyl_conj_pinnedX ω (CFSG.LieType.Chevalley.IsRoot.neg hβ), h₂]
  rw [TwistedE6Pilot.rootRankOneGroup, TwistedE6Pilot.rootRankOneGroup, Subgroup.map_sup,
    MonoidHom.map_closure, MonoidHom.map_closure, ← Set.range_comp, ← Set.range_comp, e₁, e₂]

theorem pinnedX_mem_subsystemGroup_setA_tri {γ : Fin TwistTag.E6.tag.rank → ℤ}
    (hγ : IsRoot TwistTag.E6.tag γ) (h1 : γ 1 = 0) (c : K) :
    pinnedX TwistTag.E6.tag K γ c ∈ subsystemGroup TwistTag.E6.tag K E6GraphLevi.setA := by
  rw [subsystemGroup_eq_rootSpan]
  have hmem : γ ∈ parabolicRoots TwistTag.E6.tag E6GraphLevi.setA := by
    refine ⟨hγ, fun i hi => ?_⟩
    have hi1 : i = 1 := by
      by_contra h
      exact hi h
    rw [hi1]
    exact h1
  exact pinnedX_mem_rootSpan hmem c

theorem rootRankOneGroup_le_su6Levi_tri [CharP K 2] {ι : k →+* K} {σ : K →+* K}
    (hι : ∀ c, σ (ι c) = ι c) {δ : Fin TwistTag.E6.tag.rank → ℤ}
    (hδ : IsRoot TwistTag.E6.tag δ) (h1 : δ 1 = 0) (hρ : permLattice TwistTag.E6.perm δ = δ) :
    TwistedE6Pilot.rootRankOneGroup ι δ ≤ su6Levi σ := by
  have hδ' := CFSG.LieType.Chevalley.IsRoot.neg hδ
  have hρ' : permLattice TwistTag.E6.perm (-δ) = -δ := by
    rw [show permLattice TwistTag.E6.perm (-δ) = -permLattice TwistTag.E6.perm δ from rfl, hρ]
  have h1' : (-δ) 1 = 0 := by rw [Pi.neg_apply, h1, neg_zero]
  refine sup_le ((closure_le _).2 ?_) ((closure_le _).2 ?_)
  · rintro _ ⟨c, rfl⟩
    exact ⟨pinnedX_mem_subsystemGroup_setA_tri hδ h1 _,
      pinnedX_mem_graphFixedRootGroup_of_fixed σ hδ hρ (hι c)⟩
  · rintro _ ⟨c, rfl⟩
    exact ⟨pinnedX_mem_subsystemGroup_setA_tri hδ' h1' _,
      pinnedX_mem_graphFixedRootGroup_of_fixed σ hδ' hρ' (hι c)⟩

theorem rootRankOneGroup_le_map_su6Levi_tri [CharP K 2] {ι : k →+* K} {σ : K →+* K}
    (hι : ∀ c, σ (ι c) = ι c) (ω : List (Fin TwistTag.E6.foldedTag.rank))
    {β β' : Fin TwistTag.E6.tag.rank → ℤ} (hβ : IsRoot TwistTag.E6.tag β) (h1 : β 1 = 0)
    (hρ : permLattice TwistTag.E6.perm β = β) (h₁ : twistedE6RelAct ω β = β')
    (h₂ : twistedE6RelAct ω (-β) = -β') :
    TwistedE6Pilot.rootRankOneGroup ι β' ≤
      (su6Levi σ).map (MulAut.conj (twistedE6RelWeyl K ω)).toMonoidHom := by
  rw [← map_conj_rootRankOneGroup_tri ι ω hβ h₁ h₂]
  exact map_mono (rootRankOneGroup_le_su6Levi_tri hι hβ h1 hρ)

theorem map_conj_le_rootRankOneGroup_tri [CharP K 2] {ι : k →+* K}
    {A : Subgroup (ModGL TwistTag.E6.tag K)} (hA : A ≤ E6GraphLevi.thetaRankOneGroup ι)
    (ω : List (Fin TwistTag.E6.foldedTag.rank)) {β' : Fin TwistTag.E6.tag.rank → ℤ}
    (h₁ : twistedE6RelAct ω e6HighestRoot = β')
    (h₂ : twistedE6RelAct ω (-e6HighestRoot) = -β') :
    A.map (MulAut.conj (twistedE6RelWeyl K ω)).toMonoidHom ≤
      TwistedE6Pilot.rootRankOneGroup ι β' := by
  rw [← map_conj_rootRankOneGroup_tri ι ω isRoot_e6HighestRoot h₁ h₂,
    ← thetaRankOneGroup_eq_rootRankOneGroup_tri]
  exact map_mono hA

theorem conj_twistedE6PairX_tri [CharP K 2] (σ : K →+* K)
    (ω : List (Fin TwistTag.E6.foldedTag.rank)) {β β' : Fin TwistTag.E6.tag.rank → ℤ}
    (hβ : IsRoot TwistTag.E6.tag β) (h₁ : twistedE6RelAct ω β = β')
    (h₂ : twistedE6RelAct ω (permLattice TwistTag.E6.perm β) = permLattice TwistTag.E6.perm β')
    (s : K) :
    twistedE6RelWeyl K ω * twistedE6PairX σ β s * (twistedE6RelWeyl K ω)⁻¹ =
      twistedE6PairX σ β' s := by
  have hρβ := hβ.permLattice TwistTag.E6.cartan_perm
  unfold twistedE6PairX
  calc twistedE6RelWeyl K ω * (pinnedX TwistTag.E6.tag K β s *
        pinnedX TwistTag.E6.tag K (permLattice TwistTag.E6.perm β) (σ s)) *
          (twistedE6RelWeyl K ω)⁻¹ =
        (twistedE6RelWeyl K ω * pinnedX TwistTag.E6.tag K β s * (twistedE6RelWeyl K ω)⁻¹) *
          (twistedE6RelWeyl K ω * pinnedX TwistTag.E6.tag K (permLattice TwistTag.E6.perm β) (σ s) *
            (twistedE6RelWeyl K ω)⁻¹) := by group
    _ = _ := by
      rw [twistedE6RelWeyl_conj_pinnedX ω hβ, twistedE6RelWeyl_conj_pinnedX ω hρβ, h₁, h₂]

end Transport

end CFSG.SeitzReduction.TwistedE6Pilot
