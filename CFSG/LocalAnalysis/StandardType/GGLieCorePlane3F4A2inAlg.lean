module

public import CFSG.LocalAnalysis.StandardType.GGLieCorePlane3F4Defs
public import CFSG.LocalAnalysis.StandardType.GGFamLabelAssembly
import CFSG.LocalAnalysis.StandardType.F4ExplicitPos.RationalA2Part2
import CFSG.LocalAnalysis.StandardType.F4ExplicitPos.NativePinFinalPart2
import CFSG.LocalAnalysis.StandardType.F4ExplicitPos.JointShapesPart2
import CFSG.LocalAnalysis.StandardType.F4ExplicitPos.F4LowRankShapes
import CFSG.HardMathSupport.Timmesfeld.LangTorus.InnerQuasisimpleSplit
import CFSG.Open.StatedAPI
public import CFSG.LocalAnalysis.StandardType.GGFamAssembly

public section

namespace CFSG.StandardType.LieCore

open CFSG.Assembly CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LieType.AlgebraicGroups CFSG.HardMathSupport.Timmesfeld.LangTorus CFSG.RankThree.PartOne.KE
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
open CFSG.Open (StatedLieTag)
open scoped MatrixGroups
open CFSG.HardMathSupport.Timmesfeld.CrossChar
open CFSG.RankThree.Chevalley.F4Weyl
open CFSG.RankThree.E6
open CFSG.StandardType.F4ExplicitPos.A2Actual
open CFSG.StandardType.F4ExplicitPos.RationalA2
open CFSG.StandardType.F4ExplicitPos.JointShapes
open CFSG.StandardType.F4ExplicitPos.NativePinFinal
open CFSG.SeitzReduction.F4Pilot
open CFSG.HardMathSupport.Solomon.Coordinator.LieComp
open CFSG.ComponentClassification.CatLeafProof

private theorem l10lG3_model_of_untwist
    {Ω : Type} [Field Ω] [IsAlgClosed Ω] [CharP Ω 2]
    {k : Type} [Field k] [Algebra k Ω] [IsAlgClosure k Ω]
    {f : ℕ} (hf : 1 ≤ f) (hk : Nat.card k = 2 ^ f)
    (D : LangDatum Tag.F4 Ω) (hq : D.q = 2 ^ f)
    {Ψ : Set (Fin Tag.F4.rank → ℤ)}
    {ρL : SL(3, Ω) →* ModGL Tag.F4 Ω} {r : Fin 3 → Fin 3 → Fin Tag.F4.rank → ℤ}
    (hframe : IsSLFrame ρL r) (hρinj : Function.Injective ρL)
    (hframe_eq : frameRoots r = Ψ)
    (σ : Ω ≃+* Ω) (hσc : ∀ c, σ c = c ^ D.q) (z : ModGL Tag.F4 Ω)
    (hznorm : ∀ g, g ∈ rootSpan Tag.F4 Ω Ψ ↔ z * g * z⁻¹ ∈ rootSpan Tag.F4 Ω Ψ)
    (hstep : ∀ g ∈ rootSpan Tag.F4 Ω Ψ, D.step (z * g * z⁻¹) = z * frobGL σ g * z⁻¹) :
    GGLieSL3Model ↥(rootSpan Tag.F4 Ω Ψ ⊓ D.model) f := by
  classical
  have hσ : ∀ c, σ c = c ^ 2 ^ f := fun c => by rw [hσc c, hq]
  have hfrobGLinj : Function.Injective (frobGL (τ := Tag.F4) (L := Ω) σ) := by
    have h : frobGL (τ := Tag.F4) (L := Ω) σ =
        CFSG.StandardType.F4ExplicitPos.BaseChange.bcGL (τ := Tag.F4) σ.toRingHom := by
      rw [frobGL, CFSG.StandardType.F4ExplicitPos.BaseChange.bcGL,
        CFSG.StandardType.F4ExplicitPos.BaseChange.bcEndHom_eq_entrywiseHom]
    rw [h]
    exact CFSG.StandardType.F4ExplicitPos.BaseChange.bcGL_injective (τ := Tag.F4)
      σ.toRingHom σ.injective
  let ρA : SL(3, Ω) →* ModGL Tag.F4 Ω := (MulAut.conj z).toMonoidHom.comp ρL
  have hρArange : ρA.range = rootSpan Tag.F4 Ω Ψ := by
    have hmap : (rootSpan Tag.F4 Ω Ψ).map (MulAut.conj z).toMonoidHom = rootSpan Tag.F4 Ω Ψ := by
      apply le_antisymm
      · rintro g ⟨h, hh, rfl⟩
        exact (hznorm h).mp hh
      · intro g hg
        refine ⟨z⁻¹ * g * z, (hznorm (z⁻¹ * g * z)).mpr ?_, ?_⟩
        · rw [show z * (z⁻¹ * g * z) * z⁻¹ = g by group]
          exact hg
        · show z * (z⁻¹ * g * z) * z⁻¹ = g
          group
    rw [show ρA = (MulAut.conj z).toMonoidHom.comp ρL from rfl, MonoidHom.range_comp,
      hframe.range, hframe_eq, hmap]
  have hρAinj : Function.Injective ρA := (MulAut.conj z).injective.comp hρinj
  have hρAle : ρA.range ≤ adjointGroup Tag.F4 Ω := by
    rw [hρArange, ← hframe_eq, ← hframe.range]
    exact hframe.range_le_adjointGroup
  have hroot : ∀ a b : Fin 3, a ≠ b → ∃ bu : Ωˣ, ∀ c : Ω,
      frobGL (τ := Tag.F4) (L := Ω) σ (pinnedX Tag.F4 Ω (r a b) c) =
        pinnedX Tag.F4 Ω (r a b) ((bu : Ω) * σ.toRingHom c) := by
    intro a b _
    refine ⟨1, fun c => ?_⟩
    rw [frobGL_pinnedX]
    simp
  obtain ⟨Φ', hΦ', bu, hΦ'gen⟩ := inducedAut_split (τ := Tag.F4) (L := Ω) hframe hρinj
    σ.toRingHom σ.bijective (frobGL (τ := Tag.F4) (L := Ω) σ) hfrobGLinj
    (Equiv.refl (Fin 3)) hroot
  have hΦ'' : ∀ (a b : Fin 3) (hab : a ≠ b) (t : Ω),
      ((Φ' (Matrix.SpecialLinearGroup.transvection hab t) : SL(3, Ω)) :
        Matrix (Fin 3) (Fin 3) Ω) =
        1 + Matrix.single a b ((bu a b : Ω) * t ^ 2 ^ f) := by
    intro a b hab t
    have h := hΦ'gen a b hab t
    rw [h]
    simp only [Equiv.refl_apply]
    rw [show σ.toRingHom t = t ^ 2 ^ f from hσ t]
  obtain ⟨H, _hfull, hfix⟩ := split_full_intertwining (ℓ := 2) (f := f) (k := k) (Ω := Ω)
    Nat.prime_two hf hk (n := 3) (by norm_num) σ.toRingHom hσ (Equiv.refl (Fin 3)) Φ' bu hΦ''
  have hΦ'A : ∀ X : SL(3, Ω), D.step (ρA X) = ρA (Φ' X) := by
    intro X
    have hg : ρL X ∈ rootSpan Tag.F4 Ω Ψ := by
      rw [← hframe_eq, ← hframe.range]
      exact ⟨X, rfl⟩
    calc D.step (ρA X) = D.step (z * ρL X * z⁻¹) := rfl
      _ = z * frobGL (τ := Tag.F4) (L := Ω) σ (ρL X) * z⁻¹ := hstep (ρL X) hg
      _ = z * ρL (Φ' X) * z⁻¹ := by rw [hΦ' X]
      _ = ρA (Φ' X) := rfl
  have hNdef : (kappaSL (k := k) ρA H).range = ρA.range ⊓ D.model := by
    rw [kappaSL_range (ρ := ρA) (H := H) D.step Φ' hρAinj hΦ'A hfix, LangDatum.model,
      ← inf_assoc, inf_eq_left.mpr hρAle]
  have hfin : Finite k := Nat.finite_of_card_ne_zero (by rw [hk]; exact pow_ne_zero f (by norm_num))
  have hκinj : Function.Injective (kappaSL (k := k) ρA H) :=
    kappaSL_injective (k := k) (ρ := ρA) (H := H) hρAinj
  refine ⟨k, inferInstance, hfin, hk, ?_⟩
  have e1 : SL(3, k) ≃* ↥((kappaSL (k := k) ρA H).range) := MonoidHom.ofInjective hκinj
  have e2 : ↥((kappaSL (k := k) ρA H).range) ≃* ↥(rootSpan Tag.F4 Ω Ψ ⊓ D.model) :=
    MulEquiv.subgroupCongr (hNdef.trans (by rw [hρArange]))
  have e3 : SL(3, k) ≃* ↥(rootSpan Tag.F4 Ω Ψ ⊓ D.model) := e1.trans e2
  have hSL : SL(3, k) ≃* CFSG.Open.StatedSL 3 k :=
    (MonoidHom.ofInjective Matrix.SpecialLinearGroup.toGL_injective).trans
      (MulEquiv.subgroupCongr (CFSG.Open.StatedAPI.statedSL_eq_range_toGL 3 k).symm)
  exact ⟨e3.symm.trans hSL⟩

private theorem l10lG3_card_b2LeviRoots
    : b2LeviRoots.ncard = 8 := by
  have hb2eq : b2LeviRoots = parabolicRoots Tag.F4 nodesTU := by
    ext γ
    rw [CFSG.SeitzReduction.F4Pilot.mem_b2LeviRoots, CFSG.LieType.Chevalley.parabolicRoots]
    constructor
    · rintro ⟨hr, h0, h3⟩
      refine ⟨hr, fun i hi => ?_⟩
      have hi1 : i.val ≠ 1 := fun h => hi (by rw [mem_nodesTU]; exact Or.inl (Fin.ext h))
      have hi2 : i.val ≠ 2 := fun h => hi (by rw [mem_nodesTU]; exact Or.inr (Fin.ext h))
      have hival : i.val = 0 ∨ i.val = 3 := by
        have hlt : i.val < 4 := i.isLt
        omega
      rcases hival with h | h
      · rw [show i = 0 from Fin.ext h]; exact h0
      · rw [show i = 3 from Fin.ext h]; exact h3
    · rintro ⟨hr, hv⟩
      exact ⟨hr, hv 0 (by rw [mem_nodesTU]; decide), hv 3 (by rw [mem_nodesTU]; decide)⟩
  have hnodes : nodesTU = ({f4Index 1, f4Index 2} : Set (Fin Tag.F4.rank)) := by
    have hf1 : f4Index (1 : Fin 4) = (1 : Fin Tag.F4.rank) := by decide
    have hf2 : f4Index (2 : Fin 4) = (2 : Fin Tag.F4.rank) := by decide
    ext j
    rw [mem_nodesTU, hf1, hf2]
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
  rw [hb2eq, hnodes, ncard_parabolicRoots_B2]

private theorem l10lG3_compRank_f4LeviB3 :
    compRank (parabolicRoots Tag.F4 f4LeviB3) = 3 := by
  set C : Finset (Option (Fin Tag.F4.rank)) :=
    (([1, 2, 3] : List ℕ).map (idxNode (r := Tag.F4.rank))).toFinset with hC
  have hnone : none ∉ C := by rw [hC]; decide
  have hCJ : ∀ j, some j ∈ C ↔ j ∈ f4LeviB3 := by
    intro j; rw [hC, mem_f4LeviB3_narrow]; revert j; decide
  have hroots : kacF4.rootsOf (C : Set (Option (Fin Tag.F4.rank))) =
      parabolicRoots Tag.F4 f4LeviB3 :=
    rootsOf_eq_parabolicRoots_narrow kacF4 facts_F4 hnone hCJ
  have hcard : C.card = 3 := by rw [hC]; decide
  calc compRank (parabolicRoots Tag.F4 f4LeviB3)
      = compRank (kacF4.rootsOf (C : Set (Option (Fin Tag.F4.rank)))) := by rw [hroots]
    _ = C.card := compRank_rootsOf kacF4 facts_F4 ⟨none, hnone⟩
    _ = 3 := hcard

private theorem l10lG3_compRank_f4LeviC3 :
    compRank (parabolicRoots Tag.F4 f4LeviC3) = 3 := by
  set C : Finset (Option (Fin Tag.F4.rank)) :=
    (([2, 3, 4] : List ℕ).map (idxNode (r := Tag.F4.rank))).toFinset with hC
  have hnone : none ∉ C := by rw [hC]; decide
  have hCJ : ∀ j, some j ∈ C ↔ j ∈ f4LeviC3 := by
    intro j; rw [hC, mem_f4LeviC3_narrow]; revert j; decide
  have hroots : kacF4.rootsOf (C : Set (Option (Fin Tag.F4.rank))) =
      parabolicRoots Tag.F4 f4LeviC3 :=
    rootsOf_eq_parabolicRoots_narrow kacF4 facts_F4 hnone hCJ
  have hcard : C.card = 3 := by rw [hC]; decide
  calc compRank (parabolicRoots Tag.F4 f4LeviC3)
      = compRank (kacF4.rootsOf (C : Set (Option (Fin Tag.F4.rank)))) := by rw [hroots]
    _ = C.card := compRank_rootsOf kacF4 facts_F4 ⟨none, hnone⟩
    _ = 3 := hcard

private theorem l10lG3_ncard_pair (j : Fin Tag.F4.rank) :
    ({Pi.single j (1 : ℤ), -Pi.single j 1} : Set (Fin Tag.F4.rank → ℤ)).ncard = 2 := by
  refine Set.ncard_pair ?_
  intro h
  have hc := congrFun h j
  simp only [Pi.single_eq_same, Pi.neg_apply] at hc
  norm_num at hc

theorem ggLieF4A2in_fixedGroup_alg
    {Ω : Type} [Field Ω] [IsAlgClosed Ω] [CharP Ω 2] [Algebra (ZMod 2) Ω]
    [Algebra.IsAlgebraic (ZMod 2) Ω] {D : LangDatum Tag.F4 Ω}
    {ρ : Equiv.Perm (Fin Tag.F4.rank → ℤ)} {a₁ a₂ : Fin Tag.F4.rank → Ωˣ}
    (h : GGLieF4PlaneHyp D ρ a₁ a₂)
    {f : ℕ} (hf : 1 ≤ f) (hqf : D.q = 2 ^ f) (i : KernelComponent (jointChar a₁ a₂))
    (hshape : compRank (componentRoots (jointChar a₁ a₂) i) = 2 ∧
      (componentRoots (jointChar a₁ a₂) i).ncard = 6)
    (hρΨ : (ρ : (Fin Tag.F4.rank → ℤ) → (Fin Tag.F4.rank → ℤ)) ''
      componentRoots (jointChar a₁ a₂) i = componentRoots (jointChar a₁ a₂) i)
    (hin : twistInner (componentRoots (jointChar a₁ a₂) i) (fun u => ρ u)) :
    GGLieSL3Model ↥(rootSpan Tag.F4 Ω (componentRoots (jointChar a₁ a₂) i) ⊓ D.model) f := by
  classical
  let F : Subfield Ω := TauCeti.frobeniusFixedSubfield Ω 2 f
  have hfixZ : ∀ c : ZMod 2, c ^ 2 ^ f = c := by
    have h2 : ∀ c : ZMod 2, c ^ 2 = c := by decide
    intro c
    have hpow : ∀ n : ℕ, c ^ 2 ^ n = c := by
      intro n
      induction n with
      | zero => simp
      | succ n ih =>
        have h2n : 2 ^ (n + 1) = 2 ^ n + 2 ^ n := by rw [pow_succ]; ring
        rw [h2n, pow_add, ih, ← pow_two, h2]
    exact hpow f
  let k : IntermediateField (ZMod 2) Ω := F.toIntermediateField (fun c => by
    rw [TauCeti.mem_frobeniusFixedSubfield, ← map_pow, hfixZ c])
  have : Algebra.IsAlgebraic ↥k Ω := inferInstance
  have : IsAlgClosure ↥k Ω := ⟨inferInstance, inferInstance⟩
  have hk : Nat.card ↥k = 2 ^ f := by
    change Nat.card (TauCeti.frobeniusFixedSubfield Ω 2 f) = 2 ^ f
    exact TauCeti.card_frobeniusFixedSubfield (K := Ω) (p := 2) f (by omega : f ≠ 0)
  obtain ⟨ha, hd, hne⟩ : (∀ j, a₁ j ^ 3 = 1) ∧ (∀ j, a₂ j ^ 3 = 1) ∧
      (rootDiagUnit Tag.F4 a₁ ≠ 1 ∨ rootDiagUnit Tag.F4 a₂ ≠ 1) := by
    refine ⟨pow_eq_one_of_rootDiagUnit_pow (a := a₁) h.pow₁,
      pow_eq_one_of_rootDiagUnit_pow (a := a₂) h.pow₂, ?_⟩
    by_contra hc
    push Not at hc
    obtain ⟨hb₁, hb₂⟩ := hc
    have hbot : Subgroup.closure ({rootDiagUnit Tag.F4 a₁, rootDiagUnit Tag.F4 a₂} :
        Set (ModGL Tag.F4 Ω)) = ⊥ := by
      rw [eq_bot_iff, Subgroup.closure_le]
      rintro x (rfl | rfl)
      · exact Subgroup.mem_bot.mpr hb₁
      · exact Subgroup.mem_bot.mpr hb₂
    have hcard := h.card
    rw [hbot, Subgroup.card_bot] at hcard
    norm_num at hcard
  have hker : ∀ γ ∈ kernelRoots (jointChar a₁ a₂), ρ γ ∈ kernelRoots (jointChar a₁ a₂) := by
    intro γ hγ
    obtain ⟨hroot, hchar⟩ := hγ
    rw [jointChar, MonoidHom.prod_apply, Prod.mk_eq_one] at hchar
    refine ⟨(h.frob.isRoot_iff γ).2 hroot, ?_⟩
    rw [jointChar, MonoidHom.prod_apply, Prod.mk_eq_one]
    exact ⟨by
        change rootChar a₁ (ρ γ) = 1
        rw [h.frob.rootChar_eq a₁ h.mem₁ γ hroot]
        rw [show rootChar a₁ γ = 1 from hchar.1, one_pow],
      by
        change rootChar a₂ (ρ γ) = 1
        rw [h.frob.rootChar_eq a₂ h.mem₂ γ hroot]
        rw [show rootChar a₂ γ = 1 from hchar.2, one_pow]⟩
  obtain ⟨v, hcases⟩ := CFSG.StandardType.F4ExplicitPos.JointShapes.f4_joint_component_six_shape
    (Ω := Ω) (p := 3) (by norm_num) (by norm_num) a₁ a₂ ha hd hne i
  obtain ⟨σ, z, hσc, _hzZ, hznormAll, hstep⟩ :=
    exists_untwist_one_step_native (χ := jointChar a₁ a₂) D f hf hqf ρ h.frob i hker hin
  have hznorm : ∀ g, g ∈ rootSpan Tag.F4 Ω (componentRoots (jointChar a₁ a₂) i) ↔
      z * g * z⁻¹ ∈ rootSpan Tag.F4 Ω (componentRoots (jointChar a₁ a₂) i) :=
    fun g => hznormAll i g
  rcases hcases with ⟨j, hj⟩ | hlong | hshort | hb2 | hb3 | hc3
  · exfalso
    have h2 : (componentRoots (jointChar a₁ a₂) i).ncard = 2 := by
      rw [hj, ncard_image_smul]
      exact l10lG3_ncard_pair j
    omega
  ·
    let ρA : SL(3, Ω) →* ModGL Tag.F4 Ω :=
      (MulAut.conj (canonicalRep (coxeterSystem Tag.F4) Ω v)).toMonoidHom.comp
        (f4rhoLong_actual (K := Ω))
    let r : Fin 3 → Fin 3 → Fin Tag.F4.rank → ℤ :=
      fun a b => v • chainRoot CFSG.RankThree.PartOne.KF4.f4chainLong a b
    have hframeA : CFSG.RankThree.PartOne.KF4.IsA2Frame ρA r :=
      (f4Long_frame_actual (K := Ω)).transport v
    have hframe : IsSLFrame ρA r := IsSLFrame.of_isA2Frame hframeA
    have hframe_eq : frameRoots r = componentRoots (jointChar a₁ a₂) i := by
      rw [hlong]
      ext γ
      constructor
      · rintro ⟨a, b, hab, rfl⟩
        exact ⟨chainRoot CFSG.RankThree.PartOne.KF4.f4chainLong a b,
          CFSG.RankThree.PartOne.KF4.f4chainLong_mem_parabolicRoots hab, rfl⟩
      · rintro ⟨β, hβ, rfl⟩
        obtain ⟨a, b, hab, rfl⟩ := CFSG.RankThree.PartOne.KF4.exists_f4chainLong_of_mem hβ
        exact ⟨a, b, hab, rfl⟩
    exact l10lG3_model_of_untwist hf hk D hqf hframe hframeA.injective hframe_eq σ hσc z hznorm
      hstep
  ·
    let ρA : SL(3, Ω) →* ModGL Tag.F4 Ω :=
      (MulAut.conj (canonicalRep (coxeterSystem Tag.F4) Ω v)).toMonoidHom.comp
        (f4rhoShort_actual (K := Ω))
    let r : Fin 3 → Fin 3 → Fin Tag.F4.rank → ℤ :=
      fun a b => v • CFSG.RankThree.PartOne.KF4.f4ShortSigma a b
    have hframeA : CFSG.RankThree.PartOne.KF4.IsA2Frame ρA r :=
      (f4Short_frame_actual (K := Ω)).transport v
    have hframe : IsSLFrame ρA r := IsSLFrame.of_isA2Frame hframeA
    have hframe_eq : frameRoots r = componentRoots (jointChar a₁ a₂) i := by
      rw [hshort]
      ext γ
      constructor
      · rintro ⟨a, b, hab, rfl⟩
        exact ⟨CFSG.RankThree.PartOne.KF4.f4ShortSigma a b,
          CFSG.RankThree.PartOne.KF4.f4ShortSigma_mem_parabolicRoots hab, rfl⟩
      · rintro ⟨β, hβ, rfl⟩
        obtain ⟨a, b, hab, rfl⟩ := CFSG.RankThree.PartOne.KF4.exists_f4ShortSigma_of_mem hβ
        exact ⟨a, b, hab, rfl⟩
    exact l10lG3_model_of_untwist hf hk D hqf hframe hframeA.injective hframe_eq σ hσc z hznorm
      hstep
  ·
    exfalso
    have h8 : (componentRoots (jointChar a₁ a₂) i).ncard = 8 := by
      rw [hb2, ncard_image_smul]
      exact l10lG3_card_b2LeviRoots
    omega
  ·
    exfalso
    have h3 : compRank (componentRoots (jointChar a₁ a₂) i) = 3 := by
      rw [hb3, compRank_image]
      exact l10lG3_compRank_f4LeviB3
    omega
  ·
    exfalso
    have h3 : compRank (componentRoots (jointChar a₁ a₂) i) = 3 := by
      rw [hc3, compRank_image]
      exact l10lG3_compRank_f4LeviC3
    omega

end CFSG.StandardType.LieCore
