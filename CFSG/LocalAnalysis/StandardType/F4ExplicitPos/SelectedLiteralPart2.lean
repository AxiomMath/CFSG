module

public import CFSG.LocalAnalysis.StandardType.F4ExplicitPos.RankThreeModelsPart2
public import CFSG.LocalAnalysis.StandardType.F4ExplicitPos.A2JointPairPart2
public import CFSG.LocalAnalysis.StandardType.F4ExplicitPos.SelectedLiteralPart1

@[expose] public section

public noncomputable section

namespace CFSG.StandardType.F4ExplicitPos.SelectedLiteral
open CFSG CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType CFSG.LieType.Chevalley
  CFSG.LieType.AlgebraicGroups CFSG.LieType.Steinberg CFSG.LieType.Steinberg.Adjoint
  CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  CFSG.HardMathSupport.Timmesfeld.LangTorus CFSG.HardMathSupport.Timmesfeld.CrossChar
  CFSG.RankThree.PartOne.KF4 CFSG.RankThree.E6
  CFSG.HardMathSupport.Solomon.Coordinator.LieComp CFSG.ComponentClassification.CatLeafProof
  CFSG.SeitzReduction.F4Pilot
open CFSG.StandardType.LieCore
open CFSG.Open CFSG.StandardType CFSG.StandardType.ClassicalPosition
open CFSG.StandardType.F4ExplicitPos.LiteralSetup
open CFSG.StandardType.F4ExplicitPos.ActualSetup
open CFSG.StandardType.F4ExplicitPos.ComponentAttach
open CFSG.StandardType.F4ExplicitPos.BaseChange
open CFSG.StandardType.F4ExplicitPos.AmbientAction
open CFSG.StandardType.F4ExplicitPos.A2Actual
open CFSG.StandardType.F4ExplicitPos.SelectedPair
open CFSG.StandardType.F4ExplicitPos.OddKernelActual
open CFSG.StandardType.F4ExplicitPos.RationalC3
open scoped Matrix MatrixGroups

theorem c3_selected_pair_output_of_shape
    {Ω : Type} [Field Ω] [IsAlgClosed Ω] [CharP Ω 2] [Algebra (ZMod 2) Ω]
    [Algebra.IsAlgebraic (ZMod 2) Ω]
    {k : Type} [Field k] [Finite k] [CharP k 2] [Algebra k Ω]
    {f : ℕ} (hf : 1 ≤ f)
    (D : LangDatum Tag.F4 Ω) (hq : D.q = 2 ^ f) (hk : Nat.card k = 2 ^ f)
    {M : Type*} [CommGroup M] {χ : Multiplicative (Fin Tag.F4.rank → ℤ) →* M}
    (i : KernelComponent χ) (Jbar : Subgroup (ModGL Tag.F4 Ω))
    (ρperm : Equiv.Perm (Fin Tag.F4.rank → ℤ)) (hρperm : FrobRootMap D ρperm)
    (hker : ∀ α ∈ kernelRoots χ, ρperm α ∈ kernelRoots χ)
    (hstable : (ρperm : (Fin Tag.F4.rank → ℤ) → (Fin Tag.F4.rank → ℤ)) ''
        componentRoots χ i = componentRoots χ i)
    (h3 : compRank (componentRoots χ i) = 3)
    (h18 : (componentRoots χ i).ncard = 18)
    (v : WeylGroup Tag.F4)
    (hΨ : componentRoots χ i =
      (fun α => v • α) '' parabolicRoots Tag.F4 f4LeviC3)
    {Ccent : Subgroup (ModGL Tag.F4 Ω)}
    (hCcent : rootSpan Tag.F4 Ω (componentRoots χ i) ≤ Ccent)
    (hJbar : CFSG.Assembly.IsComponentOf Jbar (D.Γ ⊓ Ccent))
    (hJbar_le : Jbar ≤ rootSpan Tag.F4 Ω (componentRoots χ i)) :
    SelectedPairOutput (k := k) D χ Jbar i := by
  have hshape : componentRoots χ i =
      (fun α => v • α) '' CFSG.StandardType.F4ExplicitPos.C3Range.c3RootSet := by
    rw [hΨ, parabolicRoots_f4LeviC3_eq_c3RootSet]
  obtain ⟨σ, z, Φ, hσc, hzZ, hnorm, hzH, hzF, -, -, hΦrange, hP_eq⟩ :=
    CFSG.StandardType.F4ExplicitPos.RankThreeModels.f4_rankThree_c3_actual_model_producer
      (Ω := Ω) (K := k) D f hf hq hk ρperm hρperm i hker hstable h3 h18 v hshape
      Ccent hCcent Jbar hJbar hJbar_le
  have hH : rootSpan Tag.F4 Ω (componentRoots χ i) =
      MonoidHom.range (conjIM Ω (canonicalRep (coxeterSystem Tag.F4) Ω v)) := by
    rw [RationalC3.range_conjIM_canonicalRep (Ω := Ω) v, ← hshape]
  have hσ : ∀ c, σ c = c ^ Nat.card k := fun c => by rw [hσc, hq, hk]
  have hnormH : ∀ g : ModGL Tag.F4 Ω,
      g ∈ rootSpan Tag.F4 Ω (componentRoots χ i) ↔
        z * g * z⁻¹ ∈ rootSpan Tag.F4 Ω (componentRoots χ i) := by
    intro g
    rw [hH]
    exact hzH g
  have hstepH : ∀ g ∈ rootSpan Tag.F4 Ω (componentRoots χ i),
      D.step (z * g * z⁻¹) = z * frobGL σ g * z⁻¹ := by
    intro g hg
    rw [hH] at hg
    rw [CFSG.StandardType.F4ExplicitPos.RankThreeModels.frobGL_eq_bcGL (Ω := Ω) σ]
    exact hzF g hg
  have hJ : Jbar = rootSpan Tag.F4 Ω (componentRoots χ i) ⊓ D.model := by
    rw [hP_eq, hΦrange, hH]
  exact CFSG.StandardType.F4ExplicitPos.InnerSelectedPair.inner_selected_pair_output_exists
    (k := k) (H := rootSpan Tag.F4 Ω (componentRoots χ i)) (Jbar := Jbar)
    D hzZ rfl hnormH hσ hstepH hJ

theorem parabolicRoots_f4LeviB3_eq_b3LeviRoots :
    parabolicRoots Tag.F4 f4LeviB3 = b3LeviRoots := by
  ext α
  constructor
  · intro h
    rw [CFSG.SeitzReduction.F4Pilot.mem_b3LeviRoots]
    exact ⟨h.1, h.2 ⟨3, by decide⟩
      (by rw [mem_f4LeviB3_narrow]; decide)⟩
  · intro h
    rw [CFSG.SeitzReduction.F4Pilot.mem_b3LeviRoots] at h
    refine ⟨h.1, fun i hi => ?_⟩
    have hi3 : i = ⟨3, by decide⟩ := by
      apply Fin.ext
      show i.val = 3
      have hnot : ¬ i.val ≤ 2 := fun hle =>
        hi ((mem_f4LeviB3_narrow i).2 hle)
      have hlt := i.isLt
      have hb : Tag.F4.rank = 4 := rfl
      omega
    rw [hi3]; exact h.2

theorem compRank_parabolicRoots_f4LeviB3
    :
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

theorem ncard_parabolicRoots_f4LeviB3 :
    (parabolicRoots Tag.F4 f4LeviB3).ncard = 18 := by
  set C : Finset (Option (Fin Tag.F4.rank)) :=
    (([1, 2, 3] : List ℕ).map (idxNode (r := Tag.F4.rank))).toFinset with hC
  have hnone : none ∉ C := by rw [hC]; decide
  have hCJ : ∀ j, some j ∈ C ↔ j ∈ f4LeviB3 := by
    intro j; rw [hC, mem_f4LeviB3_narrow]; revert j; decide
  have hroots : kacF4.rootsOf (C : Set (Option (Fin Tag.F4.rank))) =
      parabolicRoots Tag.F4 f4LeviB3 :=
    rootsOf_eq_parabolicRoots_narrow kacF4 facts_F4 hnone hCJ
  calc (parabolicRoots Tag.F4 f4LeviB3).ncard
      = (kacF4.rootsOf (C : Set (Option (Fin Tag.F4.rank)))).ncard := by rw [hroots]
    _ = kacCount Tag.F4 kacF4.θ C := ncard_rootsOf kacF4 facts_F4 ⟨none, hnone⟩
    _ = 18 := by rw [hC]; exact kacCount_F4_B3

theorem compRank_parabolicRoots_f4LeviC3
    :
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

theorem ncard_parabolicRoots_f4LeviC3 :
    (parabolicRoots Tag.F4 f4LeviC3).ncard = 18 := by
  set C : Finset (Option (Fin Tag.F4.rank)) :=
    (([2, 3, 4] : List ℕ).map (idxNode (r := Tag.F4.rank))).toFinset with hC
  have hnone : none ∉ C := by rw [hC]; decide
  have hCJ : ∀ j, some j ∈ C ↔ j ∈ f4LeviC3 := by
    intro j; rw [hC, mem_f4LeviC3_narrow]; revert j; decide
  have hroots : kacF4.rootsOf (C : Set (Option (Fin Tag.F4.rank))) =
      parabolicRoots Tag.F4 f4LeviC3 :=
    rootsOf_eq_parabolicRoots_narrow kacF4 facts_F4 hnone hCJ
  calc (parabolicRoots Tag.F4 f4LeviC3).ncard
      = (kacF4.rootsOf (C : Set (Option (Fin Tag.F4.rank)))).ncard := by rw [hroots]
    _ = kacCount Tag.F4 kacF4.θ C := ncard_rootsOf kacF4 facts_F4 ⟨none, hnone⟩
    _ = 18 := by rw [hC]; exact kacCount_F4_C3

theorem b3_selected_pair_output_of_shape
    {Ω : Type} [Field Ω] [IsAlgClosed Ω] [CharP Ω 2] [Algebra (ZMod 2) Ω]
    [Algebra.IsAlgebraic (ZMod 2) Ω]
    {k : Type} [Field k] [Finite k] [CharP k 2] [Algebra k Ω]
    {f : ℕ} (hf : 1 ≤ f)
    (D : LangDatum Tag.F4 Ω) (hq : D.q = 2 ^ f) (hk : Nat.card k = 2 ^ f)
    {M : Type*} [CommGroup M] {χ : Multiplicative (Fin Tag.F4.rank → ℤ) →* M}
    (i : KernelComponent χ) (Jbar : Subgroup (ModGL Tag.F4 Ω))
    (ρperm : Equiv.Perm (Fin Tag.F4.rank → ℤ)) (hρperm : FrobRootMap D ρperm)
    (hker : ∀ α ∈ kernelRoots χ, ρperm α ∈ kernelRoots χ)
    (hstable : (ρperm : (Fin Tag.F4.rank → ℤ) → (Fin Tag.F4.rank → ℤ)) ''
        componentRoots χ i = componentRoots χ i)
    (v : WeylGroup Tag.F4)
    (hΨ : componentRoots χ i =
      (fun α => v • α) '' parabolicRoots Tag.F4 f4LeviB3)
    {Ccent : Subgroup (ModGL Tag.F4 Ω)}
    (hCcent : rootSpan Tag.F4 Ω (componentRoots χ i) ≤ Ccent)
    (hJbar : CFSG.Assembly.IsComponentOf Jbar (D.Γ ⊓ Ccent))
    (hJbar_le : Jbar ≤ rootSpan Tag.F4 Ω (componentRoots χ i)) :
    SelectedPairOutput (k := k) D χ Jbar i := by
  have hshape : componentRoots χ i =
      (fun α => v • α) '' b3LeviRoots := by
    rw [hΨ, parabolicRoots_f4LeviB3_eq_b3LeviRoots]
  have h3 : compRank (componentRoots χ i) = 3 := by
    rw [hshape, compRank_image, ← parabolicRoots_f4LeviB3_eq_b3LeviRoots]
    exact compRank_parabolicRoots_f4LeviB3
  have h18 : (componentRoots χ i).ncard = 18 := by
    rw [hshape, ncard_image_smul, ← parabolicRoots_f4LeviB3_eq_b3LeviRoots]
    exact ncard_parabolicRoots_f4LeviB3
  obtain ⟨σ, z, ΦB, hσc, hzZ, hnorm, hzH, hzF, -, -, hΦrange, hP_eq⟩ :=
    CFSG.StandardType.F4ExplicitPos.RankThreeModels.f4_rankThree_b3_actual_model_producer
      (Ω := Ω) (K := k) D f hf hq hk ρperm hρperm i hker hstable h3 h18 v hshape
      Ccent hCcent Jbar hJbar hJbar_le
  have hH : rootSpan Tag.F4 Ω (componentRoots χ i) =
      MonoidHom.range (_root_.CFSG.StandardType.F4ExplicitPos.RationalB3.conjBM Ω
        (canonicalRep (coxeterSystem Tag.F4) Ω v)) := by
    rw [hshape, ← RationalB3.range_conjBM_canonicalRep (Ω := Ω) v]
  have hσ : ∀ c, σ c = c ^ Nat.card k := fun c => by rw [hσc, hq, hk]
  have hnormH : ∀ g : ModGL Tag.F4 Ω,
      g ∈ rootSpan Tag.F4 Ω (componentRoots χ i) ↔
        z * g * z⁻¹ ∈ rootSpan Tag.F4 Ω (componentRoots χ i) := by
    intro g
    rw [hH]
    exact hzH g
  have hstepH : ∀ g ∈ rootSpan Tag.F4 Ω (componentRoots χ i),
      D.step (z * g * z⁻¹) = z * frobGL σ g * z⁻¹ := by
    intro g hg
    rw [hH] at hg
    rw [CFSG.StandardType.F4ExplicitPos.RankThreeModels.frobGL_eq_bcGL (Ω := Ω) σ]
    exact hzF g hg
  have hJ : Jbar = rootSpan Tag.F4 Ω (componentRoots χ i) ⊓ D.model := by
    rw [hP_eq, hΦrange, hH]
  exact CFSG.StandardType.F4ExplicitPos.InnerSelectedPair.inner_selected_pair_output_exists
    (k := k) (H := rootSpan Tag.F4 Ω (componentRoots χ i)) (Jbar := Jbar)
    D hzZ rfl hnormH hσ hstepH hJ

theorem a2_long_selected_pair_output_of_shape
    {Ω : Type} [Field Ω] [IsAlgClosed Ω] [CharP Ω 2]
    {k : Type} [Field k] [Algebra k Ω] [IsAlgClosure k Ω]
    {f : ℕ} (hf : 1 ≤ f) (hk : Nat.card k = 2 ^ f)
    (D : LangDatum Tag.F4 Ω) (hq : D.q = 2 ^ f)
    (hstep_inj : Function.Injective D.step)
    {M : Type*} [CommGroup M] {χ : Multiplicative (Fin Tag.F4.rank → ℤ) →* M}
    (i : KernelComponent χ) (Jbar : Subgroup (ModGL Tag.F4 Ω))
    (ρperm : Equiv.Perm (Fin Tag.F4.rank → ℤ)) (hρperm : FrobRootMap D ρperm)
    (hker : ∀ α ∈ kernelRoots χ, ρperm α ∈ kernelRoots χ)
    (hstable : (ρperm : (Fin Tag.F4.rank → ℤ) → (Fin Tag.F4.rank → ℤ)) ''
        componentRoots χ i = componentRoots χ i)
    (v : WeylGroup Tag.F4)
    (hΨ : componentRoots χ i =
      (fun α => v • α) '' parabolicRoots Tag.F4 f4LongSupport)
    {Ccent : Subgroup (ModGL Tag.F4 Ω)}
    (hCcent : rootSpan Tag.F4 Ω (componentRoots χ i) ≤ Ccent)
    (hJbar : CFSG.Assembly.IsComponentOf Jbar (D.Γ ⊓ Ccent))
    (hJbar_le : Jbar ≤ rootSpan Tag.F4 Ω (componentRoots χ i)) :
    SelectedPairOutput (k := k) D χ Jbar i := by
  classical
  set ρA : SL(3, Ω) →* ModGL Tag.F4 Ω :=
    (MulAut.conj (canonicalRep (coxeterSystem Tag.F4) Ω v)).toMonoidHom.comp
      (f4rhoLong_actual (K := Ω)) with hρA
  set r : Fin 3 → Fin 3 → Fin Tag.F4.rank → ℤ :=
    fun a b => v • chainRoot f4chainLong a b with hr
  have hframeA : IsA2Frame ρA r := f4Long_frame_actual_transport (L := Ω) v
  have hframe : IsSLFrame ρA r := IsSLFrame.of_isA2Frame hframeA
  have hframe_eq : frameRoots r = componentRoots χ i := by
    rw [frameRoots_f4chainLong_smul (v := v), hΨ]
  have hρinj : Function.Injective ρA := hframeA.injective
  have hCcentA : ρA.range ≤ Ccent := by
    rw [hframe.range, hframe_eq]; exact hCcent
  have hJbarA : Jbar ≤ ρA.range := by
    rw [hframe.range, hframe_eq]; exact hJbar_le
  have hnorm : ∀ a b : Fin 3, a ≠ b → iform (r a b) (r a b) = 2 * (2 : ℤ) := by
    intro a b hab
    have h1 : iform (r a b) (r a b) =
        iform (chainRoot f4chainLong a b) (chainRoot f4chainLong a b) := by
      rw [hr, iform_smul]
    rw [h1]
    exact (f4_long12_isRoot a b hab).2.2
  have hmaps : ∀ a b : Fin 3, a ≠ b → ρperm (r a b) ∈ frameRoots r := by
    intro a b hab
    have hmem : r a b ∈ componentRoots χ i := by
      rw [← hframe_eq]
      exact ⟨a, b, hab, rfl⟩
    have h2 : ρperm (r a b) ∈
        (ρperm : (Fin Tag.F4.rank → ℤ) → (Fin Tag.F4.rank → ℤ)) ''
          componentRoots χ i := Set.mem_image_of_mem _ hmem
    rw [hstable] at h2
    rwa [hframe_eq]
  rcases hframe.aut_cases (by norm_num : 3 ≤ 3) (by norm_num : (2 : ℤ) ≠ 0) hnorm
      (ρperm : (Fin Tag.F4.rank → ℤ) → (Fin Tag.F4.rank → ℤ))
      hmaps hρperm.neg_eq hρperm.iform_eq with ⟨π, hsplit⟩ | ⟨π, hunitary⟩
  · exact CFSG.StandardType.F4ExplicitPos.A2JointPair.a2_split_selected_pair_output
      (Ω := Ω) (k := k) (f := f) hf hk D hq hstep_inj i Jbar ρA r hframe hρinj
      hframe_eq ρperm hρperm hstable π hsplit hCcentA hJbar hJbarA
  · exact CFSG.StandardType.F4ExplicitPos.A2JointPair.a2_unitary_selected_pair_output
      (Ω := Ω) (k := k) (f := f) hf hk D hq hstep_inj i Jbar ρA r hframe hρinj
      hframe_eq ρperm hρperm hstable π hunitary hCcentA hJbar hJbarA

theorem a2_short_selected_pair_output_of_shape
    {Ω : Type} [Field Ω] [IsAlgClosed Ω] [CharP Ω 2]
    {k : Type} [Field k] [Algebra k Ω] [IsAlgClosure k Ω]
    {f : ℕ} (hf : 1 ≤ f) (hk : Nat.card k = 2 ^ f)
    (D : LangDatum Tag.F4 Ω) (hq : D.q = 2 ^ f)
    (hstep_inj : Function.Injective D.step)
    {M : Type*} [CommGroup M] {χ : Multiplicative (Fin Tag.F4.rank → ℤ) →* M}
    (i : KernelComponent χ) (Jbar : Subgroup (ModGL Tag.F4 Ω))
    (ρperm : Equiv.Perm (Fin Tag.F4.rank → ℤ)) (hρperm : FrobRootMap D ρperm)
    (hker : ∀ α ∈ kernelRoots χ, ρperm α ∈ kernelRoots χ)
    (hstable : (ρperm : (Fin Tag.F4.rank → ℤ) → (Fin Tag.F4.rank → ℤ)) ''
        componentRoots χ i = componentRoots χ i)
    (v : WeylGroup Tag.F4)
    (hΨ : componentRoots χ i =
      (fun α => v • α) '' parabolicRoots Tag.F4 f4ShortSupport)
    {Ccent : Subgroup (ModGL Tag.F4 Ω)}
    (hCcent : rootSpan Tag.F4 Ω (componentRoots χ i) ≤ Ccent)
    (hJbar : CFSG.Assembly.IsComponentOf Jbar (D.Γ ⊓ Ccent))
    (hJbar_le : Jbar ≤ rootSpan Tag.F4 Ω (componentRoots χ i)) :
    SelectedPairOutput (k := k) D χ Jbar i := by
  classical
  set ρA : SL(3, Ω) →* ModGL Tag.F4 Ω :=
    (MulAut.conj (canonicalRep (coxeterSystem Tag.F4) Ω v)).toMonoidHom.comp
      (f4rhoShort_actual (K := Ω)) with hρA
  set r : Fin 3 → Fin 3 → Fin Tag.F4.rank → ℤ :=
    fun a b => v • f4ShortSigma a b with hr
  have hframeA : IsA2Frame ρA r := f4Short_frame_actual_transport (L := Ω) v
  have hframe : IsSLFrame ρA r := IsSLFrame.of_isA2Frame hframeA
  have hframe_eq : frameRoots r = componentRoots χ i := by
    rw [frameRoots_f4ShortSigma_smul (v := v), hΨ]
  have hρinj : Function.Injective ρA := hframeA.injective
  have hCcentA : ρA.range ≤ Ccent := by
    rw [hframe.range, hframe_eq]; exact hCcent
  have hJbarA : Jbar ≤ ρA.range := by
    rw [hframe.range, hframe_eq]; exact hJbar_le
  have hnorm : ∀ a b : Fin 3, a ≠ b → iform (r a b) (r a b) = 2 * (1 : ℤ) := by
    intro a b hab
    have h1 : iform (r a b) (r a b) =
        iform (f4ShortSigma a b) (f4ShortSigma a b) := by
      rw [hr, iform_smul]
    rw [h1]
    exact (f4_short_isRoot a b hab).2.2
  have hmaps : ∀ a b : Fin 3, a ≠ b → ρperm (r a b) ∈ frameRoots r := by
    intro a b hab
    have hmem : r a b ∈ componentRoots χ i := by
      rw [← hframe_eq]
      exact ⟨a, b, hab, rfl⟩
    have h2 : ρperm (r a b) ∈
        (ρperm : (Fin Tag.F4.rank → ℤ) → (Fin Tag.F4.rank → ℤ)) ''
          componentRoots χ i := Set.mem_image_of_mem _ hmem
    rw [hstable] at h2
    rwa [hframe_eq]
  rcases hframe.aut_cases (by norm_num : 3 ≤ 3) (by norm_num : (1 : ℤ) ≠ 0) hnorm
      (ρperm : (Fin Tag.F4.rank → ℤ) → (Fin Tag.F4.rank → ℤ))
      hmaps hρperm.neg_eq hρperm.iform_eq with ⟨π, hsplit⟩ | ⟨π, hunitary⟩
  · exact CFSG.StandardType.F4ExplicitPos.A2JointPair.a2_split_selected_pair_output
      (Ω := Ω) (k := k) (f := f) hf hk D hq hstep_inj i Jbar ρA r hframe hρinj
      hframe_eq ρperm hρperm hstable π hsplit hCcentA hJbar hJbarA
  · exact CFSG.StandardType.F4ExplicitPos.A2JointPair.a2_unitary_selected_pair_output
      (Ω := Ω) (k := k) (f := f) hf hk D hq hstep_inj i Jbar ρA r hframe hρinj
      hframe_eq ρperm hρperm hstable π hunitary hCcentA hJbar hJbarA

end CFSG.StandardType.F4ExplicitPos.SelectedLiteral
end

end
