module

public import CFSG.RankThree.PartOne.KF4.QPlusFamily
public import CFSG.RankThree.PartOne.KF4.EvenDescent

public noncomputable section

namespace CFSG.RankThree.PartOne.KF4

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.RankThree.E6
  CFSG.RankThree.Chevalley CFSG.LocalAnalysis.ComponentInitial
open CFSG.RankThree.PartOne.KE
open CFSG.RankThree.Chevalley.NativeLevi
open scoped Matrix Pointwise

section Fam

variable {L : Type} [Field L] [CharP L 2] [IsAlgClosed L]

@[expose] def QPFam (L : Type) [Field L] [CharP L 2] [IsAlgClosed L] (K : Type) [Field K]
    [Algebra K L] (f : ℕ) (J : Finset (Fin Tag.F4.rank)) (i₀ : Fin Tag.F4.rank) : Prop :=
  ∃ (ι' : Type) (P : ι' → Subgroup (ModGL Tag.F4 L)),
    IsSigmaFamily (qpRep L) (iterateFrobenius L 2 f)
        (parabolicRoots Tag.F4 (J : Set (Fin Tag.F4.rank))) P ∧
      (⨆ i, P i) = rootSpan Tag.F4 L (parabolicRoots Tag.F4 (J : Set (Fin Tag.F4.rank))) ⊓
        twistedFixedPoints (qpRep L) (Units.map (entrywiseHom (iterateFrobenius L 2 f))) ∧
      CFSG.layer ↥(⨆ i, P i) = ⊤ ∧
      ∃ h₀ : ModGL Tag.F4 L, h₀ ∈ adjointGroup Tag.F4 L ∧
        ∀ Y : SL2 K, h₀ * simpleRootSL2 Tag.F4 L i₀
          (Matrix.SpecialLinearGroup.map (algebraMap K L) Y) * h₀⁻¹ ∈ ⨆ i, P i

theorem qpFam_of_factor {K : Type} [Field K] [Algebra K L] (f : ℕ) {J : Finset (Fin Tag.F4.rank)}
    (i₀ : Fin Tag.F4.rank) {P : Subgroup (ModGL Tag.F4 L)}
    (hP : QPFactor (qpRep L) (Units.map (entrywiseHom (iterateFrobenius L 2 f)))
      (parabolicRoots Tag.F4 (J : Set (Fin Tag.F4.rank))) P)
    (hroot : ∃ h₀ : ModGL Tag.F4 L, h₀ ∈ adjointGroup Tag.F4 L ∧
        ∀ Y : SL2 K, h₀ * simpleRootSL2 Tag.F4 L i₀
          (Matrix.SpecialLinearGroup.map (algebraMap K L) Y) * h₀⁻¹ ∈ P) :
    QPFam L K f J i₀ := by
  refine ⟨Unit, fun _ => P, hP.isSigmaFamily (fun α hα => hα.1), ?_, ?_, ?_⟩
  · rw [iSup_const]; exact hP.eq
  · rw [iSup_const]; exact layer_eq_top_of_isQuasisimple hP.quasi
  · rw [iSup_const]; exact hroot

theorem exists_corestriction {K : Type} [Field K] [Algebra K L] (f : ℕ)
    (hK : ∀ a : K, iterateFrobenius L 2 f (algebraMap K L a) = algebraMap K L a) :
    ∃ κ : K →+* qpK L f, (qpK L f).subtype.comp κ = algebraMap K L :=
  ⟨(algebraMap K L).codRestrict (qpK L f) (fun a => hK a), by ext a; rfl⟩

theorem qp_rootclause {K : Type} [Field K] [Algebra K L] (f : ℕ)
    (hK : ∀ a : K, iterateFrobenius L 2 f (algebraMap K L a) = algebraMap K L a)
    {J : Finset (Fin Tag.F4.rank)} {C : List (Fin Tag.F4.rank → ℤ)} (hC : QPCascade J C)
    (ω : L) {i₀ : Fin Tag.F4.rank} (hi₀ : i₀ ∈ J) :
    ∃ h₀ : ModGL Tag.F4 L, h₀ ∈ adjointGroup Tag.F4 L ∧
      ∀ Y : SL2 K, h₀ * simpleRootSL2 Tag.F4 L i₀
        (Matrix.SpecialLinearGroup.map (algebraMap K L) Y) * h₀⁻¹ ∈
          qpFix f (J : Set (Fin Tag.F4.rank)) (qpCas C (qpA ω)⁻¹) := by
  obtain ⟨κ, hκ⟩ := exists_corestriction (L := L) f hK
  refine ⟨qpCas C (qpA ω)⁻¹,
    CFSG.LieType.Chevalley.rootSpan_le_adjointGroup L _ (qpCas_mem_rootSpan hC _), fun Y => ?_⟩
  have hmap : Matrix.SpecialLinearGroup.map (qpK L f).subtype
      (Matrix.SpecialLinearGroup.map κ Y) = Matrix.SpecialLinearGroup.map (algebraMap K L) Y := by
    apply Subtype.ext
    ext a b
    have := congrArg (fun φ : K →+* L => φ ((Y : Matrix (Fin 2) (Fin 2) K) a b)) hκ
    simpa using this
  have := qpFix_rootSL2_mem f (J := (J : Set (Fin Tag.F4.rank))) (Finset.mem_coe.2 hi₀)
    (qpCas C (qpA ω)⁻¹) (Matrix.SpecialLinearGroup.map κ Y)
  rwa [hmap] at this

theorem qpFam_connected {K : Type} [Field K] [Algebra K L] (f : ℕ) [Finite (qpK L f)]
    (h4 : 4 ≤ Nat.card (qpK L f))
    (hK : ∀ a : K, iterateFrobenius L 2 f (algebraMap K L a) = algebraMap K L a)
    (hf : 1 ≤ f) {J : Finset (Fin Tag.F4.rank)} {C : List (Fin Tag.F4.rank → ℤ)}
    (hC : QPCascade J C) (hJne : (J : Set (Fin Tag.F4.rank)).Nonempty)
    (hconn : ∀ i ∈ (J : Set (Fin Tag.F4.rank)), ∀ j ∈ (J : Set (Fin Tag.F4.rank)), ∀ k,
      i ≤ k → k ≤ j → k ∈ (J : Set (Fin Tag.F4.rank)))
    {i₀ : Fin Tag.F4.rank} (hi₀ : i₀ ∈ J) : QPFam L K f J i₀ := by
  obtain ⟨ω, hω⟩ := exists_qpOmega (Ω := L) hf
  exact qpFam_of_factor f i₀ (qp_factor_connected f h4 hC hJne hconn hω)
    (qp_rootclause f hK hC ω hi₀)

end Fam

section Checks

variable {L : Type} [Field L] [CharP L 2] [IsAlgClosed L]

omit
  [CharP L 2] [IsAlgClosed L] in
theorem rootSpan_commute_of_gen {S₁ S₂ : Set (Fin Tag.F4.rank → ℤ)}
    (h : ∀ α ∈ S₁, ∀ β ∈ S₂, ∀ c d : L,
      pinnedX Tag.F4 L α c * pinnedX Tag.F4 L β d = pinnedX Tag.F4 L β d * pinnedX Tag.F4 L α c) :
    ∀ u ∈ rootSpan Tag.F4 L S₁, ∀ v ∈ rootSpan Tag.F4 L S₂, u * v = v * u := by
  have hle : rootSpan Tag.F4 L S₁ ≤
      Subgroup.centralizer (rootSpan Tag.F4 L S₂ : Set (ModGL Tag.F4 L)) := by
    refine iSup₂_le fun α hα => ?_
    rw [rootSubgroup, Subgroup.closure_le]
    rintro _ ⟨c, rfl⟩
    rw [SetLike.mem_coe, Subgroup.mem_centralizer_iff]
    intro v hv
    have hle2 : rootSpan Tag.F4 L S₂ ≤
        Subgroup.centralizer ({pinnedX Tag.F4 L α c} : Set (ModGL Tag.F4 L)) := by
      refine iSup₂_le fun β hβ => ?_
      rw [rootSubgroup, Subgroup.closure_le]
      rintro _ ⟨d, rfl⟩
      rw [SetLike.mem_coe, Subgroup.mem_centralizer_singleton_iff]
      exact (h α hα β hβ c d).symm
    exact Subgroup.mem_centralizer_singleton_iff.1 (hle2 hv)
  intro u hu v hv
  exact (Subgroup.mem_centralizer_iff.1 (hle hu) v hv).symm

@[expose] def qpOrthSuppB (J₁ J₂ : Finset (Fin Tag.F4.rank)) : Bool :=
  (List.finRange 48).all fun m => (List.finRange 48).all fun m' =>
    !decide (∀ i : Fin Tag.F4.rank, i ∉ J₁ → f4RootVec m i = 0) ||
      !decide (∀ i : Fin Tag.F4.rank, i ∉ J₂ → f4RootVec m' i = 0) ||
        (decide (CFSG.LieType.Steinberg.Adjoint.iform (τ := Tag.F4) (f4RootVec m)
          (f4RootVec m') = 0) && !f4IsRootB (f4RootVec m + f4RootVec m'))

theorem qp_roots_orth {J₁ J₂ : Finset (Fin Tag.F4.rank)} (h : qpOrthSuppB J₁ J₂ = true) :
    ∀ α ∈ parabolicRoots Tag.F4 (J₁ : Set (Fin Tag.F4.rank)),
      ∀ β ∈ parabolicRoots Tag.F4 (J₂ : Set (Fin Tag.F4.rank)),
        CFSG.LieType.Steinberg.Adjoint.iform α β = 0 ∧ ¬ IsRoot Tag.F4 (α + β) := by
  intro α hα β hβ
  obtain ⟨m, rfl⟩ := isRoot_iff_exists_f4RootVec.1 hα.1
  obtain ⟨m', rfl⟩ := isRoot_iff_exists_f4RootVec.1 hβ.1
  simp only [qpOrthSuppB, List.all_eq_true, Bool.or_eq_true, Bool.and_eq_true, Bool.not_eq_true',
    decide_eq_false_iff_not, decide_eq_true_eq] at h
  have h1 := h m (List.mem_finRange m) m' (List.mem_finRange m')
  have hα' : ∀ i : Fin Tag.F4.rank, i ∉ J₁ → f4RootVec m i = 0 := fun i hi =>
    hα.2 i (by simpa using hi)
  have hβ' : ∀ i : Fin Tag.F4.rank, i ∉ J₂ → f4RootVec m' i = 0 := fun i hi =>
    hβ.2 i (by simpa using hi)
  rcases h1 with (h1 | h1) | h1
  · exact absurd hα' h1
  · exact absurd hβ' h1
  · refine ⟨h1.1, fun hr => ?_⟩
    have := isRoot_iff_f4IsRootB.1 hr
    rw [h1.2] at this
    exact absurd this (by simp)

omit [CharP L 2] [IsAlgClosed L] in
theorem qp_comm_of_check {J₁ J₂ : Finset (Fin Tag.F4.rank)} (h : qpOrthSuppB J₁ J₂ = true) :
    ∀ u ∈ rootSpan Tag.F4 L (parabolicRoots Tag.F4 (J₁ : Set (Fin Tag.F4.rank))),
      ∀ v ∈ rootSpan Tag.F4 L (parabolicRoots Tag.F4 (J₂ : Set (Fin Tag.F4.rank))),
        u * v = v * u :=
  rootSpan_commute_of_gen fun α hα β hβ c d =>
    pinnedX_commute_of_iform_eq_zero L hα.1 hβ.1 (qp_roots_orth h α hα β hβ).1
      (qp_roots_orth h α hα β hβ).2 c d

@[expose] def qpUnionB (J J₁ J₂ : Finset (Fin Tag.F4.rank)) : Bool :=
  (List.finRange 48).all fun m =>
    decide ((∀ i : Fin Tag.F4.rank, i ∉ J → f4RootVec m i = 0) ↔
      ((∀ i : Fin Tag.F4.rank, i ∉ J₁ → f4RootVec m i = 0) ∨
        (∀ i : Fin Tag.F4.rank, i ∉ J₂ → f4RootVec m i = 0)))

theorem parabolicRoots_union_of_check {J J₁ J₂ : Finset (Fin Tag.F4.rank)}
    (h : qpUnionB J J₁ J₂ = true) :
    parabolicRoots Tag.F4 (J : Set (Fin Tag.F4.rank)) =
      parabolicRoots Tag.F4 (J₁ : Set (Fin Tag.F4.rank)) ∪
        parabolicRoots Tag.F4 (J₂ : Set (Fin Tag.F4.rank)) := by
  simp only [qpUnionB, List.all_eq_true, decide_eq_true_eq] at h
  ext α
  constructor
  · intro hα
    obtain ⟨m, rfl⟩ := isRoot_iff_exists_f4RootVec.1 hα.1
    have := (h m (List.mem_finRange m)).1 (fun i hi => hα.2 i (by simpa using hi))
    rcases this with h1 | h1
    · exact Or.inl ⟨hα.1, fun i hi => h1 i (by simpa using hi)⟩
    · exact Or.inr ⟨hα.1, fun i hi => h1 i (by simpa using hi)⟩
  · rintro (hα | hα)
    · obtain ⟨m, rfl⟩ := isRoot_iff_exists_f4RootVec.1 hα.1
      exact ⟨hα.1, fun i hi => ((h m (List.mem_finRange m)).2 (Or.inl fun j hj =>
        hα.2 j (by simpa using hj))) i (by simpa using hi)⟩
    · obtain ⟨m, rfl⟩ := isRoot_iff_exists_f4RootVec.1 hα.1
      exact ⟨hα.1, fun i hi => ((h m (List.mem_finRange m)).2 (Or.inr fun j hj =>
        hα.2 j (by simpa using hj))) i (by simpa using hi)⟩

@[expose] def qpA1B (a : Fin Tag.F4.rank) : Bool :=
  (List.finRange 48).all fun m =>
    decide ((∀ i : Fin Tag.F4.rank, i ∉ ({a} : Finset (Fin Tag.F4.rank)) → f4RootVec m i = 0) ↔
      (f4RootVec m = Pi.single a 1 ∨ f4RootVec m = -Pi.single a 1))

theorem parabolicRoots_single_of_check {a : Fin Tag.F4.rank} (h : qpA1B a = true) :
    parabolicRoots Tag.F4 (({a} : Finset (Fin Tag.F4.rank)) : Set (Fin Tag.F4.rank)) =
      {Pi.single a 1, -Pi.single a 1} := by
  simp only [qpA1B, List.all_eq_true, decide_eq_true_eq] at h
  ext α
  constructor
  · intro hα
    obtain ⟨m, rfl⟩ := isRoot_iff_exists_f4RootVec.1 hα.1
    exact (h m (List.mem_finRange m)).1 (fun i hi => hα.2 i (by simpa using hi))
  · intro hα
    have hr : IsRoot Tag.F4 α := by
      rcases hα with rfl | rfl
      · exact isRoot_single Tag.F4 a
      · exact IsRoot.neg (isRoot_single Tag.F4 a)
    obtain ⟨m, rfl⟩ := isRoot_iff_exists_f4RootVec.1 hr
    exact ⟨hr, fun i hi => (h m (List.mem_finRange m)).2 hα i (by simpa using hi)⟩

omit [IsAlgClosed L] in
theorem qp_hcen_single {a : Fin Tag.F4.rank} (h : qpA1B a = true) :
    ∀ g ∈ rootSpan Tag.F4 L
        (parabolicRoots Tag.F4 (({a} : Finset (Fin Tag.F4.rank)) : Set (Fin Tag.F4.rank))),
      (∀ h' ∈ rootSpan Tag.F4 L
        (parabolicRoots Tag.F4 (({a} : Finset (Fin Tag.F4.rank)) : Set (Fin Tag.F4.rank))),
        g * h' = h' * g) → g = 1 := by
  have hset := parabolicRoots_single_of_check h
  have hspan : rootSpan Tag.F4 L (parabolicRoots Tag.F4
      (({a} : Finset (Fin Tag.F4.rank)) : Set (Fin Tag.F4.rank))) =
        rootRankOneGroup Tag.F4 L (Pi.single a 1) := by
    rw [hset, rootSpan, iSup_insert, iSup_singleton, rootRankOneGroup,
      range_rootSL2_of_isRoot (isRoot_single Tag.F4 a)]
  intro g hg hc
  rw [hspan] at hg hc
  exact qp_center_rootSL2 hg hc

theorem qpFam_union {K : Type} [Field K] [Algebra K L] (f : ℕ)
    {J J₁ J₂ : Finset (Fin Tag.F4.rank)} (i₀ : Fin Tag.F4.rank)
    (hJ : parabolicRoots Tag.F4 (J : Set (Fin Tag.F4.rank)) =
      parabolicRoots Tag.F4 (J₁ : Set (Fin Tag.F4.rank)) ∪
        parabolicRoots Tag.F4 (J₂ : Set (Fin Tag.F4.rank)))
    {P₁ P₂ : Subgroup (ModGL Tag.F4 L)}
    (h₁ : QPFactor (qpRep L) (Units.map (entrywiseHom (iterateFrobenius L 2 f)))
      (parabolicRoots Tag.F4 (J₁ : Set (Fin Tag.F4.rank))) P₁)
    (h₂ : QPFactor (qpRep L) (Units.map (entrywiseHom (iterateFrobenius L 2 f)))
      (parabolicRoots Tag.F4 (J₂ : Set (Fin Tag.F4.rank))) P₂)
    (hfree : QPFree (parabolicRoots Tag.F4 (J₂ : Set (Fin Tag.F4.rank))) P₂)
    (hcomm : ∀ u ∈ rootSpan Tag.F4 L (parabolicRoots Tag.F4 (J₁ : Set (Fin Tag.F4.rank))),
      ∀ v ∈ rootSpan Tag.F4 L (parabolicRoots Tag.F4 (J₂ : Set (Fin Tag.F4.rank))), u * v = v * u)
    (hcen : ∀ g ∈ rootSpan Tag.F4 L (parabolicRoots Tag.F4 (J₂ : Set (Fin Tag.F4.rank))),
      (∀ h ∈ rootSpan Tag.F4 L (parabolicRoots Tag.F4 (J₂ : Set (Fin Tag.F4.rank))),
        g * h = h * g) → g = 1)
    (hroot : ∃ h₀ : ModGL Tag.F4 L, h₀ ∈ adjointGroup Tag.F4 L ∧
        ∀ Y : SL2 K, h₀ * simpleRootSL2 Tag.F4 L i₀
          (Matrix.SpecialLinearGroup.map (algebraMap K L) Y) * h₀⁻¹ ∈ P₁ ⊔ P₂) :
    QPFam L K f J i₀ := by
  have hS₁ : ∀ α ∈ parabolicRoots Tag.F4 (J₁ : Set (Fin Tag.F4.rank)), IsRoot Tag.F4 α :=
    fun α hα => hα.1
  have hS₂ : ∀ α ∈ parabolicRoots Tag.F4 (J₂ : Set (Fin Tag.F4.rank)), IsRoot Tag.F4 α :=
    fun α hα => hα.1
  have hS₁n : ∀ α ∈ parabolicRoots Tag.F4 (J₁ : Set (Fin Tag.F4.rank)),
      -α ∈ parabolicRoots Tag.F4 (J₁ : Set (Fin Tag.F4.rank)) := fun α hα =>
    neg_mem_parabolicRoots hα
  have hS₂n : ∀ α ∈ parabolicRoots Tag.F4 (J₂ : Set (Fin Tag.F4.rank)),
      -α ∈ parabolicRoots Tag.F4 (J₂ : Set (Fin Tag.F4.rank)) := fun α hα =>
    neg_mem_parabolicRoots hα
  have hsup : (⨆ b : Bool, (bif b then P₁ else P₂)) = P₁ ⊔ P₂ := by
    rw [iSup_bool_eq]; rfl
  refine ⟨Bool, fun b => bif b then P₁ else P₂, ?_, ?_, ?_, ?_⟩
  · rw [hJ]
    exact qp_union_family hS₁ hS₂ hcomm h₁ h₂ hfree
  · rw [hsup, hJ]
    exact qp_union_fixed_eq _ hS₁ hS₂ hS₁n hS₂n hcomm hcen h₁.eq h₂.eq
  · rw [hsup]
    refine qp_layer_sup_eq_top h₁.quasi h₂.quasi fun u hu v hv => ?_
    rw [h₁.eq] at hu
    rw [h₂.eq] at hv
    exact hcomm u hu.1 v hv.1
  · rw [hsup]; exact hroot

theorem connected_singleton (a : Fin Tag.F4.rank) :
    ∀ i ∈ (({a} : Finset (Fin Tag.F4.rank)) : Set (Fin Tag.F4.rank)),
      ∀ j ∈ (({a} : Finset (Fin Tag.F4.rank)) : Set (Fin Tag.F4.rank)), ∀ k,
        i ≤ k → k ≤ j → k ∈ (({a} : Finset (Fin Tag.F4.rank)) : Set (Fin Tag.F4.rank)) := by
  intro i hi j hj k hik hkj
  simp only [Finset.coe_singleton, Set.mem_singleton_iff] at hi hj ⊢
  subst hi; subst hj
  exact le_antisymm hkj hik

theorem qpFam_A1A1 {K : Type} [Field K] [Algebra K L] (f : ℕ) [Finite (qpK L f)]
    (h4 : 4 ≤ Nat.card (qpK L f))
    (hK : ∀ a : K, iterateFrobenius L 2 f (algebraMap K L a) = algebraMap K L a)
    (hf : 1 ≤ f) {a b : Fin Tag.F4.rank} {Ca Cb : List (Fin Tag.F4.rank → ℤ)}
    (hCa : QPCascade {a} Ca) (hCb : QPCascade {b} Cb)
    (hO : qpOrthSuppB {a} {b} = true) (hU : qpUnionB {a, b} {a} {b} = true)
    (hA : qpA1B b = true) : QPFam L K f {a, b} b := by
  obtain ⟨ω, hω⟩ := exists_qpOmega (Ω := L) hf
  have hne : ∀ c : Fin Tag.F4.rank, (({c} : Finset (Fin Tag.F4.rank)) :
      Set (Fin Tag.F4.rank)).Nonempty := fun c => ⟨c, by simp⟩
  have h₁ := qp_factor_connected f h4 hCa (hne a) (connected_singleton a) hω
  have h₂ := qp_factor_connected f h4 hCb (hne b) (connected_singleton b) hω
  refine qpFam_union f b (parabolicRoots_union_of_check hU) h₁ h₂ (qpFix_free f h4 hCb ω)
    (qp_comm_of_check hO) (qp_hcen_single hA) ?_
  obtain ⟨h₀, hh₀, hY⟩ := qp_rootclause f hK hCb ω (Finset.mem_singleton_self b)
  exact ⟨h₀, hh₀, fun Y => Subgroup.mem_sup_right (hY Y)⟩

end Checks

end CFSG.RankThree.PartOne.KF4
