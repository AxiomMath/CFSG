module

public import CFSG.LocalAnalysis.StandardType.GGE8TwoFiveKernel
public import CFSG.LocalAnalysis.StandardType.GGLangRatSingleOrbit
public import CFSG.LocalAnalysis.GLTheoremA.CatC.RationalTypeAModel
public import CFSG.HardMathSupport.Dickson.Sec6.Up34Chev2Aux.InnExcSuNHom
public import CFSG.HardMathSupport.Timmesfeld.CrossChar.TwCompSUE8
public import CFSG.HardMathSupport.Timmesfeld.CrossChar.SplitLineFix
public import CFSG.HardMathSupport.Timmesfeld.LangTorus.Subnormal
public import CFSG.HardMathSupport.Timmesfeld.Steinberg.PrimeCentralizer
public import CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6ThreeTwNotAll24A2CubeIndexLang
public import CFSG.LocalAnalysis.GLTheoremA.CatA.KD147cMat
public import CFSG.LocalAnalysis.StandardType.GGTableBNbrInnerUnitaryHypCentral
public import TauCeti.GroupTheory.SemidirectProduct
public import CFSG.LieType.SeitzGeneration.SeitzStatus

public section

namespace CFSG.StandardType

namespace FieldFiveE8

open CFSG.Assembly CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LieType.AlgebraicGroups CFSG.LieType.Steinberg.Adjoint
  CFSG.HardMathSupport.Timmesfeld.LangTorus CFSG.HardMathSupport.Timmesfeld.CrossChar
  CFSG.StandardType.OmNonsplit CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley CFSG.RankThree.PartOne.KE
  CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.TwE6UniqAbs
open CFSG.LocalAnalysis.GLTheoremA (kd147c_frameRoots_ncard)
open scoped MatrixGroups
open scoped commutatorElement

private theorem e8f5a_kernelRoots_eq {L : Type} [Field L] {a : Fin Tag.E8.rank → Lˣ}
    {i₁ i₂ : KernelComponent (rootCharHom a)} (hall : ∀ k, k = i₁ ∨ k = i₂) :
    kernelRoots (rootCharHom a) =
      componentRoots (rootCharHom a) i₁ ∪ componentRoots (rootCharHom a) i₂ := by
  ext γ
  constructor
  · intro hγ
    have hmem : γ ∈ componentRoots (rootCharHom a) (⟦⟨γ, hγ⟩⟧ : KernelComponent (rootCharHom a)) :=
      ⟨hγ, rfl⟩
    rcases hall ⟦⟨γ, hγ⟩⟧ with h | h
    · exact Or.inl (h ▸ hmem)
    · exact Or.inr (h ▸ hmem)
  · rintro (⟨hγ, -⟩ | ⟨hγ, -⟩) <;> exact hγ

private theorem e8f5a_swap
    {L : Type} [Field L] [IsAlgClosed L] (S : LangSetup Tag.E8 L 5) {a : Fin Tag.E8.rank → Lˣ}
    (h : E8TwoFiveSetup S a) (hA : E8TwoFiveKernelA S.ρ (rootCharHom a)) :
    ∃ i₁ i₂ : KernelComponent (rootCharHom a), i₁ ≠ i₂ ∧ (∀ k, k = i₁ ∨ k = i₂) ∧
      compRank (componentRoots (rootCharHom a) i₁) = 4 ∧
      (componentRoots (rootCharHom a) i₁).ncard = 20 ∧
      twistKind S.ρ (rootCharHom a) i₁ = .suN ∧
      (S.ρ : (Fin Tag.E8.rank → ℤ) → _) '' componentRoots (rootCharHom a) i₁ =
        componentRoots (rootCharHom a) i₂ ∧
      (S.ρ : (Fin Tag.E8.rank → ℤ) → _) '' componentRoots (rootCharHom a) i₂ =
        componentRoots (rootCharHom a) i₁ := by
  obtain ⟨-, i₁, i₂, hne, hall, hrk, hcard, himg, hkind⟩ := hA
  refine ⟨i₁, i₂, hne, hall, hrk, hcard, hkind, himg, ?_⟩
  have hρ2 : (S.ρ : (Fin Tag.E8.rank → ℤ) → _)^[2] '' componentRoots (rootCharHom a) i₁ =
      componentRoots (rootCharHom a) i₁ := by
    obtain ⟨j', hj'⟩ := outer_iterate_image_component S h.2.1 i₁ 2
    rcases hall j' with h | h
    · rw [← hj', h]
    · exfalso
      have h2 : (S.ρ : (Fin Tag.E8.rank → ℤ) → _)^[2] ''
            componentRoots (rootCharHom a) i₁ =
          (S.ρ : (Fin Tag.E8.rank → ℤ) → _) '' componentRoots (rootCharHom a) i₁ :=
        (h ▸ hj').symm.trans himg.symm
      rw [Set.image_iterate_eq] at h2
      have h4 : (S.ρ : (Fin Tag.E8.rank → ℤ) → _) '' componentRoots (rootCharHom a) i₁ =
          componentRoots (rootCharHom a) i₁ := Set.image_injective.2 S.ρ.injective h2
      exact (fun h => hne (eq_of_componentRoots_eq h)) (himg.symm.trans h4).symm
  rw [← himg]
  exact (congrFun (Set.image_iterate_eq
    (f := (S.ρ : (Fin Tag.E8.rank → ℤ) → _)) (n := 2))
    (componentRoots (rootCharHom a) i₁)).symm.trans hρ2

private theorem e8f5a_rationalRoots_eq
    {L : Type} [Field L] [IsAlgClosed L] (S : LangSetup Tag.E8 L 5) {a : Fin Tag.E8.rank → Lˣ}
    (h : E8TwoFiveSetup S a) (hA : E8TwoFiveKernelA S.ρ (rootCharHom a))
    (i : KernelComponent (rootCharHom a)) :
    rationalRoots S.ρ (rootCharHom a) i = kernelRoots (rootCharHom a) := by
  obtain ⟨i₁, i₂, hne, hall, -, -, -, h12, h21⟩ := e8f5a_swap S h hA
  rw [e8f5a_kernelRoots_eq hall]
  have hle : ∀ k : KernelComponent (rootCharHom a), rationalRoots S.ρ (rootCharHom a) k ⊆
      componentRoots (rootCharHom a) i₁ ∪ componentRoots (rootCharHom a) i₂ := by
    intro k γ hγ
    obtain ⟨m, δ, hδ, rfl⟩ := hγ
    obtain ⟨j', hj'⟩ := outer_iterate_image_component S h.2.1 k m
    have hmem : (S.ρ : (Fin Tag.E8.rank → ℤ) → _)^[m] δ ∈ componentRoots (rootCharHom a) j' := by
      rw [hj']
      exact ⟨δ, hδ, rfl⟩
    rcases hall j' with h | h
    · exact Or.inl (h ▸ hmem)
    · exact Or.inr (h ▸ hmem)
  have hge : ∀ k : KernelComponent (rootCharHom a),
      componentRoots (rootCharHom a) i₁ ∪ componentRoots (rootCharHom a) i₂ ⊆
        rationalRoots S.ρ (rootCharHom a) k := by
    intro k
    have hsub : ∀ γ ∈ componentRoots (rootCharHom a) k,
        γ ∈ rationalRoots S.ρ (rootCharHom a) k := fun γ hγ => ⟨0, γ, hγ, rfl⟩
    have himg' : (S.ρ : (Fin Tag.E8.rank → ℤ) → _) '' componentRoots (rootCharHom a) k ⊆
        rationalRoots S.ρ (rootCharHom a) k := by
      rintro _ ⟨δ, hδ, rfl⟩
      exact ⟨1, δ, hδ, rfl⟩
    rcases hall k with rfl | rfl
    · rintro γ (hγ | hγ)
      · exact hsub γ hγ
      · exact himg' (h12 ▸ hγ)
    · rintro γ (hγ | hγ)
      · exact himg' (h21 ▸ hγ)
      · exact hsub γ hγ
  exact Set.Subset.antisymm (hle i) (hge i)

private theorem e8f5a_orbitLength_two
    {L : Type} [Field L] [IsAlgClosed L] (S : LangSetup Tag.E8 L 5) {a : Fin Tag.E8.rank → Lˣ}
    (h : E8TwoFiveSetup S a) (hA : E8TwoFiveKernelA S.ρ (rootCharHom a))
    (i : KernelComponent (rootCharHom a)) :
    componentOrbitLength S.ρ (componentRoots (rootCharHom a) i) = 2 := by
  obtain ⟨i₁, i₂, hne, hall, -, -, -, h12, h21⟩ := e8f5a_swap S h hA
  obtain ⟨hs0, hs, hmin⟩ := outer_componentOrbitLength_spec S h.2.1 i
  generalize componentOrbitLength S.ρ (componentRoots (rootCharHom a) i) = s at hs0 hs hmin ⊢
  have h2 : (S.ρ : (Fin Tag.E8.rank → ℤ) → _)^[2] '' componentRoots (rootCharHom a) i =
      componentRoots (rootCharHom a) i := by
    have h2' : (S.ρ : (Fin Tag.E8.rank → ℤ) → _)^[2] '' componentRoots (rootCharHom a) i =
        (S.ρ : (Fin Tag.E8.rank → ℤ) → _) ''
          ((S.ρ : (Fin Tag.E8.rank → ℤ) → _) '' componentRoots (rootCharHom a) i) :=
      congrFun (Set.image_iterate_eq (f := (S.ρ : (Fin Tag.E8.rank → ℤ) → _)) (n := 2)) _
    rw [h2']
    rcases hall i with rfl | rfl
    · rw [h12, h21]
    · rw [h21, h12]
  have h1 : (S.ρ : (Fin Tag.E8.rank → ℤ) → _) '' componentRoots (rootCharHom a) i ≠
      componentRoots (rootCharHom a) i := by
    rcases hall i with rfl | rfl
    · rw [h12]
      exact fun h => hne (eq_of_componentRoots_eq h.symm)
    · rw [h21]
      exact fun h => hne (eq_of_componentRoots_eq h)
  rcases Nat.lt_trichotomy s 2 with hlt | heq | hgt
  · have hs1 : s = 1 := by omega
    subst hs1
    exact absurd (by simpa using hs) h1
  · exact heq
  · exact absurd h2 (hmin 2 (by norm_num) hgt)

private def e8f5a_j1_toQ (γ : Fin Tag.E8.rank → ℤ) : Fin Tag.E8.rank → ℚ := fun i => (γ i : ℚ)

private def e8f5a_j1_qform (x y : Fin Tag.E8.rank → ℚ) : ℚ :=
  dotProduct x (Matrix.mulVec ((Tag.E8.symmetrizedCartan).map (Int.cast : ℤ → ℚ)) y)

private theorem e8f5a_j1_qform_toQ (β γ : Fin Tag.E8.rank → ℤ) :
    e8f5a_j1_qform (e8f5a_j1_toQ β) (e8f5a_j1_toQ γ) =
      (CFSG.LieType.Steinberg.Adjoint.iform β γ : ℚ) := by
  rw [← CFSG.LieType.Chevalley.dotProduct_mulVec_eq_iform β γ]
  simp only [e8f5a_j1_qform, e8f5a_j1_toQ, dotProduct, Matrix.mulVec, Matrix.map_apply,
    Finset.mul_sum]
  push_cast
  ring

private theorem e8f5a_j1_qform_add_left (x₁ x₂ y : Fin Tag.E8.rank → ℚ) :
    e8f5a_j1_qform (x₁ + x₂) y = e8f5a_j1_qform x₁ y + e8f5a_j1_qform x₂ y := by
  simp only [e8f5a_j1_qform, dotProduct, Pi.add_apply, Finset.sum_add_distrib, add_mul]

private theorem e8f5a_j1_qform_smul_left (a : ℚ) (x y : Fin Tag.E8.rank → ℚ) :
    e8f5a_j1_qform (a • x) y = a * e8f5a_j1_qform x y := by
  simp only [e8f5a_j1_qform, dotProduct, Pi.smul_apply, Finset.mul_sum, smul_eq_mul]
  exact Finset.sum_congr rfl fun i _ => by ring

private theorem e8f5a_j1_qform_add_right (x y₁ y₂ : Fin Tag.E8.rank → ℚ) :
    e8f5a_j1_qform x (y₁ + y₂) = e8f5a_j1_qform x y₁ + e8f5a_j1_qform x y₂ := by
  simp only [e8f5a_j1_qform, dotProduct, Matrix.mulVec_add, Pi.add_apply,
    Finset.sum_add_distrib, mul_add]

private theorem e8f5a_j1_qform_smul_right (a : ℚ) (x y : Fin Tag.E8.rank → ℚ) :
    e8f5a_j1_qform x (a • y) = a * e8f5a_j1_qform x y := by
  simp only [e8f5a_j1_qform, dotProduct, Matrix.mulVec_smul, Pi.smul_apply, smul_eq_mul]
  rw [Finset.mul_sum]
  exact Finset.sum_congr rfl fun i _ => by ring

private theorem e8f5a_j1_qform_pos
    {x : Fin Tag.E8.rank → ℚ} (hx : x ≠ 0) : 0 < e8f5a_j1_qform x x := by
  have hsym : Tag.E8.symmetrizedCartan = Tag.E8.cartan := by
    ext i j
    exact CFSG.RankThree.Chevalley.WeylE8.symmetrizedCartan_E8 i j
  have hpd : ((Tag.E8.symmetrizedCartan).map (Int.cast : ℤ → ℚ)).PosDef := by
    rw [hsym]
    exact e8_posDef_cartan
  simpa [e8f5a_j1_qform, Pi.star_apply] using hpd.dotProduct_mulVec_pos hx

private theorem e8f5a_j1_qform_eq_zero
    {x : Fin Tag.E8.rank → ℚ} (h : e8f5a_j1_qform x x = 0) : x = 0 := by
  by_contra hx
  exact (ne_of_gt (e8f5a_j1_qform_pos hx)) h

private theorem e8f5a_j1_qform_span_orth
    {A B : Set (Fin Tag.E8.rank → ℤ)}
    (hAB : ∀ a ∈ A, ∀ b ∈ B, CFSG.LieType.Steinberg.Adjoint.iform a b = 0) :
    ∀ x ∈ Submodule.span ℚ (e8f5a_j1_toQ '' A),
      ∀ y ∈ Submodule.span ℚ (e8f5a_j1_toQ '' B), e8f5a_j1_qform x y = 0 := by
  intro x hx
  refine Submodule.span_induction (p := fun x _ =>
    ∀ y ∈ Submodule.span ℚ (e8f5a_j1_toQ '' B), e8f5a_j1_qform x y = 0) ?_ ?_ ?_ ?_ hx
  · rintro x ⟨a, ha, rfl⟩ y hy
    refine Submodule.span_induction (p := fun y _ => e8f5a_j1_qform (e8f5a_j1_toQ a) y = 0)
      ?_ ?_ ?_ ?_ hy
    · rintro y ⟨b, hb, rfl⟩
      rw [e8f5a_j1_qform_toQ, hAB a ha b hb]
      simp
    · simp [e8f5a_j1_qform]
    · intro y₁ y₂ _ _ h1 h2
      rw [e8f5a_j1_qform_add_right, h1, h2, add_zero]
    · intro c y _ h1
      rw [e8f5a_j1_qform_smul_right, h1, mul_zero]
  · intro y _
    simp [e8f5a_j1_qform]
  · intro x₁ x₂ _ _ h1 h2 y hy
    rw [e8f5a_j1_qform_add_left, h1 y hy, h2 y hy, add_zero]
  · intro c x _ h1 y hy
    rw [e8f5a_j1_qform_smul_left, h1 y hy, mul_zero]

private theorem e8f5a_j1_compRank_union_of_orth
    {A B : Set (Fin Tag.E8.rank → ℤ)}
    (hAB : ∀ a ∈ A, ∀ b ∈ B, CFSG.LieType.Steinberg.Adjoint.iform a b = 0) :
    compRank (A ∪ B) = compRank A + compRank B := by
  have hspan : Submodule.span ℚ (e8f5a_j1_toQ '' (A ∪ B)) =
      Submodule.span ℚ (e8f5a_j1_toQ '' A) ⊔ Submodule.span ℚ (e8f5a_j1_toQ '' B) := by
    rw [Set.image_union, Submodule.span_union]
  have hinf : Submodule.span ℚ (e8f5a_j1_toQ '' A) ⊓
      Submodule.span ℚ (e8f5a_j1_toQ '' B) = ⊥ := by
    rw [Submodule.eq_bot_iff]
    intro x hx
    exact e8f5a_j1_qform_eq_zero (e8f5a_j1_qform_span_orth hAB x hx.1 x hx.2)
  have h := Submodule.finrank_sup_add_finrank_inf_eq
    (Submodule.span ℚ (e8f5a_j1_toQ '' A)) (Submodule.span ℚ (e8f5a_j1_toQ '' B))
  rw [hinf, finrank_bot, add_zero] at h
  change Module.finrank ℚ (Submodule.span ℚ (e8f5a_j1_toQ '' (A ∪ B))) =
    Module.finrank ℚ (Submodule.span ℚ (e8f5a_j1_toQ '' A)) +
    Module.finrank ℚ (Submodule.span ℚ (e8f5a_j1_toQ '' B))
  rw [hspan, h]

private theorem e8f5a_rank_eight
    {L : Type} [Field L] [IsAlgClosed L] (S : LangSetup Tag.E8 L 5) {a : Fin Tag.E8.rank → Lˣ}
    (hA : E8TwoFiveKernelA S.ρ (rootCharHom a)) :
    compRank (kernelRoots (rootCharHom a)) = Tag.E8.rank := by
  classical
  obtain ⟨-, i₁, i₂, hne, hall, hrk, hcard, h12, hkind⟩ := hA
  have hker : kernelRoots (rootCharHom a) =
      componentRoots (rootCharHom a) i₁ ∪ componentRoots (rootCharHom a) i₂ :=
    e8f5a_kernelRoots_eq hall
  obtain ⟨w, hw⟩ := S.D.n_weyl
  have hτ : ∀ t : TwistTag, t.tag ≠ Tag.E8 := by
    intro t
    cases t <;> decide +kernel
  have hρ : ∀ γ ∈ componentRoots (rootCharHom a) i₁,
      (S.ρ : (Fin Tag.E8.rank → ℤ) → _) γ = w • γ :=
    fun γ hγ => S.rho_eq_smul hτ hw hγ.1.1
  have hcomp2 : compRank (componentRoots (rootCharHom a) i₂) = 4 := by
    rw [← h12]
    have heq : (S.ρ : (Fin Tag.E8.rank → ℤ) → _) '' componentRoots (rootCharHom a) i₁ =
        (fun α => w • α) '' componentRoots (rootCharHom a) i₁ := by
      ext γ
      constructor
      · rintro ⟨δ, hδ, rfl⟩
        exact ⟨δ, hδ, (hρ δ hδ).symm⟩
      · rintro ⟨δ, hδ, rfl⟩
        exact ⟨δ, hδ, hρ δ hδ⟩
    rw [heq, CFSG.HardMathSupport.Timmesfeld.LangTorus.compRank_image w
      (componentRoots (rootCharHom a) i₁), hrk]
  have horth : ∀ x ∈ componentRoots (rootCharHom a) i₁,
      ∀ y ∈ componentRoots (rootCharHom a) i₂,
        CFSG.LieType.Steinberg.Adjoint.iform x y = 0 := by
    intro x hx y hy
    obtain ⟨hxk, hxi⟩ := hx
    obtain ⟨hyk, hyi⟩ := hy
    refine CFSG.LieType.Chevalley.iform_eq_zero_of_mk_ne
      (α := ⟨x, hxk⟩) (β := ⟨y, hyk⟩) ?_
    rw [hxi, hyi]
    exact hne
  rw [hker, e8f5a_j1_compRank_union_of_orth horth, hrk, hcomp2]
  rfl

private theorem e8f5a_torus_le_rootSpan
    {L : Type} [Field L] [IsAlgClosed L] {Δ : Set (Fin Tag.E8.rank → ℤ)}
    (hΔ : ∀ β ∈ Δ, IsRoot Tag.E8 β) (hneg : ∀ β ∈ Δ, -β ∈ Δ) (hrk : compRank Δ = Tag.E8.rank)
    (b : Fin Tag.E8.rank → Lˣ) : rootDiagUnit Tag.E8 b ∈ rootSpan Tag.E8 L Δ := by
  classical
  have hfin : Module.finrank ℚ (Submodule.span ℚ (e8f5a_j1_toQ '' Δ)) = Tag.E8.rank := by
    change compRank Δ = Tag.E8.rank
    exact hrk
  obtain ⟨f, hfmem, -, hfli⟩ :=
    Submodule.exists_fun_fin_finrank_span_eq (K := ℚ) (s := e8f5a_j1_toQ '' Δ)
  let e : Fin Tag.E8.rank ≃ Fin (Module.finrank ℚ (Submodule.span ℚ (e8f5a_j1_toQ '' Δ))) :=
    Fintype.equivOfCardEq (by simp [hfin])
  choose β hβmem hβeq using fun i => hfmem (e i)
  have hβroot : ∀ i, IsRoot Tag.E8 (β i) := fun i => hΔ (β i) (hβmem i)
  have hβli : LinearIndependent ℚ (fun i => e8f5a_j1_toQ (β i)) := by
    have h1 : (fun i => e8f5a_j1_toQ (β i)) = f ∘ e := by
      funext i
      exact hβeq i
    rw [h1]
    exact hfli.comp e e.injective
  let E : Matrix (Fin Tag.E8.rank) (Fin Tag.E8.rank) ℤ :=
    fun i j => corootPair (β i) (Pi.single j 1)
  have hE : E = (Matrix.of fun i j => β i j) * Tag.E8.symmetrizedCartan := by
    ext i j
    change corootPair (β i) (Pi.single j 1) =
      ((Matrix.of fun i j => β i j) * Tag.E8.symmetrizedCartan) i j
    rw [Matrix.mul_apply]
    have h2 : iform (β i) (β i) = 2 := by
      have h := CFSG.LieType.Chevalley.rootForm_self (Or.inr (Or.inr (Or.inr rfl))) (hβroot i)
      rwa [CFSG.LieType.Chevalley.dotProduct_mulVec_eq_iform] at h
    have hcp : corootPair (β i) (Pi.single j 1) = iform (β i) (Pi.single j 1) := by
      have h := CFSG.LieType.Chevalley.corootPair_mul (hβroot i) (Pi.single j 1)
      rw [h2] at h
      omega
    rw [hcp, ← CFSG.LieType.Chevalley.dotProduct_mulVec_eq_iform,
      CFSG.LieType.Chevalley.dotProduct_mulVec_symmetrizedCartan_eq_sum]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [Finset.sum_eq_single j]
    · simp
    · intro b _ hb
      rw [Pi.single_eq_of_ne hb, mul_zero]
    · intro hj
      exact absurd (Finset.mem_univ j) hj
  have hdet : E.det ≠ 0 := by
    have hsym : Tag.E8.symmetrizedCartan = Tag.E8.cartan := by
      ext i j
      exact CFSG.RankThree.Chevalley.WeylE8.symmetrizedCartan_E8 i j
    have hdetcart : Tag.E8.symmetrizedCartan.det = 1 := by
      rw [hsym, CFSG.LieType.Chevalley.det_cartan_E8]
    have hMdet : ((Matrix.of fun i j => β i j).map (Int.cast : ℤ → ℚ)).det ≠ 0 := by
      have hrows : LinearIndependent ℚ
          (fun i => ((Matrix.of fun i j => β i j).map (Int.cast : ℤ → ℚ)) i) := by
        have hfun : (fun i => ((Matrix.of fun i j => β i j).map (Int.cast : ℤ → ℚ)) i) =
            (fun i => e8f5a_j1_toQ (β i)) := by
          funext i j
          rfl
        rw [hfun]
        exact hβli
      exact (Matrix.nonsingular_iff_det_ne_zero).1
        (Matrix.Nonsingular.of_linearIndependent_row hrows)
    have hMdetZ : (Matrix.of fun i j => β i j).det ≠ 0 := by
      intro h0
      have h1 := RingHom.map_det (Int.castRingHom ℚ) (Matrix.of fun i j => β i j)
      rw [h0] at h1
      simp only [map_zero] at h1
      exact hMdet h1.symm
    rw [hE, Matrix.det_mul, hdetcart, mul_one]
    exact hMdetZ
  have hroot : ∀ j : Fin Tag.E8.rank, ∃ f : Lˣ, f ^ E.det = b j := by
    intro j
    have hpos : 0 < E.det.natAbs := Int.natAbs_pos.2 hdet
    have hn0 : E.det.natAbs ≠ 0 := by omega
    rcases Int.natAbs_eq E.det with h | h
    · obtain ⟨f, hf⟩ := IsAlgClosed.exists_pow_nat_eq (b j : L) hpos
      have hf0 : f ≠ 0 := by
        intro h0
        rw [h0, zero_pow hn0] at hf
        exact (b j).ne_zero hf.symm
      refine ⟨Units.mk0 f hf0, ?_⟩
      rw [h, zpow_natCast]
      exact Units.ext (by simpa using hf)
    · obtain ⟨f, hf⟩ := IsAlgClosed.exists_pow_nat_eq ((b j)⁻¹ : L) hpos
      have hf0 : f ≠ 0 := by
        intro h0
        rw [h0, zero_pow hn0] at hf
        exact (inv_ne_zero (b j).ne_zero) hf.symm
      refine ⟨Units.mk0 f hf0, ?_⟩
      rw [h, zpow_neg, zpow_natCast,
        show (Units.mk0 f hf0 : Lˣ) ^ E.det.natAbs = (b j)⁻¹ from Units.ext (by simpa using hf)]
      simp
  choose f hf using hroot
  let c : Fin Tag.E8.rank → Lˣ := fun i => ∏ j, f j ^ E.adjugate j i
  have hc : ∀ j, ∏ i, c i ^ E i j = b j := by
    intro j
    have hcalc : ∏ i, (∏ k, f k ^ E.adjugate k i) ^ E i j =
        ∏ k, f k ^ (∑ i, E.adjugate k i * E i j) := by
      calc ∏ i, (∏ k, f k ^ E.adjugate k i) ^ E i j
          = ∏ i, ∏ k, (f k ^ E.adjugate k i) ^ E i j :=
            Finset.prod_congr rfl fun i _ => (Finset.prod_zpow _ _ _).symm
        _ = ∏ k, ∏ i, (f k ^ E.adjugate k i) ^ E i j := Finset.prod_comm
        _ = ∏ k, ∏ i, f k ^ (E.adjugate k i * E i j) :=
            Finset.prod_congr rfl fun k _ => Finset.prod_congr rfl fun i _ => by rw [zpow_mul]
        _ = ∏ k, f k ^ (∑ i, E.adjugate k i * E i j) :=
            Finset.prod_congr rfl fun k _ => by rw [Finset.prod_zpow_eq_zpow_sum]
    rw [hcalc]
    have hsum : ∀ k, ∑ i, E.adjugate k i * E i j = E.det * (if k = j then 1 else 0) := by
      intro k
      have h1 := congrFun (congrFun (Matrix.adjugate_mul E) k) j
      simp only [Matrix.mul_apply, Matrix.smul_apply, Matrix.one_apply, smul_eq_mul] at h1
      rw [h1]
    rw [show (∏ k, f k ^ (∑ i, E.adjugate k i * E i j)) =
        ∏ k, f k ^ (E.det * (if k = j then 1 else 0)) from
      Finset.prod_congr rfl fun k _ => by rw [hsum k]]
    rw [Finset.prod_eq_single j]
    · rw [if_pos rfl, mul_one]
      exact hf j
    · intro k _ hk
      rw [if_neg hk, mul_zero, zpow_zero]
    · intro hj
      exact absurd (Finset.mem_univ j) hj
  have hb : b = ∏ i, (fun j => c i ^ corootPair (β i) (Pi.single j 1)) := by
    funext j
    rw [Finset.prod_apply]
    exact (hc j).symm
  rw [hb]
  have hmem : ∀ s : Finset (Fin Tag.E8.rank),
      rootDiagUnit Tag.E8 (∏ i ∈ s, (fun j => c i ^ corootPair (β i) (Pi.single j 1))) ∈
        rootSpan Tag.E8 L Δ := by
    intro s
    induction s using Finset.induction with
    | empty =>
      rw [Finset.prod_empty]
      rw [show rootDiagUnit Tag.E8 (1 : Fin Tag.E8.rank → Lˣ) = 1 from
        map_one (CFSG.LieType.Chevalley.rootDiagUnitHom Tag.E8 L)]
      exact Subgroup.one_mem _
    | insert i s hi ih =>
      rw [Finset.prod_insert hi, rootDiagUnit_mul]
      refine mul_mem ?_ ih
      rw [show rootDiagUnit Tag.E8 (fun j => c i ^ corootPair (β i) (Pi.single j 1)) =
          rootSL2 Tag.E8 L (β i) (HSL (c i)) from
        (CFSG.HardMathSupport.Timmesfeld.CrossChar.rootSL2_HSL_eq (hβroot i) (c i)).symm]
      exact CFSG.RankThree.PartOne.KE.rootRankOneGroup_le_rootSpan (hβroot i) (hβmem i)
        (hneg (β i) (hβmem i)) ⟨HSL (c i), rfl⟩
  exact hmem Finset.univ

private theorem e8f5a_j2_sl5_center_card {L : Type} [Field L] [IsAlgClosed L]
    (h5 : (5 : L) ≠ 0) :
    Nat.card ↥(Subgroup.center (Matrix.SpecialLinearGroup (Fin 5) L)) = 5 := by
  haveI : NeZero ((5 : ℕ) : L) := ⟨h5⟩
  have hroot : Nat.card ↥(rootsOfUnity 5 L) = 5 :=
    HasEnoughRootsOfUnity.natCard_rootsOfUnity L 5
  calc Nat.card ↥(Subgroup.center (Matrix.SpecialLinearGroup (Fin 5) L))
      = Nat.card ↥(rootsOfUnity 5 L) :=
        Nat.card_congr (Matrix.SpecialLinearGroup.center_equiv_rootsOfUnity' (0 : Fin 5)).toEquiv
    _ = 5 := hroot

private theorem e8f5a_j2_center_map_eq
    {L : Type} [Field L] [IsAlgClosed L] {τ : Tag}
    {χ : Multiplicative (Fin τ.rank → ℤ) →* Lˣ} {i : KernelComponent χ}
    {ψ : Matrix.SpecialLinearGroup (Fin 5) L →* ModGL τ L}
    {σ : Fin 5 → Fin 5 → Fin τ.rank → ℤ} (hψ : IsSLFrame ψ σ)
    (hΨ : componentRoots χ i = frameRoots σ) :
    (Subgroup.center ↥(rootSpan τ L (componentRoots χ i))).map
        (rootSpan τ L (componentRoots χ i)).subtype =
      (Subgroup.center (Matrix.SpecialLinearGroup (Fin 5) L)).map ψ := by
  have hrange : ψ.range = rootSpan τ L (componentRoots χ i) := by rw [hψ.range, ← hΨ]
  have hψker : ψ.ker ≠ ⊤ := by
    intro htop
    have h01 : (0 : Fin 5) ≠ 1 := by decide +kernel
    obtain ⟨ε, hε⟩ := hψ.transv 0 1 h01
    have hmem : Matrix.SpecialLinearGroup.transvection h01 (1 : L) ∈ ψ.ker := by
      rw [htop]; exact Subgroup.mem_top _
    rw [MonoidHom.mem_ker, hε] at hmem
    have h0 : (ε : L) * 1 = 0 :=
      pinnedX_injective τ L (σ 0 1) (hmem.trans (pinnedX_zero τ L (σ 0 1)).symm)
    exact Units.ne_zero ε (by simpa using h0)
  apply le_antisymm
  · rintro z ⟨y, hy, rfl⟩
    have hyψ : (y : ModGL τ L) ∈ ψ.range := by rw [hrange]; exact y.2
    obtain ⟨B, hB⟩ := MonoidHom.mem_range.1 hyψ
    refine Subgroup.mem_map.2 ⟨B, ?_, hB⟩
    refine mem_center_SL_of_commute (by norm_num : 3 ≤ 5) ψ hψker ?_
    intro X
    have hX : ψ X ∈ rootSpan τ L (componentRoots χ i) := by
      rw [← hrange]; exact ⟨X, rfl⟩
    have hcz := Subgroup.mem_center_iff.1 hy (⟨ψ X, hX⟩ : ↥(rootSpan τ L (componentRoots χ i)))
    have hcz' : ψ X * (y : ModGL τ L) = (y : ModGL τ L) * ψ X :=
      congrArg Subtype.val hcz
    rw [hB]
    exact hcz'.symm
  · rintro z ⟨B, hB, rfl⟩
    refine Subgroup.mem_map.2 ⟨⟨ψ B, ?_⟩, ?_, rfl⟩
    · rw [← hrange]; exact MonoidHom.mem_range.2 ⟨B, rfl⟩
    · rw [Subgroup.mem_center_iff]
      intro w
      have hwψ : (w : ModGL τ L) ∈ ψ.range := by rw [hrange]; exact w.2
      obtain ⟨X, hX⟩ := MonoidHom.mem_range.1 hwψ
      apply Subtype.ext
      change (w : ModGL τ L) * ψ B = ψ B * (w : ModGL τ L)
      rw [← hX, ← map_mul, ← map_mul, Subgroup.mem_center_iff.1 hB X]

private theorem e8f5a_j2_component_center_dvd
    {L : Type} [Field L] [IsAlgClosed L]
    (S : LangSetup Tag.E8 L 5) {a : Fin Tag.E8.rank → Lˣ} (h : E8TwoFiveSetup S a)
    (i : KernelComponent (rootCharHom a))
    (h2 : 2 ≤ compRank (componentRoots (rootCharHom a) i))
    (hn : (componentRoots (rootCharHom a) i).ncard =
      compRank (componentRoots (rootCharHom a) i) *
        (compRank (componentRoots (rootCharHom a) i) + 1))
    (hrank : compRank (componentRoots (rootCharHom a) i) = 4) :
    Nat.card ↥(Subgroup.center ↥(rootSpan Tag.E8 L (componentRoots (rootCharHom a) i))) ∣ 5 := by
  have hd5 : rootDiagUnit Tag.E8 a ^ 5 = 1 := by
    rw [rootDiagUnit_pow, show a ^ 5 = 1 from funext fun k => h.2.2.2.1 k, rootDiagUnit_one]
  have hpL : (5 : L) ≠ 0 := by
    have h2L : (2 : L) = 0 := by
      have := S.hqpow.2
      rw [h.1] at this
      exact this
    have h5L : (5 : L) = 1 := by
      have h52 : (5 : L) = 2 * (2 : L) + (1 : L) := by ring
      rw [h52, h2L]; ring
    rw [h5L]; exact one_ne_zero
  have hn20 : (componentRoots (rootCharHom a) i).ncard = 20 := by rw [hn, hrank]
  obtain ⟨ν, ψ, σ, hν, hψ, hnorm, hΨ⟩ :=
    exists_frame_of_typeA_E8_T_of_prime S Nat.prime_five hpL hd5 i (by rw [hrank]; norm_num)
      (by rw [hn, hrank])
  have hν5 : ν = 5 := by
    have hcard := kd147c_frameRoots_ncard hψ (show (1 : ℤ) ≠ 0 by norm_num) hnorm
    rw [← hΨ, hn20] at hcard
    have hZ : (ν : ℤ) * ((ν : ℤ) - 1) = 20 := by
      have h1 : ((ν * (ν - 1) : ℕ) : ℤ) = 20 := by rw [← hcard]; norm_num
      rwa [Nat.cast_mul, Nat.cast_sub (by omega : 1 ≤ ν)] at h1
    have hνZ : (ν : ℤ) = 5 := by nlinarith
    exact_mod_cast hνZ
  subst hν5
  have hcenter_eq : (Subgroup.center ↥(rootSpan Tag.E8 L (componentRoots (rootCharHom a) i))).map
      (rootSpan Tag.E8 L (componentRoots (rootCharHom a) i)).subtype =
      (Subgroup.center (Matrix.SpecialLinearGroup (Fin 5) L)).map ψ :=
    e8f5a_j2_center_map_eq hψ hΨ
  have h1 : Nat.card ↥((Subgroup.center ↥(rootSpan Tag.E8 L
      (componentRoots (rootCharHom a) i))).map
      (rootSpan Tag.E8 L (componentRoots (rootCharHom a) i)).subtype) ∣ 5 := by
    rw [hcenter_eq]
    simpa [e8f5a_j2_sl5_center_card hpL] using
      Subgroup.card_map_dvd (Subgroup.center (Matrix.SpecialLinearGroup (Fin 5) L)) ψ
  have h2' : Nat.card ↥(Subgroup.center ↥(rootSpan Tag.E8 L (componentRoots (rootCharHom a) i))) =
      Nat.card ↥((Subgroup.center ↥(rootSpan Tag.E8 L (componentRoots (rootCharHom a) i))).map
        (rootSpan Tag.E8 L (componentRoots (rootCharHom a) i)).subtype) :=
    Nat.card_congr (Subgroup.equivMapOfInjective (Subgroup.center ↥(rootSpan Tag.E8 L
      (componentRoots (rootCharHom a) i)))
      (rootSpan Tag.E8 L (componentRoots (rootCharHom a) i)).subtype
      (rootSpan Tag.E8 L (componentRoots (rootCharHom a) i)).subtype_injective).toEquiv
  rwa [h2']

private theorem e8f5a_j2_mem_sup
    {L : Type} [Field L] [IsAlgClosed L] {τ : Tag}
    {χ : Multiplicative (Fin τ.rank → ℤ) →* Lˣ} {i₁ i₂ : KernelComponent χ}
    (hall : ∀ i, i = i₁ ∨ i = i₂) {d : ModGL τ L}
    (hd : d ∈ rootSpan τ L (kernelRoots χ)) :
    d ∈ rootSpan τ L (componentRoots χ i₁) ⊔ rootSpan τ L (componentRoots χ i₂) := by
  have hsup : rootSpan τ L (kernelRoots χ) =
      rootSpan τ L (componentRoots χ i₁) ⊔ rootSpan τ L (componentRoots χ i₂) := by
    rw [← iSup_componentRootSpan L]
    change ⨆ k, componentRootSpan L χ k =
      componentRootSpan L χ i₁ ⊔ componentRootSpan L χ i₂
    apply le_antisymm
    · refine iSup_le fun k => ?_
      rcases hall k with hk | hk <;> rw [hk]
      · exact le_sup_left
      · exact le_sup_right
    · exact sup_le (le_iSup (fun k => componentRootSpan L χ k) i₁)
        (le_iSup (fun k => componentRootSpan L χ k) i₂)
  rwa [hsup] at hd

private theorem e8f5a_j2_mem_sup'
    {L : Type} [Field L] [IsAlgClosed L] {a : Fin Tag.E8.rank → Lˣ}
    {i₁ i₂ : KernelComponent (rootCharHom a)} {S₁ S₂ : Subgroup (ModGL Tag.E8 L)}
    (hS₁ : S₁ = rootSpan Tag.E8 L (componentRoots (rootCharHom a) i₁))
    (hS₂ : S₂ = rootSpan Tag.E8 L (componentRoots (rootCharHom a) i₂))
    (hall : ∀ i, i = i₁ ∨ i = i₂)
    (hdker : rootDiagUnit Tag.E8 a ∈ rootSpan Tag.E8 L (kernelRoots (rootCharHom a))) :
    rootDiagUnit Tag.E8 a ∈ S₁ ⊔ S₂ := by
  rw [hS₁, hS₂]
  exact e8f5a_j2_mem_sup hall hdker

private theorem e8f5a_j2_mem_kernel
    {L : Type} [Field L] [IsAlgClosed L] (S : LangSetup Tag.E8 L 5)
    {a : Fin Tag.E8.rank → Lˣ} (hA : E8TwoFiveKernelA S.ρ (rootCharHom a)) :
    rootDiagUnit Tag.E8 a ∈ rootSpan Tag.E8 L (kernelRoots (rootCharHom a)) :=
  e8f5a_torus_le_rootSpan (Δ := kernelRoots (rootCharHom a)) (fun β hβ => hβ.1)
    (fun β hβ => ⟨isRoot_neg_iff.2 hβ.1, by rw [ofAdd_neg, map_inv, hβ.2, inv_one]⟩)
    (e8f5a_rank_eight S hA) a

private theorem e8f5a_j2_central
    {L : Type} [Field L] (a : Fin Tag.E8.rank → Lˣ) :
    ∀ y ∈ rootSpan Tag.E8 L (kernelRoots (rootCharHom a)),
      rootDiagUnit Tag.E8 a * y = y * rootDiagUnit Tag.E8 a := by
  intro y hy
  have hker : kernelRoots (rootCharHom a) ⊆ rootCharKernel a := by
    rw [kernelRoots_rootCharHom]; exact fun _ h => h
  exact (Subgroup.mem_centralizer_singleton_iff.1 (rootSpan_le_centralizer a hker hy)).symm

private theorem e8f5a_j2_step_fixed
    {L : Type} [Field L] [IsAlgClosed L] (S : LangSetup Tag.E8 L 5)
    {a : Fin Tag.E8.rank → Lˣ} (hΓ : rootDiagUnit Tag.E8 a ∈ S.Γ) :
    S.D.step (rootDiagUnit Tag.E8 a) = rootDiagUnit Tag.E8 a :=
  (S.D.mem_model.mp
    (CFSG.HardMathSupport.Timmesfeld.LangTorus.commutator_le_self_of_subgroup S.D.model hΓ)).2

private theorem e8f5a_j2_map_span
    {L : Type} [Field L] [IsAlgClosed L] {a : Fin Tag.E8.rank → Lˣ}
    (S : LangSetup Tag.E8 L 5) {i₁ i₂ : KernelComponent (rootCharHom a)}
    (himg : (S.ρ : (Fin Tag.E8.rank → ℤ) → _) '' componentRoots (rootCharHom a) i₁ =
      componentRoots (rootCharHom a) i₂) :
    (rootSpan Tag.E8 L (componentRoots (rootCharHom a) i₁)).map S.D.step =
      rootSpan Tag.E8 L (componentRoots (rootCharHom a) i₂) := by
  rw [map_rootSpan_step S (componentRoots (rootCharHom a) i₁)
    (fun _ hγ => isRoot_of_mem_componentRoots hγ)]
  rw [himg]

private theorem e8f5a_j2_comm
    {L : Type} [Field L] [IsAlgClosed L] {a : Fin Tag.E8.rank → Lˣ}
    {i j : KernelComponent (rootCharHom a)} (hij : i ≠ j) :
    rootSpan Tag.E8 L (componentRoots (rootCharHom a) i) ≤
      Subgroup.centralizer (rootSpan Tag.E8 L (componentRoots (rootCharHom a) j) :
        Set (ModGL Tag.E8 L)) :=
  componentRootSpan_le_centralizer L hij

private theorem e8f5a_j2_center_dvd₂
    {L : Type} [Field L] [IsAlgClosed L] {a : Fin Tag.E8.rank → Lˣ}
    (S : LangSetup Tag.E8 L 5) {i₁ i₂ : KernelComponent (rootCharHom a)}
    (hmap : (rootSpan Tag.E8 L (componentRoots (rootCharHom a) i₁)).map S.D.step =
      rootSpan Tag.E8 L (componentRoots (rootCharHom a) i₂))
    (hcard₁ : Nat.card ↥(Subgroup.center ↥(rootSpan Tag.E8 L
      (componentRoots (rootCharHom a) i₁))) ∣ 5) :
    Nat.card ↥(Subgroup.center ↥(rootSpan Tag.E8 L
      (componentRoots (rootCharHom a) i₂))) ∣ 5 := by
  have hFeq : rootSpan Tag.E8 L (componentRoots (rootCharHom a) i₁) ≃*
      rootSpan Tag.E8 L (componentRoots (rootCharHom a) i₂) :=
    (Subgroup.equivMapOfInjective _ S.D.step (splitLine_step_injective S)).trans
      (MulEquiv.subgroupCongr hmap)
  have hcard_eq : Nat.card ↥(Subgroup.center ↥(rootSpan Tag.E8 L
        (componentRoots (rootCharHom a) i₁))) =
      Nat.card ↥(Subgroup.center ↥(rootSpan Tag.E8 L
        (componentRoots (rootCharHom a) i₂))) :=
    Nat.card_congr (Subgroup.centerCongr hFeq).toEquiv
  rw [← hcard_eq]; exact hcard₁

private theorem e8f5a_j2_finalize {G : Type*} [Group G] {F : G →* G} {S₁ S₂ : Subgroup G}
    {c d u₁ u₂ : G} (hdstep : F d = d) (hd5 : d ^ 5 = 1) (hdne : d ≠ 1)
    (hcZ : c ∈ S₁ ⊓ S₂) (hcard₁ : Nat.card ↥(Subgroup.center ↥S₁) ∣ 5)
    (hcard₂ : Nat.card ↥(Subgroup.center ↥S₂) ∣ 5)
    (hZle₁ : (S₁ ⊓ S₂).subgroupOf S₁ ≤ Subgroup.center ↥S₁)
    (hZle₂ : (S₁ ⊓ S₂).subgroupOf S₂ ≤ Subgroup.center ↥S₂)
    (hu₁ : u₁ ∈ S₁) (hu₂ : u₂ ∈ S₂) (hd_eq : u₁ * u₂ = d)
    (hu₁cen : (⟨u₁, hu₁⟩ : ↥S₁) ∈ Subgroup.center ↥S₁)
    (hu₂cen : (⟨u₂, hu₂⟩ : ↥S₂) ∈ Subgroup.center ↥S₂) :
    F c = c ∧ c ^ 5 = 1 := by
  by_cases hc1 : c = 1
  · subst hc1
    exact ⟨map_one F, one_pow 5⟩
  · have hZne : S₁ ⊓ S₂ ≠ ⊥ := by
      intro hbot
      exact hc1 (Subgroup.mem_bot.1 (hbot ▸ hcZ))
    have hZ'ne : (S₁ ⊓ S₂).subgroupOf S₁ ≠ ⊥ := by
      intro hbot
      apply hZne
      refine le_antisymm ?_ bot_le
      intro z hz
      have hz' : (⟨z, hz.1⟩ : ↥S₁) ∈ (S₁ ⊓ S₂).subgroupOf S₁ := by
        rw [Subgroup.mem_subgroupOf]; exact hz
      rw [hbot] at hz'
      exact Subgroup.mem_bot.2 (congrArg Subtype.val (Subgroup.mem_bot.1 hz'))
    have hZ'card_dvd : Nat.card ↥((S₁ ⊓ S₂).subgroupOf S₁) ∣ 5 := by
      have h1 : Nat.card ↥(((S₁ ⊓ S₂).subgroupOf S₁).subgroupOf (Subgroup.center ↥S₁)) ∣
          Nat.card ↥(Subgroup.center ↥S₁) := Subgroup.card_subgroup_dvd_card _
      rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hZle₁).toEquiv] at h1
      exact h1.trans hcard₁
    have hZ'card : Nat.card ↥((S₁ ⊓ S₂).subgroupOf S₁) = 5 :=
      ((Nat.dvd_prime Nat.prime_five).1 hZ'card_dvd).resolve_left
        (fun h => hZ'ne (Subgroup.eq_bot_of_card_eq
          (H := (S₁ ⊓ S₂).subgroupOf S₁) h))
    have hZcard : Nat.card ↥(S₁ ⊓ S₂) = 5 := by
      have h := Nat.card_congr (Subgroup.subgroupOfEquivOfLe
        (inf_le_left : S₁ ⊓ S₂ ≤ S₁)).toEquiv
      rw [hZ'card] at h
      exact h.symm
    have hcard₁_eq : Nat.card ↥(Subgroup.center ↥S₁) = 5 := by
      have hdvd : 5 ∣ Nat.card ↥(Subgroup.center ↥S₁) := by
        rw [← hZ'card]
        have h1 : Nat.card ↥(((S₁ ⊓ S₂).subgroupOf S₁).subgroupOf (Subgroup.center ↥S₁)) ∣
            Nat.card ↥(Subgroup.center ↥S₁) := Subgroup.card_subgroup_dvd_card _
        rwa [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hZle₁).toEquiv] at h1
      exact (Nat.dvd_antisymm hdvd hcard₁).symm
    have hZeq₁ : (S₁ ⊓ S₂).subgroupOf S₁ = Subgroup.center ↥S₁ := by
      haveI : Finite ↥(Subgroup.center ↥S₁) :=
        Nat.finite_of_card_ne_zero (by rw [hcard₁_eq]; norm_num)
      exact Subgroup.eq_of_le_of_card_ge hZle₁ (by rw [hZ'card, hcard₁_eq])
    have hu₁Z : u₁ ∈ S₁ ⊓ S₂ := by
      have h : (⟨u₁, hu₁⟩ : ↥S₁) ∈ (S₁ ⊓ S₂).subgroupOf S₁ := by
        rw [hZeq₁]; exact hu₁cen
      exact Subgroup.mem_subgroupOf.1 h
    have hZ'card₂ : Nat.card ↥((S₁ ⊓ S₂).subgroupOf S₂) = 5 := by
      have h := Nat.card_congr (Subgroup.subgroupOfEquivOfLe
        (inf_le_right : S₁ ⊓ S₂ ≤ S₂)).toEquiv
      rw [hZcard] at h
      exact h
    have hcard₂_eq : Nat.card ↥(Subgroup.center ↥S₂) = 5 := by
      have hdvd : 5 ∣ Nat.card ↥(Subgroup.center ↥S₂) := by
        rw [← hZ'card₂]
        have h1 : Nat.card ↥(((S₁ ⊓ S₂).subgroupOf S₂).subgroupOf (Subgroup.center ↥S₂)) ∣
            Nat.card ↥(Subgroup.center ↥S₂) := Subgroup.card_subgroup_dvd_card _
        rwa [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hZle₂).toEquiv] at h1
      exact (Nat.dvd_antisymm hdvd hcard₂).symm
    have hZeq₂ : (S₁ ⊓ S₂).subgroupOf S₂ = Subgroup.center ↥S₂ := by
      haveI : Finite ↥(Subgroup.center ↥S₂) :=
        Nat.finite_of_card_ne_zero (by rw [hcard₂_eq]; norm_num)
      exact Subgroup.eq_of_le_of_card_ge hZle₂ (by rw [hZ'card₂, hcard₂_eq])
    have hu₂Z : u₂ ∈ S₁ ⊓ S₂ := by
      have h : (⟨u₂, hu₂⟩ : ↥S₂) ∈ (S₁ ⊓ S₂).subgroupOf S₂ := by
        rw [hZeq₂]; exact hu₂cen
      exact Subgroup.mem_subgroupOf.1 h
    have hdZ : d ∈ S₁ ⊓ S₂ := by
      rw [← hd_eq]; exact mul_mem hu₁Z hu₂Z
    have hc5 : c ^ 5 = 1 := by
      have h := orderOf_dvd_natCard (⟨c, hcZ⟩ : ↥(S₁ ⊓ S₂))
      rw [hZcard] at h
      have h' := orderOf_dvd_iff_pow_eq_one.1 h
      simpa using congrArg Subtype.val h'
    have hZeq_zp : S₁ ⊓ S₂ = Subgroup.zpowers d := by
      haveI : Finite ↥(S₁ ⊓ S₂) := Nat.finite_of_card_ne_zero (by rw [hZcard]; norm_num)
      symm
      apply Subgroup.eq_of_le_of_card_ge
      · rw [Subgroup.zpowers_le]; exact hdZ
      · rw [hZcard, Nat.card_zpowers, orderOf_eq_prime hd5 hdne]
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.1 (hZeq_zp ▸ hcZ)
    refine ⟨?_, hc5⟩
    rw [← hk, map_zpow, hdstep]

private theorem e8f5a_inter_fixed
    {L : Type} [Field L] [IsAlgClosed L] (S : LangSetup Tag.E8 L 5) {a : Fin Tag.E8.rank → Lˣ}
    (h : E8TwoFiveSetup S a) (hA : E8TwoFiveKernelA S.ρ (rootCharHom a))
    {i j : KernelComponent (rootCharHom a)} (hij : i ≠ j) {c : ModGL Tag.E8 L}
    (hci : c ∈ rootSpan Tag.E8 L (componentRoots (rootCharHom a) i))
    (hcj : c ∈ rootSpan Tag.E8 L (componentRoots (rootCharHom a) j)) :
    S.D.step c = c ∧ c ^ 5 = 1 := by
  classical
  have hA0 : E8TwoFiveKernelA S.ρ (rootCharHom a) := hA
  obtain ⟨_hkn, i₁, i₂, hi12, hall, hrk₁, hcard₁, himg, _hkind⟩ := hA
  set S₁ : Subgroup (ModGL Tag.E8 L) := rootSpan Tag.E8 L (componentRoots (rootCharHom a) i₁)
    with hS₁
  set S₂ : Subgroup (ModGL Tag.E8 L) := rootSpan Tag.E8 L (componentRoots (rootCharHom a) i₂)
    with hS₂
  have hd5 : rootDiagUnit Tag.E8 a ^ 5 = 1 := by
    rw [rootDiagUnit_pow, show a ^ 5 = 1 from funext fun k => h.2.2.2.1 k, rootDiagUnit_one]
  have hS₁le : S₁ ≤ rootSpan Tag.E8 L (kernelRoots (rootCharHom a)) := by
    rw [hS₁]; exact rootSpan_mono (fun _ hγ => hγ.1)
  have hS₂le : S₂ ≤ rootSpan Tag.E8 L (kernelRoots (rootCharHom a)) := by
    rw [hS₂]; exact rootSpan_mono (fun _ hγ => hγ.1)
  have hdker : rootDiagUnit Tag.E8 a ∈ rootSpan Tag.E8 L (kernelRoots (rootCharHom a)) :=
    e8f5a_j2_mem_kernel S hA0
  have hdcent := e8f5a_j2_central a
  have hdstep : S.D.step (rootDiagUnit Tag.E8 a) = rootDiagUnit Tag.E8 a :=
    e8f5a_j2_step_fixed S h.2.2.1
  have hFmap : S₁.map S.D.step = S₂ := by
    rw [hS₁, hS₂]; exact e8f5a_j2_map_span S himg
  have hcomm12 : S₂ ≤ Subgroup.centralizer (S₁ : Set (ModGL Tag.E8 L)) := by
    rw [hS₁, hS₂]; exact e8f5a_j2_comm (Ne.symm hi12)
  have hcomm21 : S₁ ≤ Subgroup.centralizer (S₂ : Set (ModGL Tag.E8 L)) := by
    rw [hS₁, hS₂]; exact e8f5a_j2_comm hi12
  have hcases : (i = i₁ ∧ j = i₂) ∨ (i = i₂ ∧ j = i₁) := by
    rcases hall i with hi | hi
    · rcases hall j with hj | hj
      · exact absurd (hi.trans hj.symm) hij
      · exact Or.inl ⟨hi, hj⟩
    · rcases hall j with hj | hj
      · exact Or.inr ⟨hi, hj⟩
      · exact absurd (hi.trans hj.symm) hij
  have hcS₁ : c ∈ S₁ := by
    rcases hcases with ⟨hi, _⟩ | ⟨_, hj⟩
    · rw [hS₁, ← hi]; exact hci
    · rw [hS₁, ← hj]; exact hcj
  have hcS₂ : c ∈ S₂ := by
    rcases hcases with ⟨_, hj⟩ | ⟨hi, _⟩
    · rw [hS₂, ← hj]; exact hcj
    · rw [hS₂, ← hi]; exact hci
  have hcZ : c ∈ S₁ ⊓ S₂ := ⟨hcS₁, hcS₂⟩
  have h2 : 2 ≤ compRank (componentRoots (rootCharHom a) i₁) := by rw [hrk₁]; norm_num
  have hn : (componentRoots (rootCharHom a) i₁).ncard =
      compRank (componentRoots (rootCharHom a) i₁) *
        (compRank (componentRoots (rootCharHom a) i₁) + 1) := by
    rw [hrk₁, hcard₁]
  have hcard_center₁ : Nat.card ↥(Subgroup.center ↥S₁) ∣ 5 := by
    rw [hS₁]
    exact e8f5a_j2_component_center_dvd S h i₁ h2 hn hrk₁
  have hcard_center₂ : Nat.card ↥(Subgroup.center ↥S₂) ∣ 5 := by
    rw [hS₂]
    exact e8f5a_j2_center_dvd₂ S (by rw [← hS₁, ← hS₂]; exact hFmap)
      (by rw [← hS₁]; exact hcard_center₁)
  have hZle₁ : (S₁ ⊓ S₂).subgroupOf S₁ ≤ Subgroup.center ↥S₁ := by
    intro z hz
    rw [Subgroup.mem_center_iff]
    intro w
    have hz₂ : (z : ModGL Tag.E8 L) ∈ S₂ :=
      (Subgroup.mem_inf.1 (Subgroup.mem_subgroupOf.1 hz)).2
    exact Subtype.ext ((Subgroup.mem_centralizer_iff.1 (hcomm12 hz₂) (w : ModGL Tag.E8 L) w.2))
  have hZle₂ : (S₁ ⊓ S₂).subgroupOf S₂ ≤ Subgroup.center ↥S₂ := by
    intro z hz
    rw [Subgroup.mem_center_iff]
    intro w
    have hz₁ : (z : ModGL Tag.E8 L) ∈ S₁ :=
      (Subgroup.mem_inf.1 (Subgroup.mem_subgroupOf.1 hz)).1
    exact Subtype.ext ((Subgroup.mem_centralizer_iff.1 (hcomm21 hz₁) (w : ModGL Tag.E8 L) w.2))
  have hdA : rootDiagUnit Tag.E8 a ∈ S₁ ⊔ S₂ :=
    e8f5a_j2_mem_sup' hS₁ hS₂ hall hdker
  have hS₂norm : S₂ ≤ Subgroup.normalizer (S₁ : Set (ModGL Tag.E8 L)) :=
    hcomm12.trans (Subgroup.centralizer_le_normalizer _)
  obtain ⟨u₁, hu₁, u₂, hu₂, hd_eq⟩ :=
    (TauCeti.Subgroup.mem_sup_of_right_le_normalizer_left hS₂norm).mp hdA
  have hu₁cen : (⟨u₁, hu₁⟩ : ↥S₁) ∈ Subgroup.center ↥S₁ := by
    rw [Subgroup.mem_center_iff]
    intro w
    apply Subtype.ext
    have hdw := hdcent (w : ModGL Tag.E8 L) (hS₁le w.2)
    have hu₂w : u₂ * (w : ModGL Tag.E8 L) = (w : ModGL Tag.E8 L) * u₂ :=
      (Subgroup.mem_centralizer_iff.1 (hcomm12 hu₂) (w : ModGL Tag.E8 L) w.2).symm
    have hcalc : rootDiagUnit Tag.E8 a * (w : ModGL Tag.E8 L) =
        (u₁ * (w : ModGL Tag.E8 L)) * u₂ := by
      rw [hd_eq, mul_assoc, hu₂w, ← mul_assoc]
    have hcalc2 : (w : ModGL Tag.E8 L) * rootDiagUnit Tag.E8 a =
        ((w : ModGL Tag.E8 L) * u₁) * u₂ := by
      rw [hd_eq, mul_assoc]
    rw [hcalc, hcalc2] at hdw
    exact (mul_right_cancel hdw).symm
  have hu₂cen : (⟨u₂, hu₂⟩ : ↥S₂) ∈ Subgroup.center ↥S₂ := by
    rw [Subgroup.mem_center_iff]
    intro w
    apply Subtype.ext
    have hdw := hdcent (w : ModGL Tag.E8 L) (hS₂le w.2)
    have hu₁w : (w : ModGL Tag.E8 L) * u₁ = u₁ * (w : ModGL Tag.E8 L) :=
      Subgroup.mem_centralizer_iff.1 (hcomm21 hu₁) (w : ModGL Tag.E8 L) w.2
    have hcalc : rootDiagUnit Tag.E8 a * (w : ModGL Tag.E8 L) =
        u₁ * (u₂ * (w : ModGL Tag.E8 L)) := by
      rw [hd_eq, mul_assoc]
    have hcalc2 : (w : ModGL Tag.E8 L) * rootDiagUnit Tag.E8 a =
        u₁ * ((w : ModGL Tag.E8 L) * u₂) := by
      rw [hd_eq, ← mul_assoc, hu₁w, mul_assoc]
    rw [hcalc, hcalc2] at hdw
    exact (mul_left_cancel hdw).symm
  exact e8f5a_j2_finalize hdstep hd5 h.2.2.2.2 hcZ hcard_center₁ hcard_center₂ hZle₁ hZle₂
    hu₁ hu₂ hd_eq.symm hu₁cen hu₂cen

private theorem e8f5a_exists_frame
    {L : Type} [Field L] [IsAlgClosed L] (S : LangSetup Tag.E8 L 5) {a : Fin Tag.E8.rank → Lˣ}
    (h : E8TwoFiveSetup S a) {i : KernelComponent (rootCharHom a)}
    (hrk : compRank (componentRoots (rootCharHom a) i) = 4)
    (hcard : (componentRoots (rootCharHom a) i).ncard = 20)
    (hkind : twistKind S.ρ (rootCharHom a) i = .suN) :
    ∃ (ψ : SL(5, L) →* ModGL Tag.E8 L) (σ : Fin 5 → Fin 5 → Fin Tag.E8.rank → ℤ),
      IsSLFrame ψ σ ∧ componentRoots (rootCharHom a) i = frameRoots σ ∧
        (∀ x y, x ≠ y → iform (σ x y) (σ x y) = 2 * 1) ∧
        ∃ π : Equiv.Perm (Fin 5), ∀ x y, x ≠ y →
          (S.ρ : (Fin Tag.E8.rank → ℤ) → _)^[componentOrbitLength S.ρ
            (componentRoots (rootCharHom a) i)] (σ x y) = σ (π y) (π x) := by
  have h2L : ((2 : ℕ) : L) = 0 := by simpa [h.1] using S.hqpow.2
  haveI : CharP L 2 := (CharP.charP_iff_prime_eq_zero Nat.prime_two).2 h2L
  have hpL : ((5 : ℕ) : L) ≠ 0 := by
    intro h5
    have hdvd := (CharP.cast_eq_zero_iff L 2 5).1 h5
    norm_num at hdvd
  have hTp : rootDiagUnit Tag.E8 a ^ 5 = 1 :=
    CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple.rootDiagUnit_pow_eq_one_of_forall
      h.2.2.2.1
  have hn : (componentRoots (rootCharHom a) i).ncard =
      compRank (componentRoots (rootCharHom a) i) *
        (compRank (componentRoots (rootCharHom a) i) + 1) := by
    rw [hrk, hcard]
  obtain ⟨ν, ψ, σ, hν3, hψ, hnorm, hΨ⟩ :=
    exists_frame_of_typeA_E8_T_of_prime S Nat.prime_five hpL hTp i (by omega) hn
  have hncard : (frameRoots σ).ncard = ν * (ν - 1) :=
    kd147c_frameRoots_ncard hψ one_ne_zero hnorm
  have h20 : ν * (ν - 1) = 20 := by rw [← hncard, ← hΨ, hcard]
  have hν5 : ν = 5 := by
    have hle : ν ≤ 5 := by
      by_contra hgt
      have h6 : 6 ≤ ν := by omega
      have hmul : 6 * 5 ≤ ν * (ν - 1) := Nat.mul_le_mul h6 (by omega)
      omega
    interval_cases ν <;> norm_num at h20
    rfl
  subst ν
  obtain ⟨π, hπ⟩ :=
    CFSG.HardMathSupport.Dickson.Sec6.Up34Exc.two_suN_perm S h.2.1 i hkind hν3 hψ
      (κ := 1) one_ne_zero hnorm hΨ
  exact ⟨ψ, σ, hψ, hΨ, hnorm, π, hπ⟩

private theorem e8f5a_i_frame_injective_aux
    {L : Type} [Field L] [IsAlgClosed L] (S : LangSetup Tag.E8 L 5)
    {a : Fin Tag.E8.rank → Lˣ} (h : E8TwoFiveSetup S a)
    (hA : E8TwoFiveKernelA S.ρ (rootCharHom a))
    {i j : KernelComponent (rootCharHom a)} (hij : i ≠ j)
    (hall : ∀ k, k = i ∨ k = j)
    (himg : (S.ρ : (Fin Tag.E8.rank → ℤ) → _) '' componentRoots (rootCharHom a) i =
      componentRoots (rootCharHom a) j)
    {ψ : SL(5, L) →* ModGL Tag.E8 L} {σ : Fin 5 → Fin 5 → Fin Tag.E8.rank → ℤ}
    (hψ : IsSLFrame ψ σ) (hΨ : componentRoots (rootCharHom a) i = frameRoots σ) :
    Function.Injective ψ := by
  classical
  rw [injective_iff_map_eq_one]
  intro X hXmem
  by_contra hXne
  have hXker : X ∈ ψ.ker := MonoidHom.mem_ker.2 hXmem
  have hker : ψ.ker ≠ ⊤ := by
    intro htop
    have h01 : (0 : Fin 5) ≠ 1 := by decide +kernel
    obtain ⟨ε, hε⟩ := hψ.transv 0 1 h01
    have hmem : Matrix.SpecialLinearGroup.transvection h01 (1 : L) ∈ ψ.ker := by
      rw [htop]; exact Subgroup.mem_top _
    rw [MonoidHom.mem_ker, hε] at hmem
    have h0 : (ε : L) * 1 = 0 :=
      pinnedX_injective Tag.E8 L (σ 0 1) (hmem.trans (pinnedX_zero Tag.E8 L (σ 0 1)).symm)
    exact Units.ne_zero ε (by simpa using h0)
  have hker_le_center : ψ.ker ≤
      Subgroup.center (Matrix.SpecialLinearGroup (Fin 5) L) := by
    intro Y hY
    refine mem_center_SL_of_commute (by norm_num : 3 ≤ 5) ψ hker ?_
    intro Z
    rw [MonoidHom.mem_ker.1 hY, one_mul, mul_one]
  have hpL : (5 : L) ≠ 0 := by
    have h2L : (2 : L) = 0 := by
      have := S.hqpow.2
      rw [h.1] at this
      exact this
    have h5L : (5 : L) = 1 := by
      have h52 : (5 : L) = 2 * (2 : L) + (1 : L) := by ring
      rw [h52, h2L]; ring
    rw [h5L]; exact one_ne_zero
  have hcard_center : Nat.card ↥(Subgroup.center (Matrix.SpecialLinearGroup (Fin 5) L)) = 5 :=
    e8f5a_j2_sl5_center_card hpL
  have hcard_dvd : Nat.card ↥ψ.ker ∣ 5 := by
    have h1 := Subgroup.card_dvd_of_le hker_le_center
    rwa [hcard_center] at h1
  have hcard_ne1 : Nat.card ↥ψ.ker ≠ 1 := by
    intro hcard1
    have hbot := Subgroup.eq_bot_of_card_eq (H := ψ.ker) hcard1
    rw [hbot] at hXker
    exact hXne (Subgroup.mem_bot.1 hXker)
  have hcard_ker : Nat.card ↥ψ.ker = 5 := by
    rcases (Nat.dvd_prime Nat.prime_five).1 hcard_dvd with h1 | h5
    · exact absurd h1 hcard_ne1
    · exact h5
  haveI : Finite ↥(Subgroup.center (Matrix.SpecialLinearGroup (Fin 5) L)) :=
    Nat.finite_of_card_ne_zero (by rw [hcard_center]; norm_num)
  have hker_eq_center : ψ.ker = Subgroup.center (Matrix.SpecialLinearGroup (Fin 5) L) :=
    Subgroup.eq_of_le_of_card_ge hker_le_center (by rw [hcard_center, hcard_ker])
  have hZmap : (Subgroup.center (Matrix.SpecialLinearGroup (Fin 5) L)).map ψ = ⊥ := by
    rw [Subgroup.map_eq_bot_iff]
    rw [hker_eq_center]
  set S_i : Subgroup (ModGL Tag.E8 L) :=
    rootSpan Tag.E8 L (componentRoots (rootCharHom a) i) with hS_i
  set S_j : Subgroup (ModGL Tag.E8 L) :=
    rootSpan Tag.E8 L (componentRoots (rootCharHom a) j) with hS_j
  have hZi : Subgroup.center ↥S_i = ⊥ := by
    have hcenter := e8f5a_j2_center_map_eq hψ hΨ
    rw [← hS_i] at hcenter
    rw [hZmap] at hcenter
    have hle := (Subgroup.map_eq_bot_iff _).1 hcenter
    rw [Subgroup.ker_subtype] at hle
    exact le_bot_iff.1 hle
  have hmap_i : S_i.map S.D.step = S_j := by
    rw [hS_i, hS_j]
    exact e8f5a_j2_map_span S himg
  have hFeq : S_i ≃* S_j :=
    (Subgroup.equivMapOfInjective S_i S.D.step (splitLine_step_injective S)).trans
      (MulEquiv.subgroupCongr hmap_i)
  have hcardZeq : Nat.card ↥(Subgroup.center ↥S_i) =
      Nat.card ↥(Subgroup.center ↥S_j) :=
    Nat.card_congr (Subgroup.centerCongr hFeq).toEquiv
  have hZj : Subgroup.center ↥S_j = ⊥ := by
    apply Subgroup.eq_bot_of_card_eq
    rw [← hcardZeq, hZi]
    exact Subgroup.card_bot
  have hdker : rootDiagUnit Tag.E8 a ∈
      rootSpan Tag.E8 L (kernelRoots (rootCharHom a)) :=
    e8f5a_j2_mem_kernel S hA
  have hSi_le : S_i ≤ rootSpan Tag.E8 L (kernelRoots (rootCharHom a)) := by
    rw [hS_i]; exact rootSpan_mono (fun _ hγ => hγ.1)
  have hSj_le : S_j ≤ rootSpan Tag.E8 L (kernelRoots (rootCharHom a)) := by
    rw [hS_j]; exact rootSpan_mono (fun _ hγ => hγ.1)
  have hdcent := e8f5a_j2_central a
  have hcomm_ij : S_i ≤ Subgroup.centralizer (S_j : Set (ModGL Tag.E8 L)) :=
    e8f5a_j2_comm (i := i) (j := j) hij
  have hcomm_ji : S_j ≤ Subgroup.centralizer (S_i : Set (ModGL Tag.E8 L)) :=
    e8f5a_j2_comm (i := j) (j := i) hij.symm
  have hS_j_norm : S_j ≤ Subgroup.normalizer (S_i : Set (ModGL Tag.E8 L)) :=
    hcomm_ji.trans (Subgroup.centralizer_le_normalizer _)
  have hdA : rootDiagUnit Tag.E8 a ∈ S_i ⊔ S_j :=
    e8f5a_j2_mem_sup' hS_i hS_j hall hdker
  obtain ⟨u_i, hu_i, u_j, hu_j, hd_eq⟩ :=
    (TauCeti.Subgroup.mem_sup_of_right_le_normalizer_left hS_j_norm).mp hdA
  have hu_i_cen : (⟨u_i, hu_i⟩ : ↥S_i) ∈ Subgroup.center ↥S_i := by
    rw [Subgroup.mem_center_iff]
    intro w
    apply Subtype.ext
    have hdw := hdcent (w : ModGL Tag.E8 L) (hSi_le w.2)
    have hu_jw : u_j * (w : ModGL Tag.E8 L) = (w : ModGL Tag.E8 L) * u_j :=
      (Subgroup.mem_centralizer_iff.1 (hcomm_ji hu_j) (w : ModGL Tag.E8 L) w.2).symm
    have hcalc : rootDiagUnit Tag.E8 a * (w : ModGL Tag.E8 L) =
        (u_i * (w : ModGL Tag.E8 L)) * u_j := by
      rw [hd_eq, mul_assoc, hu_jw, ← mul_assoc]
    have hcalc2 : (w : ModGL Tag.E8 L) * rootDiagUnit Tag.E8 a =
        ((w : ModGL Tag.E8 L) * u_i) * u_j := by
      rw [hd_eq, mul_assoc]
    rw [hcalc, hcalc2] at hdw
    exact (mul_right_cancel hdw).symm
  have hu_j_cen : (⟨u_j, hu_j⟩ : ↥S_j) ∈ Subgroup.center ↥S_j := by
    rw [Subgroup.mem_center_iff]
    intro w
    apply Subtype.ext
    have hdw := hdcent (w : ModGL Tag.E8 L) (hSj_le w.2)
    have hu_iw : (w : ModGL Tag.E8 L) * u_i = u_i * (w : ModGL Tag.E8 L) :=
      Subgroup.mem_centralizer_iff.1 (hcomm_ij hu_i) (w : ModGL Tag.E8 L) w.2
    have hcalc : rootDiagUnit Tag.E8 a * (w : ModGL Tag.E8 L) =
        u_i * (u_j * (w : ModGL Tag.E8 L)) := by
      rw [hd_eq, mul_assoc]
    have hcalc2 : (w : ModGL Tag.E8 L) * rootDiagUnit Tag.E8 a =
        u_i * ((w : ModGL Tag.E8 L) * u_j) := by
      rw [hd_eq, ← mul_assoc, hu_iw, mul_assoc]
    rw [hcalc, hcalc2] at hdw
    exact (mul_left_cancel hdw).symm
  have hu_i_one : u_i = 1 := by
    have hmem : (⟨u_i, hu_i⟩ : ↥S_i) ∈ (⊥ : Subgroup ↥S_i) := by
      rw [← hZi]; exact hu_i_cen
    exact congrArg Subtype.val (Subgroup.mem_bot.1 hmem)
  have hu_j_one : u_j = 1 := by
    have hmem : (⟨u_j, hu_j⟩ : ↥S_j) ∈ (⊥ : Subgroup ↥S_j) := by
      rw [← hZj]; exact hu_j_cen
    exact congrArg Subtype.val (Subgroup.mem_bot.1 hmem)
  exact h.2.2.2.2 (by rw [hd_eq, hu_i_one, hu_j_one, one_mul])

private theorem e8f5a_frame_injective
    {L : Type} [Field L] [IsAlgClosed L] (S : LangSetup Tag.E8 L 5) {a : Fin Tag.E8.rank → Lˣ}
    (h : E8TwoFiveSetup S a) (hA : E8TwoFiveKernelA S.ρ (rootCharHom a))
    {i : KernelComponent (rootCharHom a)} {ψ : SL(5, L) →* ModGL Tag.E8 L}
    {σ : Fin 5 → Fin 5 → Fin Tag.E8.rank → ℤ} (hψ : IsSLFrame ψ σ)
    (hΨ : componentRoots (rootCharHom a) i = frameRoots σ) : Function.Injective ψ := by
  obtain ⟨i₁, i₂, hi12, hall, -, -, -, h12, h21⟩ := e8f5a_swap S h hA
  rcases hall i with hi | hi
  · subst hi
    exact e8f5a_i_frame_injective_aux S h hA hi12 hall h12 hψ hΨ
  · subst hi
    refine e8f5a_i_frame_injective_aux S h hA (Ne.symm hi12) ?_ h21 hψ hΨ
    intro k
    rcases hall k with hk | hk
    · exact Or.inr hk
    · exact Or.inl hk

private theorem e8f5a_unitary_fixed
    {L : Type} [Field L] [IsAlgClosed L] (S : LangSetup Tag.E8 L 5) {a : Fin Tag.E8.rank → Lˣ}
    (h : E8TwoFiveSetup S a) (hA : E8TwoFiveKernelA S.ρ (rootCharHom a))
    {i : KernelComponent (rootCharHom a)}
    (hrk : compRank (componentRoots (rootCharHom a) i) = 4)
    (hcard : (componentRoots (rootCharHom a) i).ncard = 20)
    (hkind : twistKind S.ρ (rootCharHom a) i = .suN) :
    ∃ (H : Subgroup SL(5, L)) (θ : H →* ModGL Tag.E8 L), Group.IsPerfect H ∧
      (∀ c, θ c ∈ rootSpan Tag.E8 L (componentRoots (rootCharHom a) i)) ∧
      (∀ c, iterHom S.D.step (componentOrbitLength S.ρ (componentRoots (rootCharHom a) i))
        (θ c) = θ c) ∧
      ∀ g ∈ rootSpan Tag.E8 L (componentRoots (rootCharHom a) i),
        iterHom S.D.step (componentOrbitLength S.ρ (componentRoots (rootCharHom a) i)) g = g →
          ∃ c, θ c = g := by
  obtain ⟨ψ, σ, hψ, hΨ, -, π, hπ⟩ := e8f5a_exists_frame S h hrk hcard hkind
  exact CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6Three.KSNotAll24.a2ci_exists_unitary_fixed
    S h.2.1 i (by norm_num) hψ (e8f5a_frame_injective S h hA hψ hΨ) hΨ π hπ
    (by simp)

private theorem e8f5a_n_zmod2_cases (k : ZMod 2) : k = 0 ∨ k = 1 := by
  have hlt : k.val < 2 := ZMod.val_lt k
  have h01 : k.val = 0 ∨ k.val = 1 := by omega
  rcases h01 with h | h
  · left; exact (ZMod.val_eq_zero k).1 h
  · right; exact (ZMod.val_eq_one (by norm_num) k).1 h

private theorem e8f5a_n_cyc2_mu_eq {G : Type*} [Group G] {F : G →* G}
    (P : CycFamily F 2) (f : ∀ k, P.S k) : P.mu f = (f 0 : G) * (f 1 : G) := by
  have hf : f = Pi.mulSingle 0 (f 0) * Pi.mulSingle 1 (f 1) := by
    funext k
    rcases e8f5a_n_zmod2_cases k with hk | hk <;> subst hk <;> simp [Pi.mul_apply]
  have := congrArg P.mu hf
  rwa [map_mul, P.mu_mulSingle, P.mu_mulSingle] at this

private theorem e8f5a_n_cyc2_norm_decomp {G : Type*} [Group G] {F : G →* G}
    (P : CycFamily F 2)
    (hinter : ∀ c ∈ P.S 0 ⊓ P.S 1, F c = c ∧ c ^ 5 = 1)
    (f : ∀ k, P.S k) (hF : F (P.mu f) = P.mu f) :
    ∃ y : P.S 0, iterHom F 2 (y : G) = y ∧ P.mu f = P.norm y := by
  classical
  have hmu : P.mu f = (f 0 : G) * (f 1 : G) := e8f5a_n_cyc2_mu_eq P f
  have hF0 : F (f 0 : G) ∈ P.S 1 := by
    have h : F (f 0 : G) ∈ (P.S 0).map F := Subgroup.mem_map_of_mem F (f 0).2
    rwa [P.map_eq 0, zero_add] at h
  have hF1 : F (f 1 : G) ∈ P.S 0 := by
    have h : F (f 1 : G) ∈ (P.S 1).map F := Subgroup.mem_map_of_mem F (f 1).2
    rwa [P.map_eq 1, show (1 : ZMod 2) + 1 = 0 from ZMod.natCast_self 2] at h
  have hFba : F (f 0 : G) * F (f 1 : G) = (f 0 : G) * (f 1 : G) := by
    have h := hF
    rw [hmu, map_mul] at h
    exact h
  have hcomm : Commute (F (f 1 : G)) (F (f 0 : G)) :=
    P.comm 0 1 zero_ne_one _ hF1 _ hF0
  have hc_eq : (F (f 1 : G))⁻¹ * (f 0 : G) = F (f 0 : G) * (f 1 : G)⁻¹ := by
    have hkey : (f 0 : G) * (f 1 : G) = F (f 1 : G) * F (f 0 : G) :=
      hFba.symm.trans hcomm.eq.symm
    rw [inv_mul_eq_iff_eq_mul, ← mul_assoc, ← hkey, mul_inv_cancel_right]
  set c : G := (F (f 1 : G))⁻¹ * (f 0 : G) with hcdef
  have hc1 : c = F (f 0 : G) * (f 1 : G)⁻¹ := hcdef.trans hc_eq
  have hc_mem0 : c ∈ P.S 0 := by
    rw [hcdef]; exact mul_mem (inv_mem hF1) (f 0).2
  have hc_mem1 : c ∈ P.S 1 := by
    rw [hc1]; exact mul_mem hF0 (inv_mem (f 1).2)
  have hc_mem : c ∈ P.S 0 ⊓ P.S 1 := ⟨hc_mem0, hc_mem1⟩
  have hcfix : F c = c := (hinter c hc_mem).1
  have hc5 : c ^ 5 = 1 := (hinter c hc_mem).2
  have hg0 : (f 0 : G) = F (f 1 : G) * c := by rw [hcdef]; group
  have hb : F (f 0 : G) = c * (f 1 : G) := by rw [hc1]; group
  have hg1 : (f 1 : G) = c⁻¹ * F (f 0 : G) := by rw [hb]; group
  have hF2g1 : F (F (f 1 : G)) = (f 1 : G) := by
    have h1 : F (f 0 : G) = F (F (f 1 : G)) * c := by rw [hg0, map_mul, hcfix]
    have h2 : F (F (f 1 : G)) * c = c * (f 1 : G) := by rw [← h1, hb]
    have h3 : c * (f 1 : G) = (f 1 : G) * c :=
      (P.comm 0 1 zero_ne_one _ hc_mem0 _ (f 1).2).eq
    rw [h3] at h2
    exact mul_right_cancel h2
  have hF2g0 : F (F (f 0 : G)) = (f 0 : G) := by
    have ha : F (F (F (f 1 : G))) = F (f 1 : G) := by rw [hF2g1]
    have hF2c : F (F c) = c := by simp only [hcfix]
    rw [hg0, map_mul, map_mul, ha, hF2c]
  have hFt : F (c ^ 2 * (f 0 : G)) = c ^ 2 * F (f 0 : G) := by
    rw [map_mul, map_pow, hcfix]
  have hF2t : F (F (c ^ 2 * (f 0 : G))) = c ^ 2 * (f 0 : G) := by
    rw [hFt, map_mul, map_pow, hcfix, hF2g0]
  have hcg0 : Commute c (f 0 : G) := P.comm 1 0 one_ne_zero _ hc_mem1 _ (f 0).2
  have hc4 : c ^ 4 = c⁻¹ := by
    exact eq_inv_of_mul_eq_one_left (by rw [← pow_succ, show 4 + 1 = 5 by norm_num, hc5])
  have hmain : (f 0 : G) * (f 1 : G) =
      (c ^ 2 * (f 0 : G)) * F (c ^ 2 * (f 0 : G)) := by
    have hc2g0 : c ^ 2 * (f 0 : G) = (f 0 : G) * c ^ 2 := (hcg0.pow_left 2).eq
    calc (f 0 : G) * (f 1 : G)
        = (f 0 : G) * c ^ 4 * F (f 0 : G) := by rw [hg1, hc4]; group
      _ = (c ^ 2 * (f 0 : G)) * F (c ^ 2 * (f 0 : G)) := by rw [hFt, hc2g0]; group
  have ht_mem : c ^ 2 * (f 0 : G) ∈ P.S 0 := mul_mem (pow_mem hc_mem0 2) (f 0).2
  refine ⟨⟨c ^ 2 * (f 0 : G), ht_mem⟩, ?_, ?_⟩
  · show iterHom F 2 (c ^ 2 * (f 0 : G)) = c ^ 2 * (f 0 : G)
    rw [iterHom_succ, iterHom_succ, iterHom_zero, hF2t]
  · show P.mu f = P.norm ⟨c ^ 2 * (f 0 : G), ht_mem⟩
    have hdiag0 : ((P.diag ⟨c ^ 2 * (f 0 : G), ht_mem⟩) 0 : G) = c ^ 2 * (f 0 : G) := by
      rw [P.coe_diag_apply, ZMod.val_zero, iterHom_zero]
    have hdiag1 : ((P.diag ⟨c ^ 2 * (f 0 : G), ht_mem⟩) 1 : G) =
        F (c ^ 2 * (f 0 : G)) := by
      rw [P.coe_diag_apply, ZMod.val_one'' (show (2 : ℕ) ≠ 1 by norm_num),
        iterHom_succ, iterHom_zero]
    have hnorm : P.norm ⟨c ^ 2 * (f 0 : G), ht_mem⟩ =
        (c ^ 2 * (f 0 : G)) * F (c ^ 2 * (f 0 : G)) := by
      change P.mu (P.diag ⟨c ^ 2 * (f 0 : G), ht_mem⟩) = _
      rw [e8f5a_n_cyc2_mu_eq P (P.diag ⟨c ^ 2 * (f 0 : G), ht_mem⟩), hdiag0, hdiag1]
    rw [hmu, hnorm]
    exact hmain

private theorem e8f5a_norm_decomp
    {L : Type} [Field L] [IsAlgClosed L] (S : LangSetup Tag.E8 L 5) {a : Fin Tag.E8.rank → Lˣ}
    (h : E8TwoFiveSetup S a) (hA : E8TwoFiveKernelA S.ρ (rootCharHom a))
    (i : KernelComponent (rootCharHom a)) {s : ℕ} [NeZero s]
    (hs : (S.ρ : (Fin Tag.E8.rank → ℤ) → _)^[s] '' componentRoots (rootCharHom a) i =
      componentRoots (rootCharHom a) i)
    (hmin : ∀ k, 0 < k → k < s →
      (S.ρ : (Fin Tag.E8.rank → ℤ) → _)^[k] '' componentRoots (rootCharHom a) i ≠
        componentRoots (rootCharHom a) i)
    (hs2 : s = 2) {x : ModGL Tag.E8 L}
    (hxA : x ∈ rootSpan Tag.E8 L (kernelRoots (rootCharHom a))) (hxF : S.D.step x = x) :
    ∃ y : (outerOrbitFamily S h.2.1 i hs hmin).S 0,
      iterHom S.D.step s (y : ModGL Tag.E8 L) = y ∧
        x = (outerOrbitFamily S h.2.1 i hs hmin).norm y := by
  classical
  subst hs2
  set P := outerOrbitFamily S h.2.1 i hs hmin with hP
  have hPA : P.A = rootSpan Tag.E8 L (kernelRoots (rootCharHom a)) := by
    rw [hP, outerOrbitFamily_A, e8f5a_rationalRoots_eq S h hA i]
  have hxA' : x ∈ P.A := by rw [hPA]; exact hxA
  obtain ⟨f, hf⟩ := P.mem_A_iff.1 hxA'
  have hF : S.D.step (P.mu f) = P.mu f := by rw [hf]; exact hxF
  obtain ⟨j, hj⟩ := outer_iterate_image_component S h.2.1 i 1
  have hS0 : P.S 0 = rootSpan Tag.E8 L (componentRoots (rootCharHom a) i) := by
    rw [hP, outerOrbitFamily_S, ZMod.val_zero]
    simp only [Function.iterate_zero, id_eq, Set.image_id']
  have hS1 : P.S 1 = rootSpan Tag.E8 L (componentRoots (rootCharHom a) j) := by
    rw [hP, outerOrbitFamily_S, ZMod.val_one'' (show (2 : ℕ) ≠ 1 by norm_num), ← hj]
  have hne : componentRoots (rootCharHom a) j ≠ componentRoots (rootCharHom a) i := by
    rw [hj]
    exact hmin 1 (by norm_num) (by norm_num)
  have hij : i ≠ j := by
    intro h'
    exact hne (by rw [h'])
  have hinter : ∀ c ∈ P.S 0 ⊓ P.S 1, S.D.step c = c ∧ c ^ 5 = 1 := by
    intro c hc
    refine e8f5a_inter_fixed S h hA hij ?_ ?_
    · rw [← hS0]; exact hc.1
    · rw [← hS1]; exact hc.2
  obtain ⟨y, hyfix, hynorm⟩ := e8f5a_n_cyc2_norm_decomp P hinter f hF
  exact ⟨y, hyfix, hf.symm.trans hynorm⟩

private theorem e8f5a_decomp
    {L : Type} [Field L] [IsAlgClosed L] {a : Fin Tag.E8.rank → Lˣ} (h5 : ∀ i, a i ^ 5 = 1)
    {c : ModGL Tag.E8 L} (hc : c ∈ toralCentralizer Tag.E8 L a) :
    ∃ (b : Fin Tag.E8.rank → Lˣ) (s : ModGL Tag.E8 L),
      s ∈ rootSpan Tag.E8 L (kernelRoots (rootCharHom a)) ∧
        c = rootDiagUnit Tag.E8 b * s := by
  rw [CFSG.HardMathSupport.Timmesfeld.Steinberg.toralCentralizer_eq_toralRootGroup_E8_five
    L a h5, toralRootGroup] at hc
  rw [← SetLike.mem_coe, Subgroup.coe_mul_of_left_le_normalizer_right _ _
    (CFSG.RankThree.PartOne.KE.torusGroup_le_normalizer_rootSpan (S := rootCharKernel a)
      fun α hα => hα.1)] at hc
  obtain ⟨t, ht, s, hs, rfl⟩ := hc
  obtain ⟨b, rfl⟩ := exists_rootDiagUnit_eq_of_mem_torusGroup ht
  exact ⟨b, s, hs, rfl⟩

private theorem e8f5a_centralizer_le_AM
    {L : Type} [Field L] [IsAlgClosed L] (S : LangSetup Tag.E8 L 5) {a : Fin Tag.E8.rank → Lˣ}
    (h : E8TwoFiveSetup S a) (hA : E8TwoFiveKernelA S.ρ (rootCharHom a)) :
    S.Γ ⊓ Subgroup.centralizer {rootDiagUnit Tag.E8 a} ≤
      rootSpan Tag.E8 L (kernelRoots (rootCharHom a)) ⊓ S.D.model := by
  classical
  intro x hx
  have hxM : x ∈ S.D.model :=
    CFSG.HardMathSupport.Timmesfeld.LangTorus.commutator_le_self_of_subgroup S.D.model
      (Subgroup.mem_inf.mp hx).1
  have hxC : x ∈ Subgroup.centralizer {rootDiagUnit Tag.E8 a} := (Subgroup.mem_inf.mp hx).2
  have hxT : x ∈ toralCentralizer Tag.E8 L a := by
    refine mem_toralCentralizer.2 ⟨(S.D.mem_model.mp hxM).1, ?_⟩
    exact conj_eq_iff_mem_centralizer.2 hxC
  obtain ⟨b, s, hs, hbx⟩ := e8f5a_decomp h.2.2.2.1 hxT
  refine ⟨?_, hxM⟩
  rw [hbx]
  refine mul_mem (e8f5a_torus_le_rootSpan (fun β hβ => hβ.1) (fun β hβ => ?_)
    (e8f5a_rank_eight S hA) b) hs
  exact ⟨isRoot_neg_iff.2 hβ.1, by rw [ofAdd_neg, map_inv, hβ.2, inv_one]⟩

theorem e8TwoFive_kernelA_centralizer_le
    {L : Type} [Field L] [IsAlgClosed L]
    (S : LangSetup Tag.E8 L 5) {a : Fin Tag.E8.rank → Lˣ} (h : E8TwoFiveSetup S a)
    (hA : E8TwoFiveKernelA S.ρ (rootCharHom a)) (i : KernelComponent (rootCharHom a)) :
    S.Γ ⊓ Subgroup.centralizer {rootDiagUnit Tag.E8 a} ≤
      rationalComponent S.ρ S.Γ (rootCharHom a) i := by
  classical
  have hT := h.2.1
  obtain ⟨i₁, i₂, hne, hall, hrk, hcard, hkind, h12, h21⟩ := e8f5a_swap S h hA
  have hR : rationalComponent S.ρ S.Γ (rootCharHom a) i =
      rationalComponent S.ρ S.Γ (rootCharHom a) i₁ := by
    unfold rationalComponent rationalSpan
    rw [e8f5a_rationalRoots_eq S h hA i, e8f5a_rationalRoots_eq S h hA i₁]
  rw [hR]
  obtain ⟨hs0, hs, hmin⟩ := outer_componentOrbitLength_spec S hT i₁
  set s := componentOrbitLength S.ρ (componentRoots (rootCharHom a) i₁) with hsdef
  haveI : NeZero s := ⟨hs0.ne'⟩
  have hs2 : s = 2 := e8f5a_orbitLength_two S h hA i₁
  obtain ⟨H, θ, hHperf, hθS, hθfix, hθonto⟩ := e8f5a_unitary_fixed S h hA hrk hcard hkind
  set P := outerOrbitFamily S hT i₁ hs hmin with hP
  have hP0 : P.S 0 = rootSpan Tag.E8 L (componentRoots (rootCharHom a) i₁) := by
    rw [hP, outerOrbitFamily_S, ZMod.val_zero]
    simp only [Function.iterate_zero, id_eq, Set.image_id']
  let θ₀ : H →* P.S 0 := θ.codRestrict (P.S 0) fun c => by
    rw [hP0]
    exact hθS c
  have hθ₀fix : ∀ x, iterHom S.D.step s ((θ₀ x : P.S 0) : ModGL Tag.E8 L) = θ₀ x :=
    fun x => hθfix x
  intro x hx
  have hxAM := e8f5a_centralizer_le_AM S h hA hx
  have hxF : S.D.step x = x := (S.D.mem_model.mp hxAM.2).2
  obtain ⟨y, hyfix, rfl⟩ := e8f5a_norm_decomp S h hA i₁ hs hmin hs2 hxAM.1 hxF
  obtain ⟨c₀, hc₀⟩ := hθonto y (by rw [← hP0]; exact y.2) hyfix
  have hy' : y = θ₀ c₀ := Subtype.ext hc₀.symm
  rw [hy']
  exact outer_norm_mem_rationalComponent S hT i₁ hs hmin hHperf θ₀ hθ₀fix c₀

private theorem e8f5a_j4_injective_of_cover
    {C R : Type*} [Group C] [Finite C] [Group R] (g : C →* R)
    (hsurj : Function.Surjective g) (hker : g.ker ≤ Subgroup.center C)
    (hperf : Group.IsPerfect C) (hcard : Nat.card (Subgroup.center C) ∣ 5)
    {d : R} (hdZ : d ∈ Subgroup.center R) (hd1 : d ≠ 1) :
    Function.Injective g := by
  haveI : Group.IsPerfect C := hperf
  have hZle : Subgroup.center R ≤ Subgroup.map g (Subgroup.center C) :=
    le_of_eq (CFSG.RankThree.PartOne.Sec66T.center_eq_map_of_perfect g hsurj hker)
  rw [← MonoidHom.ker_eq_bot_iff, Subgroup.eq_bot_iff_forall]
  intro x hx
  by_contra hxne
  have hker_ne : g.ker ≠ ⊥ := by
    intro hbot
    exact hxne (Subgroup.mem_bot.mp (hbot ▸ hx))
  have hlt : 1 < Nat.card g.ker := (Subgroup.one_lt_card_iff_ne_bot g.ker).mpr hker_ne
  have hker_dvd : Nat.card g.ker ∣ 5 := (Subgroup.card_dvd_of_le hker).trans hcard
  have hker_card : Nat.card g.ker = 5 := by
    rcases (Nat.dvd_prime Nat.prime_five).mp hker_dvd with h | h
    · omega
    · exact h
  have hcenter_card : Nat.card (Subgroup.center C) = 5 :=
    Nat.dvd_antisymm hcard (hker_card ▸ Subgroup.card_dvd_of_le hker)
  have hcard_le : Nat.card (Subgroup.center C) ≤ Nat.card g.ker := by
    rw [hcenter_card, hker_card]
  have hker_eq : g.ker = Subgroup.center C :=
    Subgroup.eq_of_le_of_card_ge hker hcard_le
  obtain ⟨y, hyZ, hy_eq⟩ := Subgroup.mem_map.mp (hZle hdZ)
  have hy_ker : y ∈ g.ker := by rw [hker_eq]; exact hyZ
  exact hd1 (hy_eq.symm.trans (MonoidHom.mem_ker.mp hy_ker))

private theorem e8f5a_j4_cover
    {L : Type} [Field L] [IsAlgClosed L] (S : LangSetup Tag.E8 L 5) {a : Fin Tag.E8.rank → Lˣ}
    (hT : rootDiagUnit Tag.E8 a ∈ S.D.torus) (h2 : S.D.q = 2)
    (i : KernelComponent (rootCharHom a))
    (horb : componentOrbitLength S.ρ (componentRoots (rootCharHom a) i) = 2)
    {ψ : SL(5, L) →* ModGL Tag.E8 L}
    {σ : Fin 5 → Fin 5 → Fin Tag.E8.rank → ℤ}
    (hψ : IsSLFrame ψ σ) (hΨ : componentRoots (rootCharHom a) i = frameRoots σ)
    (π : Equiv.Perm (Fin 5))
    (hπ : ∀ x y, x ≠ y → (S.ρ : (Fin Tag.E8.rank → ℤ) → _)^[componentOrbitLength S.ρ
      (componentRoots (rootCharHom a) i)] (σ x y) = σ (π y) (π x)) :
    ∃ (K : Type) (_ : Field K) (_ : Finite K) (f : ℕ),
      1 ≤ f ∧ Nat.card K = (ringChar L ^ f) ^ 2 ∧
      ringChar L ^ f = S.D.q ^ componentOrbitLength S.ρ (componentRoots (rootCharHom a) i) ∧
      ringChar K = ringChar L ∧ (5, ringChar L ^ f) ≠ (3, 2) ∧
      Group.IsPerfect ↥(CFSG.Open.StatedSU 5 (ringChar L ^ f) K) ∧
      Nat.card (Subgroup.center ↥(CFSG.Open.StatedSU 5 (ringChar L ^ f) K)) ∣ 5 ∧
      ∃ g : ↥(CFSG.Open.StatedSU 5 (ringChar L ^ f) K) →*
          ↥(rationalComponent S.ρ S.Γ (rootCharHom a) i),
        Function.Surjective g ∧
          g.ker ≤ Subgroup.center ↥(CFSG.Open.StatedSU 5 (ringChar L ^ f) K) := by
  classical
  obtain ⟨hs0, -, -⟩ := outer_componentOrbitLength_spec S hT i
  obtain ⟨r, e, hr, hchar, he, hq⟩ := exists_char_pow S
  haveI : Fact r.Prime := ⟨hr⟩
  haveI : CharP L r := hchar
  set s := componentOrbitLength S.ρ (componentRoots (rootCharHom a) i) with hsdef
  have hs2 : s = 2 := hsdef.trans horb
  have hes : 0 < e * s := Nat.mul_pos he hs0
  have hrL : ringChar L = r := ringChar.eq L r
  have hrs : r ^ (e * s) = 2 ^ 2 := by rw [pow_mul, ← hq, h2, hs2]
  have h32r : (5, r ^ (e * s)) ≠ (3, 2) := by
    rw [hrs]
    intro hh
    exact absurd (congrArg Prod.snd hh) (by norm_num)
  obtain ⟨σQ, hσc, f, hf1, hfker, hf2⟩ :=
    CFSG.HardMathSupport.Dickson.Sec6.Up34Exc.two_suN_exists_hom S hT i (ν := 5)
      (by norm_num) hψ hΨ π hπ hr hchar he hq
  obtain ⟨hfin, hqsC, -⟩ := stdUnitary_fixSubgroup (ν := 5) hr hes σQ hσc (by norm_num)
  have hCperf : Group.IsPerfect
      ↥(CFSG.RankThree.Classical2.fixSubgroup (stdUnitaryEquiv (ν := 5) σQ)) :=
    (hqsC h32r).1
  have hRf : f.range = rationalComponent S.ρ S.Γ (rootCharHom a) i :=
    le_antisymm (hf2 hCperf) hf1
  let g : ↥(CFSG.RankThree.Classical2.fixSubgroup (stdUnitaryEquiv (ν := 5) σQ)) →*
      ↥(rationalComponent S.ρ S.Γ (rootCharHom a) i) :=
    f.codRestrict _ (fun c => hRf ▸ ⟨c, rfl⟩)
  have hgker : g.ker ≤ Subgroup.center
      ↥(CFSG.RankThree.Classical2.fixSubgroup (stdUnitaryEquiv (ν := 5) σQ)) := by
    intro c hc
    apply hfker
    rw [MonoidHom.mem_ker] at hc ⊢
    exact congrArg Subtype.val hc
  obtain ⟨F, hFcard, ⟨eC⟩⟩ :=
    CFSG.HardMathSupport.Dickson.Sec6.Up34Exc.two_suN_exists_equiv (ν := 5) hr hes σQ hσc
      (by norm_num)
  haveI : Finite ↥F := Nat.finite_of_card_ne_zero (by
    rw [hFcard]
    exact (pow_pos (pow_pos hr.pos _) 2).ne')
  let g' : ↥(CFSG.Open.StatedSU 5 (r ^ (e * s)) F) →*
      ↥(rationalComponent S.ρ S.Γ (rootCharHom a) i) := g.comp eC.toMonoidHom
  have hg'surj : Function.Surjective g' := by
    rintro ⟨x, hx⟩
    obtain ⟨c, hc⟩ : x ∈ f.range := hRf ▸ hx
    obtain ⟨c', rfl⟩ := eC.surjective c
    exact ⟨c', Subtype.ext hc⟩
  have hg'ker : g'.ker ≤ Subgroup.center ↥(CFSG.Open.StatedSU 5 (r ^ (e * s)) F) :=
    CFSG.HardMathSupport.Solomon.Coordinator.LieComp.ker_comp_mulEquiv_le_center eC g hgker
  have hring : ringChar ↥F = ringChar L :=
    CFSG.HardMathSupport.Solomon.Coordinator.LieComp.ringChar_subfield' _
  have hperfF : Group.IsPerfect ↥(CFSG.Open.StatedSU 5 (r ^ (e * s)) F) :=
    (CFSG.LieType.Universal.Unitary.isQuasisimple_statedSU_of_card (n := 5) (p := r) (f := e * s)
      hFcard (by norm_num) h32r).1.1
  have hZcardF : Nat.card (Subgroup.center ↥(CFSG.Open.StatedSU 5 (r ^ (e * s)) F)) ∣ 5 := by
    have hFcard'' : Nat.card F = (2 ^ 2) ^ 2 := by rw [← hrs]; exact hFcard
    have h := CFSG.StandardType.card_center_statedSU_dvd (n := 2) (d := 5) (F := F)
      hFcard'' (by norm_num)
    norm_num at h
    rw [hrs]
    exact h
  rw [hrL]
  refine ⟨↥F, inferInstance, inferInstance, e * s, Nat.mul_pos he hs0, hFcard,
    ?_, ?_, ?_, hperfF, hZcardF, g', hg'surj, hg'ker⟩
  · rw [pow_mul, ← hq]
  · exact hring.trans hrL
  · exact h32r

private theorem e8f5a_rationalComponent_equiv
    {L : Type} [Field L] [IsAlgClosed L]
    (S : LangSetup Tag.E8 L 5) {a : Fin Tag.E8.rank → Lˣ} (h : E8TwoFiveSetup S a)
    (hA : E8TwoFiveKernelA S.ρ (rootCharHom a)) (i : KernelComponent (rootCharHom a)) :
    ∃ (K : Type) (_ : Field K) (_ : Finite K), Nat.card K = (2 ^ 2) ^ 2 ∧
      Nonempty (↥(CFSG.Open.StatedSU 5 (2 ^ 2) K) ≃*
        ↥(rationalComponent S.ρ S.Γ (rootCharHom a) i)) := by
  classical
  obtain ⟨i₁, i₂, hne, hall, hrk, hcard, hkind, h12, h21⟩ := e8f5a_swap S h hA
  have hR : rationalComponent S.ρ S.Γ (rootCharHom a) i =
      rationalComponent S.ρ S.Γ (rootCharHom a) i₁ := by
    unfold rationalComponent rationalSpan
    rw [e8f5a_rationalRoots_eq S h hA i, e8f5a_rationalRoots_eq S h hA i₁]
  obtain ⟨ψ, σ, hψ, hΨ, -, π, hπ⟩ := e8f5a_exists_frame S h hrk hcard hkind
  have horb : componentOrbitLength S.ρ (componentRoots (rootCharHom a) i₁) = 2 :=
    e8f5a_orbitLength_two S h hA i₁
  obtain ⟨K, hKfield, hKfin, f, hf1, hKcard, hKq, hKchar, hne32, hperf, hZcard, g, hgsurj,
    hgker⟩ :=
    e8f5a_j4_cover S h.2.1 h.1 i₁ horb hψ hΨ π hπ
  haveI : Finite K := hKfin
  have hring : ringChar L ^ f = 2 ^ 2 := by rw [hKq, h.1, horb]
  have hKcard' : Nat.card K = (2 ^ 2) ^ 2 := by
    rw [hring] at hKcard
    exact hKcard
  have hRle : rationalComponent S.ρ S.Γ (rootCharHom a) i₁ ≤
      S.Γ ⊓ Subgroup.centralizer {rootDiagUnit Tag.E8 a} :=
    (langSubnormal_of_mem_torus S h.2.1 i₁).1
  have hdcent : rootDiagUnit Tag.E8 a ∈ Subgroup.centralizer {rootDiagUnit Tag.E8 a} :=
    Subgroup.mem_centralizer_iff_commutator_eq_one'.mpr fun x hx => by
      rw [Set.mem_singleton_iff] at hx
      rw [hx]
      simp
  have hdR : rootDiagUnit Tag.E8 a ∈ rationalComponent S.ρ S.Γ (rootCharHom a) i₁ :=
    e8TwoFive_kernelA_centralizer_le S h hA i₁ ⟨h.2.2.1, hdcent⟩
  have hdZ : (⟨rootDiagUnit Tag.E8 a, hdR⟩ :
      ↥(rationalComponent S.ρ S.Γ (rootCharHom a) i₁)) ∈
      Subgroup.center ↥(rationalComponent S.ρ S.Γ (rootCharHom a) i₁) := by
    rw [Subgroup.mem_center_iff]
    intro x
    apply Subtype.ext
    exact (Subgroup.mem_centralizer_iff.mp
      (Subgroup.mem_inf.mp (hRle x.2)).2 (rootDiagUnit Tag.E8 a)
      (Set.mem_singleton _)).symm
  have hd1 : (⟨rootDiagUnit Tag.E8 a, hdR⟩ :
      ↥(rationalComponent S.ρ S.Γ (rootCharHom a) i₁)) ≠ 1 := by
    intro hh
    exact h.2.2.2.2 (Subtype.ext_iff.mp hh)
  have hinj : Function.Injective g :=
    e8f5a_j4_injective_of_cover g hgsurj hgker hperf hZcard hdZ hd1
  have hmul := MulEquiv.ofBijective g ⟨hinj, hgsurj⟩
  have hmul' := hmul.trans (MulEquiv.subgroupCongr hR).symm
  refine ⟨K, hKfield, hKfin, hKcard', ?_⟩
  rw [← hring]
  exact ⟨hmul'⟩

theorem e8TwoFive_statedSU_equiv
    {L : Type} [Field L] [IsAlgClosed L] (S : LangSetup Tag.E8 L 5)
    {a : Fin Tag.E8.rank → Lˣ} (h : E8TwoFiveSetup S a)
    (hA : E8TwoFiveKernelA S.ρ (rootCharHom a)) :
    ∃ (K : Type) (_ : Field K) (_ : Finite K), Nat.card K = (2 ^ 2) ^ 2 ∧
      Nonempty (↥(CFSG.Open.StatedSU 5 (2 ^ 2) K) ≃*
        ↥(S.Γ ⊓ Subgroup.centralizer {rootDiagUnit Tag.E8 a})) := by
  classical
  obtain ⟨i₁, -⟩ := e8f5a_swap S h hA
  obtain ⟨K, hF, hfin, hK, ⟨e⟩⟩ := e8f5a_rationalComponent_equiv S h hA i₁
  have heq : rationalComponent S.ρ S.Γ (rootCharHom a) i₁ =
      S.Γ ⊓ Subgroup.centralizer {rootDiagUnit Tag.E8 a} :=
    le_antisymm (langSubnormal_of_mem_torus S h.2.1 i₁).1
      (e8TwoFive_kernelA_centralizer_le S h hA i₁)
  exact ⟨K, hF, hfin, hK, ⟨e.trans (MulEquiv.subgroupCongr heq)⟩⟩

private theorem e8f5a_j5_norm_two {G : Type*} [Group G] {F : G →* G}
    (P : CycFamily F 2) (t : P.S 0) : P.norm t = (t : G) * F t := by
  have h2 : (2 : ZMod 2) = 0 := by decide +kernel
  have hdiag : P.diag t = Pi.mulSingle 0 (P.diag t 0) * Pi.mulSingle 1 (P.diag t 1) := by
    funext k
    have hk : k = 0 ∨ k = 1 := by
      have := natCast_eq_zero_or_one_of_two_eq_zero k.val h2
      rwa [ZMod.natCast_zmod_val] at this
    rcases hk with rfl | rfl <;> simp
  show P.mu (P.diag t) = (t : G) * F t
  rw [hdiag, map_mul, P.mu_mulSingle, P.mu_mulSingle, P.coe_diag_apply, P.coe_diag_apply]
  rw [ZMod.val_zero, iterHom_zero]
  have h1 : (1 : ZMod 2).val = 1 := by decide +kernel
  rw [h1, iterHom_succ, iterHom_zero]

private theorem e8f5a_j5_commute_of_norm {G : Type*} [Group G] {F : G →* G}
    (P : CycFamily F 2) {d : G} (hdF : F d = d)
    (hd0 : ∀ x ∈ P.S 0, d * x * d⁻¹ ∈ P.S 0)
    (hinter : ∀ c : G, c ∈ P.S 0 → c ∈ P.S 1 → F c = c ∧ c ^ 5 = 1)
    {t : P.S 0} (hy : d * P.norm t * d⁻¹ = P.norm t) :
    d * (t : G) = (t : G) * d := by
  set T : G := d * (t : G) * d⁻¹ with hTdef
  have hT0 : T ∈ P.S 0 := hd0 t t.2
  set u : G := (t : G)⁻¹ * T with hudef
  have hu0 : u ∈ P.S 0 := mul_mem (inv_mem t.2) hT0
  have hTtu : T = (t : G) * u := by rw [hudef, hTdef]; group
  have hL : d * P.norm t * d⁻¹ = T * F T := by
    rw [e8f5a_j5_norm_two P t, hTdef]
    rw [map_mul, map_mul, map_inv, hdF]
    group
  have hcomm_ut : Commute u (F (t : G)) := by
    have hFt1 : F (t : G) ∈ P.S 1 := by
      have hm : F (t : G) ∈ (P.S 0).map F := Subgroup.mem_map_of_mem F t.2
      rwa [P.map_eq 0, zero_add] at hm
    exact P.comm 0 1 (by decide +kernel) u hu0 (F (t : G)) hFt1
  have hkey : u * F u = 1 := by
    have e : (t : G) * u * F (t : G) * F u = (t : G) * F (t : G) := by
      have h1 : T * F T = P.norm t := hL.symm.trans hy
      rw [hTtu, map_mul, e8f5a_j5_norm_two P t] at h1
      simpa only [mul_assoc] using h1
    have h2 : ((t : G) * F (t : G)) * (u * F u) = ((t : G) * F (t : G)) * 1 := by
      calc ((t : G) * F (t : G)) * (u * F u)
          = (t : G) * (F (t : G) * u) * F u := by group
        _ = (t : G) * (u * F (t : G)) * F u := by rw [← hcomm_ut.eq]
        _ = (t : G) * u * F (t : G) * F u := by group
        _ = (t : G) * F (t : G) := e
        _ = ((t : G) * F (t : G)) * 1 := by rw [mul_one]
    exact mul_left_cancel h2
  have hFu : F u = u⁻¹ := eq_inv_of_mul_eq_one_right hkey
  have hc0 : F u ∈ P.S 0 := by rw [hFu]; exact inv_mem hu0
  have hc1 : F u ∈ P.S 1 := by
    have hm : F u ∈ (P.S 0).map F := Subgroup.mem_map_of_mem F hu0
    rwa [P.map_eq 0, zero_add] at hm
  have hc_eq : F u = (F u)⁻¹ := by
    have h1 : F (F u) = F u := (hinter (F u) hc0 hc1).1
    have h1' : F (u⁻¹) = F u := by rw [← hFu]; exact h1
    have h2 : F (u⁻¹) = (F u)⁻¹ := map_inv F u
    exact (h2.symm.trans h1').symm
  have hc2 : (F u) ^ 2 = 1 := by
    rw [pow_two]
    nth_rewrite 2 [hc_eq]
    exact mul_inv_cancel (F u)
  have hc5 : (F u) ^ 5 = 1 := (hinter (F u) hc0 hc1).2
  have hc_one : F u = 1 := by
    have := (pow_gcd_eq_one (a := F u) (m := 2) (n := 5)).2 ⟨hc2, hc5⟩
    simpa using this
  have hu1 : u = 1 := by
    have : u⁻¹ = 1 := by rw [← hFu]; exact hc_one
    exact inv_eq_one.mp this
  have hdT : d * (t : G) * d⁻¹ = (t : G) := by
    rw [← hTdef]
    rw [hTtu, hu1, mul_one]
  calc d * (t : G) = d * (t : G) * d⁻¹ * d := by group
    _ = (t : G) * d := by rw [hdT]

private theorem e8f5a_j5_conjDiagn_apply {L : Type} [Field L] {ν : ℕ} (d : Fin ν → Lˣ)
    (A : SL(ν, L)) (k l : Fin ν) :
    ((conjDiagn d A : SL(ν, L)) : Matrix (Fin ν) (Fin ν) L) k l =
      (d k : L) * (A : Matrix (Fin ν) (Fin ν) L) k l * ((d l : L))⁻¹ := by
  rw [CFSG.RankThree.PartOne.KE.coe_conjDiagn]
  change (Matrix.diagonal (fun i => (d i : L)) * (A : Matrix (Fin ν) (Fin ν) L) *
      Matrix.diagonal (fun i => (((d i)⁻¹ : Lˣ) : L))) k l = _
  have hdiag : (fun i => (((d i)⁻¹ : Lˣ) : L)) = (fun i => ((d i : L))⁻¹) := by
    funext i
    exact Units.val_inv_eq_inv_val (d i)
  rw [hdiag, Matrix.mul_diagonal, Matrix.diagonal_mul]

private theorem e8f5a_j5_diag_comm {L : Type} [Field L] {ν : ℕ} {D : Fin ν → Lˣ}
    (hD : Function.Injective D) {A A' : SL(ν, L)}
    (hA : conjDiagn D A = A) (hA' : conjDiagn D A' = A') : A * A' = A' * A := by
  have hoff : ∀ (B : SL(ν, L)), conjDiagn D B = B →
      ∀ i j : Fin ν, i ≠ j → (B : Matrix (Fin ν) (Fin ν) L) i j = 0 := by
    intro B hB i j hij
    have h : ((conjDiagn D B : SL(ν, L)) : Matrix (Fin ν) (Fin ν) L) i j =
        (B : Matrix (Fin ν) (Fin ν) L) i j := by
      rw [hB]
    rw [e8f5a_j5_conjDiagn_apply] at h
    have hDne : (D i : L) ≠ (D j : L) := by
      intro hc
      exact hij (hD (Units.ext hc))
    have hmul : (D i : L) * (B : Matrix (Fin ν) (Fin ν) L) i j =
        (D j : L) * (B : Matrix (Fin ν) (Fin ν) L) i j := by
      have h2 : (D i : L) * (B : Matrix (Fin ν) (Fin ν) L) i j *
          ((D j : L)⁻¹ * (D j : L)) =
          (D i : L) * (B : Matrix (Fin ν) (Fin ν) L) i j := by
        rw [inv_mul_cancel₀ (Units.ne_zero (D j)), mul_one]
      rw [← h2, ← mul_assoc, h, mul_comm]
    have hmain : ((D i : L) - (D j : L)) * (B : Matrix (Fin ν) (Fin ν) L) i j = 0 := by
      rw [sub_mul, hmul, sub_self]
    exact (mul_eq_zero.mp hmain).resolve_left (sub_ne_zero.mpr hDne)
  have hdiagB : ∀ (B : SL(ν, L)), conjDiagn D B = B →
      (B : Matrix (Fin ν) (Fin ν) L) =
        Matrix.diagonal (fun i => (B : Matrix (Fin ν) (Fin ν) L) i i) := by
    intro B hB
    ext i j
    by_cases h : i = j
    · subst h
      rw [Matrix.diagonal_apply_eq]
    · rw [Matrix.diagonal_apply_ne _ h]
      exact hoff B hB i j h
  apply Subtype.ext
  rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul, hdiagB A hA,
    hdiagB A' hA', Matrix.diagonal_mul_diagonal, Matrix.diagonal_mul_diagonal]
  congr 1
  funext i
  exact mul_comm _ _

theorem e8TwoFive_plane_centralizer_comm
    {L : Type} [Field L] [IsAlgClosed L]
    (S : LangSetup Tag.E8 L 5) {a : Fin Tag.E8.rank → Lˣ} (h : E8TwoFiveSetup S a)
    (hA : E8TwoFiveKernelA S.ρ (rootCharHom a)) {b : Fin Tag.E8.rank → Lˣ}
    (hbT : rootDiagUnit Tag.E8 b ∈ S.D.torus) (hbΓ : rootDiagUnit Tag.E8 b ∈ S.Γ)
    (hb5 : ∀ i, b i ^ 5 = 1)
    (hdisj : ∀ β ∈ kernelRoots (rootCharHom a), rootChar b β ≠ 1) :
    IsMulCommutative ↥(S.Γ ⊓ Subgroup.centralizer {rootDiagUnit Tag.E8 a} ⊓
      Subgroup.centralizer {rootDiagUnit Tag.E8 b}) := by
  classical
  let Y : Subgroup (ModGL Tag.E8 L) :=
    S.Γ ⊓ Subgroup.centralizer {rootDiagUnit Tag.E8 a} ⊓
      Subgroup.centralizer {rootDiagUnit Tag.E8 b}
  change IsMulCommutative ↥Y
  obtain ⟨i₁, i₂, hne, hall, hrk, hcard, hkind, h12, h21⟩ := e8f5a_swap S h hA
  have hs2 : componentOrbitLength S.ρ (componentRoots (rootCharHom a) i₁) = 2 :=
    e8f5a_orbitLength_two S h hA i₁
  obtain ⟨hs0, hs, hmin⟩ := outer_componentOrbitLength_spec S h.2.1 i₁
  have hs' : (S.ρ : (Fin Tag.E8.rank → ℤ) → _)^[2] '' componentRoots (rootCharHom a) i₁ =
      componentRoots (rootCharHom a) i₁ := by
    rw [← hs2]
    exact hs
  have hmin' : ∀ k, 0 < k → k < 2 →
      (S.ρ : (Fin Tag.E8.rank → ℤ) → _)^[k] '' componentRoots (rootCharHom a) i₁ ≠
        componentRoots (rootCharHom a) i₁ := by
    intro k hk hk2
    exact hmin k hk (by rwa [← hs2] at hk2)
  let P : CycFamily S.D.step 2 := outerOrbitFamily S h.2.1 i₁ hs' hmin'
  have hP0 : P.S 0 = rootSpan Tag.E8 L (componentRoots (rootCharHom a) i₁) := by
    change (outerOrbitFamily S h.2.1 i₁ hs' hmin').S 0 = _
    rw [outerOrbitFamily_S, ZMod.val_zero]
    simp only [Function.iterate_zero, id_eq, Set.image_id']
  have hP1 : P.S 1 = rootSpan Tag.E8 L (componentRoots (rootCharHom a) i₂) := by
    change (outerOrbitFamily S h.2.1 i₁ hs' hmin').S 1 = _
    rw [outerOrbitFamily_S]
    have h1val : (1 : ZMod 2).val = 1 := by decide +kernel
    rw [h1val, Function.iterate_one, h12]
  obtain ⟨ψ, σ, hψ, hΨ, hif, π, hπ⟩ := e8f5a_exists_frame S h hrk hcard hkind
  have hinjψ : Function.Injective ψ := e8f5a_frame_injective S h hA hψ hΨ
  set db : ModGL Tag.E8 L := rootDiagUnit Tag.E8 b with hdb
  have hdb_torus : db ∈ torusGroup Tag.E8 L :=
    (CFSG.RankThree.PartOne.KE.mem_twistedTorusOf.mp hbT).1
  have hdb_model : db ∈ S.D.model :=
    CFSG.HardMathSupport.Timmesfeld.LangTorus.commutator_le_self_of_subgroup S.D.model hbΓ
  have hdF : S.D.step db = db := (S.D.mem_model.mp hdb_model).2
  have hroot : ∀ α ∈ componentRoots (rootCharHom a) i₁, IsRoot Tag.E8 α :=
    fun α hα => CFSG.ComponentClassification.ExcSelector.isRoot_of_mem_componentRoots hα
  have hnorm1 : db ∈ Subgroup.normalizer
      (rootSpan Tag.E8 L (componentRoots (rootCharHom a) i₁) : Set (ModGL Tag.E8 L)) :=
    CFSG.LieType.Chevalley.torusGroup_le_normalizer_rootSpan hroot hdb_torus
  have hd0 : ∀ x ∈ P.S 0, db * x * db⁻¹ ∈ P.S 0 := by
    intro x hx
    rw [hP0] at hx ⊢
    exact (Subgroup.mem_normalizer_iff.mp hnorm1 x).mp hx
  have hinter : ∀ c : ModGL Tag.E8 L, c ∈ P.S 0 → c ∈ P.S 1 →
      S.D.step c = c ∧ c ^ 5 = 1 := by
    intro c hc0 hc1
    rw [hP0] at hc0
    rw [hP1] at hc1
    exact e8f5a_inter_fixed S h hA hne hc0 hc1
  let D : Fin 5 → Lˣ := fun i => rootChar b (σ i 0)
  have hDinj : Function.Injective D := by
    intro x y hxy
    by_contra hxy'
    have hxy'' : rootChar b (σ x 0) = rootChar b (σ y 0) := hxy
    have hroot1 : rootChar b (σ x y) = 1 := by
      rw [hψ.eq_sub x y 0, rootChar_sub]
      rw [hxy'', mul_inv_cancel]
    have hmem : σ x y ∈ componentRoots (rootCharHom a) i₁ := by
      rw [hΨ]
      exact ⟨x, y, hxy', rfl⟩
    have hker : σ x y ∈ kernelRoots (rootCharHom a) := hmem.elim fun h _ => h
    exact hdisj (σ x y) hker hroot1
  have step3 : ∀ t : P.S 0, db * (t : ModGL Tag.E8 L) = (t : ModGL Tag.E8 L) * db →
      ∃ A : SL(5, L), conjDiagn D A = A ∧ ψ A = (t : ModGL Tag.E8 L) := by
    intro t ht
    have htmem : (t : ModGL Tag.E8 L) ∈ rootSpan Tag.E8 L (frameRoots σ) := by
      have h1 : (t : ModGL Tag.E8 L) ∈
          rootSpan Tag.E8 L (componentRoots (rootCharHom a) i₁) := (le_of_eq hP0) t.2
      rwa [hΨ] at h1
    have htmem' : (t : ModGL Tag.E8 L) ∈ ψ.range := by rwa [hψ.range]
    obtain ⟨A, hAψ⟩ := MonoidHom.mem_range.mp htmem'
    refine ⟨A, ?_, hAψ⟩
    apply hinjψ
    rw [hAψ, ← hψ.torus 0 b A, hAψ]
    rw [← hdb, ht]
    group
  have key : ∀ x : ↥Y, ∃ (t : P.S 0) (A : SL(5, L)),
      (x : ModGL Tag.E8 L) = P.norm t ∧ conjDiagn D A = A ∧
        ψ A = (t : ModGL Tag.E8 L) := by
    intro x
    obtain ⟨hxΓa, hxb⟩ := Subgroup.mem_inf.mp x.2
    obtain ⟨hxΓ, hxa⟩ := Subgroup.mem_inf.mp hxΓa
    have hxAM := e8f5a_centralizer_le_AM S h hA ⟨hxΓ, hxa⟩
    have hxA : (x : ModGL Tag.E8 L) ∈
        rootSpan Tag.E8 L (kernelRoots (rootCharHom a)) := hxAM.1
    have hxF : S.D.step (x : ModGL Tag.E8 L) = (x : ModGL Tag.E8 L) :=
      (S.D.mem_model.mp hxAM.2).2
    obtain ⟨t, -, hxt⟩ := e8f5a_norm_decomp S h hA i₁ hs' hmin' rfl hxA hxF
    have hcomm : db * (t : ModGL Tag.E8 L) = (t : ModGL Tag.E8 L) * db := by
      refine e8f5a_j5_commute_of_norm P hdF hd0 hinter ?_
      have hxb' : db * P.norm t = P.norm t * db := by
        rw [← hxt]
        exact Subgroup.mem_centralizer_iff.mp hxb db hdb
      rw [hxb', mul_assoc, mul_inv_cancel, mul_one]
    obtain ⟨A, hAdiag, hAψ⟩ := step3 t hcomm
    exact ⟨t, A, hxt, hAdiag, hAψ⟩
  refine ⟨⟨fun x y => Subtype.ext ?_⟩⟩
  obtain ⟨t, A, hxt, hAdiag, hAψ⟩ := key x
  obtain ⟨t', A', hyt, hAdiag', hAψ'⟩ := key y
  have hAA := e8f5a_j5_diag_comm hDinj hAdiag hAdiag'
  have htt : t * t' = t' * t := by
    apply Subtype.ext
    rw [Subgroup.coe_mul, Subgroup.coe_mul, ← hAψ, ← hAψ', ← map_mul, ← map_mul, hAA]
  calc (x : ModGL Tag.E8 L) * (y : ModGL Tag.E8 L)
      = P.norm t * P.norm t' := by rw [hxt, hyt]
    _ = P.norm (t * t') := by rw [map_mul]
    _ = P.norm (t' * t) := by rw [htt]
    _ = P.norm t' * P.norm t := by rw [map_mul]
    _ = (y : ModGL Tag.E8 L) * (x : ModGL Tag.E8 L) := by rw [hyt, hxt]

end FieldFiveE8

end CFSG.StandardType
