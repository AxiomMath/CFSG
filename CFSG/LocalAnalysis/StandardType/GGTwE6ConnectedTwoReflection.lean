module

public import CFSG.LocalAnalysis.StandardType.GGTwE6ConnectedReflection
public import CFSG.LieType.AlgebraicGroups.RootSpanConnected
public import CFSG.LieType.AlgebraicGroups.MatrixFixedIdentityComponent
public import CFSG.LieType.Chevalley.EvenOddCentralizerRadicalKempf
public import CFSG.LieType.Chevalley.ParabolicRadicalLevi
public import CFSG.LieType.AlgebraicGroups.FixedComponentNorm
public import CFSG.LieType.AlgebraicGroups.ConnectedCentralizerReflection
public import CFSG.Blueprint.ChevalleyRootGroupsTriangular
public import CFSG.LieType.AlgebraicGroups.ClosedIdentityComponentFunctorial
public import CFSG.LieType.AlgebraicGroups.CentralizerComponentInduction
public import CFSG.LieType.AlgebraicGroups.FixedUnipotentConnected
public import CFSG.LieType.AlgebraicGroups.UnipotentFinitePoints
public import CFSG.GroupTheory.TwoElementGeneration
public import CFSG.LieType.Chevalley.EvenOddCentralizerRadicalLift

public noncomputable section

namespace CFSG.StandardType.SCFourCover

open Subgroup CFSG.Assembly CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  CFSG.HardMathSupport.Lang.E6Descent
  CFSG.LieType.AlgebraicGroups


variable {Ω : Type} [Field Ω]

variable {n : ℕ} (hn : 1 ≤ n) {K : Type} [Field K] [Finite K]
  (hK : Nat.card K = (2 ^ n) ^ 2) (σ : K ≃+* K) (hσ : ∀ c, σ c = c ^ 2 ^ n)
  [Algebra K Ω] [IsAlgClosure K Ω]
  (Fr : Ω →+* Ω) (hFr : ∀ c, Fr c = c ^ 2 ^ n)
  (ε : ↥(graphFixedRootGroup TwistTag.E6 K σ.toRingHom) ≃* TwE6Delta.RecipeR K n)
  {L' : Type} [Group L'] [Finite L'] {ψ : L' →* TwE6Delta.RecipeR K n}
  {A : Subgroup (MulAut L')}

@[expose] noncomputable def actorNormalizer (A : Subgroup (MulAut L')) : Subgroup L' :=
  (Subgroup.normalizer (A : Set (MulAut L'))).comap (MulAut.conj : L' →* MulAut L')

def actorNormalizerMem (n : actorNormalizer A) :
    MulAut.conj (n : L') ∈ Subgroup.normalizer (A : Set (MulAut L')) := n.2

@[expose] def actorNormalizerToNormalizer (A : Subgroup (MulAut L')) :
    actorNormalizer A →* Subgroup.normalizer (A : Set (MulAut L')) where
  toFun n := ⟨MulAut.conj (n : L'), actorNormalizerMem (A := A) n⟩
  map_one' := by
    apply Subtype.ext
    exact map_one MulAut.conj
  map_mul' n m := by
    apply Subtype.ext
    exact map_mul MulAut.conj (n : L') (m : L')

@[expose] noncomputable def actorNormalizerAction (A : Subgroup (MulAut L')) :
    actorNormalizer A →* MulAut A :=
  A.normalizerMonoidHom.comp (actorNormalizerToNormalizer A)

@[expose] noncomputable def actorModel
    (hn : 1 ≤ n) (hK : Nat.card K = (2 ^ n) ^ 2)
    (σ : K ≃+* K) (hσ : ∀ c, σ c = c ^ 2 ^ n)
    (Fr : Ω →+* Ω) (hFr : ∀ c, Fr c = c ^ 2 ^ n)
    (ε : ↥(graphFixedRootGroup TwistTag.E6 K σ.toRingHom) ≃* TwE6Delta.RecipeR K n)
    (hε : ∀ x : MulAut ↥(graphFixedRootGroup TwistTag.E6 K σ.toRingHom),
      MulAut.congr ε x ∈ TwE6Delta.RecipeI K n ↔ x ∈ (RecipeExcLang.twConj K σ).range)
    (hψ : Function.Surjective ψ) (hker : ψ.ker ≤ Subgroup.center L')
    (hperf : commutator L' = ⊤)
    (hAI : ∀ a ∈ A, ∃ φ ∈ TwE6Delta.RecipeI K n, ∀ l : L', φ (ψ l) = ψ (a l)) :
    A →* ModGL Tag.E6 Ω :=
  (rgrpModel hn hK σ hσ Fr hFr ε (TypeA.inducedSub ψ A)).subtype.comp
    (recipeActorModelEquiv hn hK σ hσ Fr hFr ε hε hψ hker hperf hAI).toMonoidHom

@[expose] noncomputable def actorMatrixModel
    (hn : 1 ≤ n) (hK : Nat.card K = (2 ^ n) ^ 2)
    (σ : K ≃+* K) (hσ : ∀ c, σ c = c ^ 2 ^ n)
    (Fr : Ω →+* Ω) (hFr : ∀ c, Fr c = c ^ 2 ^ n)
    (ε : ↥(graphFixedRootGroup TwistTag.E6 K σ.toRingHom) ≃* TwE6Delta.RecipeR K n)
    (ψ : L' →* TwE6Delta.RecipeR K n) :
    actorNormalizer A →* ModGL Tag.E6 Ω :=
  (recipeMatrixHom σ ε (ψ := ψ)).comp (actorNormalizer A).subtype

theorem actorModel_mem_adjoint
    (hn : 1 ≤ n) (hK : Nat.card K = (2 ^ n) ^ 2)
    (σ : K ≃+* K) (hσ : ∀ c, σ c = c ^ 2 ^ n)
    (Fr : Ω →+* Ω) (hFr : ∀ c, Fr c = c ^ 2 ^ n)
    (ε : ↥(graphFixedRootGroup TwistTag.E6 K σ.toRingHom) ≃* TwE6Delta.RecipeR K n)
    (hε : ∀ x : MulAut ↥(graphFixedRootGroup TwistTag.E6 K σ.toRingHom),
      MulAut.congr ε x ∈ TwE6Delta.RecipeI K n ↔ x ∈ (RecipeExcLang.twConj K σ).range)
    (hψ : Function.Surjective ψ) (hker : ψ.ker ≤ Subgroup.center L')
    (hperf : commutator L' = ⊤)
    (hAI : ∀ a ∈ A, ∃ φ ∈ TwE6Delta.RecipeI K n, ∀ l : L', φ (ψ l) = ψ (a l)) :
    ∀ a : A, actorModel hn hK σ hσ Fr hFr ε hε hψ hker hperf hAI a ∈
      adjointGroup Tag.E6 Ω := by
  intro a
  exact ((TwistedDiag.mem_Rgrp _).mp
    (rgrpModel_le_Rgrp hn hK σ hσ Fr hFr ε _
      (recipeActorModelEquiv hn hK σ hσ Fr hFr ε hε hψ hker hperf hAI a).2)).1

theorem actorMatrixModel_mem_adjoint
    (hn : 1 ≤ n) (hK : Nat.card K = (2 ^ n) ^ 2)
    (σ : K ≃+* K) (hσ : ∀ c, σ c = c ^ 2 ^ n)
    (Fr : Ω →+* Ω) (hFr : ∀ c, Fr c = c ^ 2 ^ n)
    (ε : ↥(graphFixedRootGroup TwistTag.E6 K σ.toRingHom) ≃* TwE6Delta.RecipeR K n)
    (ψ : L' →* TwE6Delta.RecipeR K n) (n : actorNormalizer A) :
    actorMatrixModel hn hK σ hσ Fr hFr ε ψ n ∈
      adjointGroup Tag.E6 Ω := by
  change (recipeMatrixHom σ ε (ψ := ψ) (n : L') : ModGL Tag.E6 Ω) ∈
    adjointGroup Tag.E6 Ω
  exact ((TwistedDiag.mem_Rgrp _).mp
    (recipeMatrixHom_mem_Rgrp hn hK σ hσ Fr hFr ε (ψ := ψ) (n : L'))).1

theorem exists_finite_actor_descent
    (hn : 1 ≤ n) (hK : Nat.card K = (2 ^ n) ^ 2)
    (σ : K ≃+* K) (hσ : ∀ c, σ c = c ^ 2 ^ n)
    (Fr : Ω →+* Ω) (hFr : ∀ c, Fr c = c ^ 2 ^ n)
    (ε : ↥(graphFixedRootGroup TwistTag.E6 K σ.toRingHom) ≃* TwE6Delta.RecipeR K n)
    (hε : ∀ x : MulAut ↥(graphFixedRootGroup TwistTag.E6 K σ.toRingHom),
      MulAut.congr ε x ∈ TwE6Delta.RecipeI K n ↔ x ∈ (RecipeExcLang.twConj K σ).range)
    (hψ : Function.Surjective ψ) (hker : ψ.ker ≤ Subgroup.center L')
    (hperf : commutator L' = ⊤)
    (hAI : ∀ a ∈ A, ∃ φ ∈ TwE6Delta.RecipeI K n, ∀ l : L', φ (ψ l) = ψ (a l)) :
    ∃ (k : Type) (_ : Field k) (_ : Finite k) (_ : CharP k 2)
      (κ : K →+* k) (ι : k →+* Ω),
      ι.comp κ = algebraMap K Ω ∧
      ∃ (e_k : A →* ↥(adjointGroup Tag.E6 k))
        (j_k : actorNormalizer A →* ↥(adjointGroup Tag.E6 k)),
        (∀ a : A, baseChangeGL ι (e_k a).val =
          actorModel hn hK σ hσ Fr hFr ε hε hψ hker hperf hAI a) ∧
        (∀ n : actorNormalizer A, baseChangeGL ι (j_k n).val =
          actorMatrixModel hn hK σ hσ Fr hFr ε ψ n) ∧
        (∀ (n : actorNormalizer A) (a : A),
          e_k (actorNormalizerAction A n a) = j_k n * e_k a * (j_k n)⁻¹) ∧
        Function.Injective e_k := by
  have : CharP K 2 :=
    CFSG.StandardType.charP_two_of_card (m := n * 2) (by rw [hK, pow_mul])
  have : CharP Ω 2 := charP_of_injective_algebraMap (algebraMap K Ω).injective 2
  let _ : Algebra (ZMod 2) Ω := ZMod.algebra Ω 2
  have : Algebra.IsAlgebraic (ZMod 2) Ω :=
    CFSG.RankThree.PartOne.KE.isAlgebraic_zmod_of_isAlgClosure (k := K)
  haveI : Finite A := Subtype.finite
  haveI : Finite (actorNormalizer A) := Subtype.finite
  have hact : ∀ n : actorNormalizer A,
      actorNormalizerAction A n = ggConjAut A (actorNormalizerMem (A := A) n) := by
    intro n
    apply MulEquiv.ext
    intro a
    rfl
  have hα : ∀ (n : actorNormalizer A) (a : A),
      actorModel hn hK σ hσ Fr hFr ε hε hψ hker hperf hAI
          (actorNormalizerAction A n a) =
        actorMatrixModel hn hK σ hσ Fr hFr ε ψ n *
          actorModel hn hK σ hσ Fr hFr ε hε hψ hker hperf hAI a *
          (actorMatrixModel hn hK σ hσ Fr hFr ε ψ n)⁻¹ := by
    intro n a
    rw [hact]
    simpa only [actorModel, actorMatrixModel, MonoidHom.comp_apply, Subgroup.coe_subtype,
      MulEquiv.coe_toMonoidHom] using
      (recipeActorModelEquiv_conj hn hK σ hσ Fr hFr ε hε hψ hker hperf hAI
        (g := (n : L')) (actorNormalizerMem (A := A) n) a)
  obtain ⟨k, hk, hkfin, hchar, κ, ι, hcomp, e_k, j_k, he_k, hj_k, hconj, hinj⟩ :=
    CFSG.StandardType.LieCore.exists_finite_adjoint_action_descent
      (e := actorModel hn hK σ hσ Fr hFr ε hε hψ hker hperf hAI)
      (j := actorMatrixModel hn hK σ hσ Fr hFr ε ψ)
      (he := actorModel_mem_adjoint hn hK σ hσ Fr hFr ε hε hψ hker hperf hAI)
      (hj := actorMatrixModel_mem_adjoint hn hK σ hσ Fr hFr ε ψ)
      (α := actorNormalizerAction A) (hα := hα) K (algebraMap K Ω)
  refine ⟨k, hk, hkfin, hchar, κ, ι, hcomp, e_k, j_k, ?_, ?_, ?_, ?_⟩
  · exact he_k
  · exact hj_k
  · exact hconj
  · apply hinj
    intro a b hab
    apply (recipeActorModelEquiv hn hK σ hσ Fr hFr ε hε hψ hker hperf hAI).injective
    apply Subtype.ext
    exact hab

theorem actorNormalizerAction_eq_ggConjAut (n : actorNormalizer A) :
    actorNormalizerAction A n = ggConjAut A (actorNormalizerMem (A := A) n) := by
  apply MulEquiv.ext
  intro a
  rfl

section TwoElement

theorem exists_two_element_lift_of_reflection
    [Finite A] {φ : MulAut A} (hφ : GGIsReflection 3 φ)
    {g : L'} (hg : MulAut.conj g ∈ Subgroup.normalizer (A : Set (MulAut L')))
    (hgφ : ggConjAut A hg = φ) :
    ∃ (g2 : L') (hg2 : MulAut.conj g2 ∈ Subgroup.normalizer (A : Set (MulAut L')))
      (m : ℕ),
      g2 ^ (2 ^ m) = 1 ∧ ggConjAut A hg2 = φ := by
  let n : actorNormalizer A := ⟨g, hg⟩
  have hσ : actorNormalizerAction A n * actorNormalizerAction A n = 1 := by
    rw [actorNormalizerAction_eq_ggConjAut, hgφ]
    simpa only [pow_two] using hφ.1
  obtain ⟨n', -, ⟨m, hm⟩, hmap⟩ :=
    CFSG.GroupTheory.exists_twoElem_mem_map (actorNormalizerAction A)
      (M := ⊤) (m := n) (Subgroup.mem_top n) hσ
  refine ⟨(n' : L'), n'.2, m, ?_, ?_⟩
  · simpa only [Subgroup.coe_pow, Subgroup.coe_one] using
      congrArg (fun x : actorNormalizer A => (x : L')) hm
  · rw [actorNormalizerAction_eq_ggConjAut] at hmap
    change ggConjAut A (actorNormalizerMem (A := A) n') =
      ggConjAut A (actorNormalizerMem (A := A) n) at hmap
    exact hmap.trans hgφ

end TwoElement


section UnipotentFixedCentralizer

variable [IsAlgClosed Ω] [CharP Ω 2]

open CFSG.LieType.AlgebraicGroups
open scoped TensorProduct

theorem isNilpotent_endOfPoint_sub_one_of_two_pow_eq_one
    {k H M : Type*} [Field k] [CharP k 2] [CommRing H] [HopfAlgebra k H]
    [AddCommMonoid M] [Module k M] [Module.Finite k M] [TauCeti.Comodule k H M]
    (g : WithConv (H →ₐ[k] k)) (n : ℕ) (hg : g ^ 2 ^ n = 1) :
    IsNilpotent (TauCeti.Comodule.endOfPoint M g.ofConv - 1) := by
  refine ⟨2 ^ n, ?_⟩
  rcases subsingleton_or_nontrivial (TensorProduct k k M) with hV | hV
  · haveI := hV
    have : Subsingleton (Module.End k (TensorProduct k k M)) :=
      ⟨fun a b => LinearMap.ext fun m => Subsingleton.elim _ _⟩
    exact Subsingleton.elim _ _
  · have : FaithfulSMul k (Module.End k (TensorProduct k k M)) := inferInstance
    let : CharP (Module.End k (TensorProduct k k M)) 2 :=
      charP_of_injective_algebraMap' (A := Module.End k (TensorProduct k k M)) k 2
    have hcomm : Commute (TauCeti.Comodule.endOfPoint M g.ofConv) 1 :=
      Commute.one_right _
    have h := sub_pow_char_pow_of_commute
      (R := Module.End k (TensorProduct k k M))
      (x := TauCeti.Comodule.endOfPoint M g.ofConv) (y := 1)
      (p := 2) (n := n) hcomm
    rw [h, one_pow]
    rw [← CFSG.LieType.AlgebraicGroups.ReductiveDescent.endOfPoint_pow
      (M := M) (g := g) (n := 2 ^ n)]
    rw [hg, TauCeti.Comodule.endOfPoint_convOne]
    exact sub_self _

theorem isUnipotentPoint_of_two_pow_eq_one
    {k H : Type*} [Field k] [CharP k 2] [CommRing H] [HopfAlgebra k H]
    (g : WithConv (H →ₐ[k] k)) (n : ℕ) (hg : g ^ 2 ^ n = 1) :
    TauCeti.HopfAlgebra.IsUnipotentPoint g := by
  rw [TauCeti.HopfAlgebra.isUnipotentPoint_iff_forall_isNilpotent_endOfPoint_sub_one]
  intro M
  haveI : Module.Finite k M.obj := TauCeti.FGComoduleCat.instFiniteCarrier M
  exact isNilpotent_endOfPoint_sub_one_of_two_pow_eq_one (M := M.obj) g n hg

theorem isUnipotentPoint_of_isPGroup_two
    {k H : Type*} [Field k] [CharP k 2] [CommRing H] [HopfAlgebra k H]
    (h2 : IsPGroup 2 (WithConv (H →ₐ[k] k)))
    (g : WithConv (H →ₐ[k] k)) : TauCeti.HopfAlgebra.IsUnipotentPoint g := by
  obtain ⟨n, hn⟩ := h2 g
  exact isUnipotentPoint_of_two_pow_eq_one g n hn

theorem connectedSpace_coordinateHopf_inf_centralizer
    (M : Subgroup (ModGL Tag.E6 Ω))
    (hM : IsPointClosed Ω
      (transportPoints (modGLPoint Tag.E6 Ω)
        (M : Set (ModGL Tag.E6 Ω))))
    [Algebra.Smooth Ω (MatrixComponents.coordinateHopf M)]
    [ConnectedSpace (PrimeSpectrum (MatrixComponents.coordinateHopf M))]
    (hM2 : IsPGroup 2 M)
    (a : ModGL Tag.E6 Ω) (ha : ∀ y ∈ M, a * y * a⁻¹ ∈ M)
    (h3 : (3 : Ω) ≠ 0) (ha3 : a ^ 3 = 1) :
    ConnectedSpace (PrimeSpectrum (MatrixComponents.coordinateHopf
        (M ⊓ Subgroup.centralizer ({a} : Set (ModGL Tag.E6 Ω))))) ∧
      Algebra.Smooth Ω (MatrixComponents.coordinateHopf
        (M ⊓ Subgroup.centralizer ({a} : Set (ModGL Tag.E6 Ω)))) ∧
      IsPGroup 2 ↥(M ⊓ Subgroup.centralizer ({a} : Set (ModGL Tag.E6 Ω))) := by
  let H := MatrixComponents.coordinateHopf M
  let : IsReduced H := TauCeti.isReduced_of_smooth Ω H
  let e := MatrixComponents.coordinatePointsMulEquiv M hM
  have hpts : IsPGroup 2 (WithConv (H →ₐ[Ω] Ω)) :=
    IsPGroup.of_equiv hM2 e.symm
  have hAll : ∀ g : WithConv (H →ₐ[Ω] Ω),
      TauCeti.HopfAlgebra.IsUnipotentPoint g :=
    fun g => isUnipotentPoint_of_isPGroup_two hpts g
  let F := fixedCoordinate H (matrixInnerCoordinate M a ha)
  have hF : ConnectedSpace (PrimeSpectrum F) :=
    connectedSpace_fixedCoordinate_of_unipotent_three H hAll h3
      (matrixInnerCoordinate M a ha) (matrixInnerCoordinate_cube M a ha ha3)
  let eB := BialgEquiv.ofBijective (matrixFixedCoordinatePointMap M hM a ha h3 ha3)
    (matrixFixedCoordinatePointMap_bijective M hM a ha h3 ha3)
  refine ⟨?_, smooth_coordinateHopf_centralizer M hM a ha h3 ha3,
    hM2.to_le inf_le_left⟩
  exact (PrimeSpectrum.homeomorphOfRingEquiv eB.toAlgEquiv.toRingEquiv).connectedSpace_iff.mpr hF

end UnipotentFixedCentralizer


section FiniteFixedCentralizer

variable [IsAlgClosed Ω] [CharP Ω 2]

theorem componentPointsHom_eq_one_of_connectedSpace
    (H : TauCeti.FiniteTypeCommHopfAlgCat Ω)
    [ConnectedSpace (PrimeSpectrum H)]
    (x : TauCeti.HopfAlgebra.points (R := Ω) (H := H)
      (CommAlgCat.of Ω Ω)) :
    H.componentPointsHom (CommAlgCat.of Ω Ω) x = 1 := by
  rw [componentPointsHom_eq_one_iff]
  rw [TauCeti.FiniteTypeCommHopfAlgCat.rationalComponentMap_apply]
  haveI : Subsingleton (ConnectedComponents (PrimeSpectrum H)) :=
    ConnectedComponents.subsingleton
  exact Subsingleton.elim _ _

theorem connectedSpace_coordinateHopf_inf_centralizer_of_finite_elemAbelian_three
    (M : Subgroup (ModGL Tag.E6 Ω))
    (hM : IsPointClosed Ω
      (transportPoints (modGLPoint Tag.E6 Ω)
        (M : Set (ModGL Tag.E6 Ω))))
    [Algebra.Smooth Ω (MatrixComponents.coordinateHopf M)]
    [ConnectedSpace (PrimeSpectrum (MatrixComponents.coordinateHopf M))]
    (hM2 : IsPGroup 2 M)
    (H : Subgroup (ModGL Tag.E6 Ω)) [Finite H]
    (hH3 : CFSG.Open.IsElemAbelian 3 H)
    (hHM : H ≤ Subgroup.normalizer (M : Set (ModGL Tag.E6 Ω)))
    (h3 : (3 : Ω) ≠ 0) :
    ConnectedSpace (PrimeSpectrum (MatrixComponents.coordinateHopf
        (M ⊓ Subgroup.centralizer (H : Set (ModGL Tag.E6 Ω))))) ∧
      Algebra.Smooth Ω (MatrixComponents.coordinateHopf
        (M ⊓ Subgroup.centralizer (H : Set (ModGL Tag.E6 Ω)))) ∧
      IsPGroup 2 ↥(M ⊓ Subgroup.centralizer (H : Set (ModGL Tag.E6 Ω))) := by
  classical
  letI : Fintype H := Fintype.ofFinite H
  let G := ModGL Tag.E6 Ω
  let Ms : Finset H → Subgroup G := fun s =>
    M ⊓ Subgroup.centralizer (((s : Set H).image (Subtype.val : H → G)) : Set G)
  have hMs_empty : Ms (∅ : Finset H) = M := by
    dsimp [Ms]
    have hc : Subgroup.centralizer (∅ : Set G) = ⊤ := by
      ext x
      simp [Subgroup.mem_centralizer_iff]
    rw [Finset.coe_empty, Set.image_empty, hc]
    simp
  have hMs_univ : Ms (Finset.univ : Finset H) =
      M ⊓ Subgroup.centralizer (H : Set G) := by
    dsimp [Ms]
    congr 1
    ext x
    simp [Subtype.coe_image, Set.range]
  have hMs_insert : ∀ (s : Finset H) (h : H),
      Ms (insert h s) = Ms s ⊓ Subgroup.centralizer ({(h : G)} : Set G) := by
    intro s h
    dsimp [Ms]
    simp only [Finset.coe_insert, Set.image_insert_eq, Set.insert_eq, Set.centralizer_union]
    ext x
    simp only [Subgroup.mem_inf, Subgroup.mem_centralizer_iff, Set.mem_inter_iff, Set.mem_union,
      Set.mem_singleton_iff]
    constructor
    · rintro ⟨hxM, hx⟩
      refine ⟨⟨hxM, ?_⟩, ?_⟩
      · intro y hy
        rcases hy with ⟨k, hk, rfl⟩
        exact hx (Subtype.val k) ⟨k, Or.inr hk, rfl⟩
      · simpa using hx (h : G) ⟨h, Or.inl rfl, rfl⟩
    · rintro ⟨⟨hxM, hxS⟩, hxH⟩
      refine ⟨hxM, ?_⟩
      intro y hy
      rcases hy with ⟨k, hk, rfl⟩
      rcases hk with rfl | hk
      · simpa using hxH
      · exact hxS (Subtype.val k) ⟨k, hk, rfl⟩
  have hmain : ∀ s : Finset H,
      ConnectedSpace (PrimeSpectrum (MatrixComponents.coordinateHopf (Ms s))) ∧
        Algebra.Smooth Ω (MatrixComponents.coordinateHopf (Ms s)) ∧
        IsPGroup 2 ↥(Ms s) := by
    intro s
    induction s using Finset.induction_on with
    | empty =>
        rw [hMs_empty]
        exact ⟨inferInstance, inferInstance, hM2⟩
    | insert h s hs ih =>
        rw [hMs_insert s h]
        have hMs_pointclosed : IsPointClosed Ω
            (transportPoints (modGLPoint Tag.E6 Ω)
              (Ms s : Set (ModGL Tag.E6 Ω))) := by
          dsimp [Ms]
          exact isPointClosed_inf hM (isPointClosed_centralizer _)
        have hh3 : (h : G) ^ 3 = 1 := hH3.2 h h.2
        have hha : ∀ y ∈ Ms s, (h : G) * y * (h : G)⁻¹ ∈ Ms s := by
          intro y hy
          change y ∈ M ∧ y ∈ Subgroup.centralizer
            ((Subtype.val '' ((s : Finset H) : Set H)) : Set G) at hy
          rcases hy with ⟨hyM, hyC⟩
          refine ⟨?_, ?_⟩
          · exact (Subgroup.mem_normalizer_iff.mp (hHM h.2) y).mp hyM
          · simp only [Subgroup.mem_centralizer_iff] at hyC ⊢
            intro z hz
            rcases hz with ⟨k, hk, rfl⟩
            have hcomm_hk : (h : G) * (k : G) = (k : G) * (h : G) := by
              exact congrArg (fun u : H => (u : G)) (hH3.1.is_comm.comm h k)
            have hcomm_inv : (h : G)⁻¹ * (k : G) = (k : G) * (h : G)⁻¹ := by
              calc
                (h : G)⁻¹ * (k : G)
                    = (h : G)⁻¹ * (k : G) * ((h : G) * (h : G)⁻¹) := by group
                _ = (h : G)⁻¹ * ((k : G) * (h : G)) * (h : G)⁻¹ := by group
                _ = (h : G)⁻¹ * ((h : G) * (k : G)) * (h : G)⁻¹ := by rw [← hcomm_hk]
                _ = (k : G) * (h : G)⁻¹ := by group
            calc
              (k : G) * ((h : G) * y * (h : G)⁻¹)
                  = (k : G) * (h : G) * y * (h : G)⁻¹ := by group
              _ = (h : G) * (k : G) * y * (h : G)⁻¹ := by rw [← hcomm_hk]
              _ = (h : G) * ((k : G) * y) * (h : G)⁻¹ := by group
              _ = (h : G) * (y * (k : G)) * (h : G)⁻¹ := by
                rw [hyC (k : G) ⟨k, hk, rfl⟩]
              _ = (h : G) * y * ((k : G) * (h : G)⁻¹) := by group
              _ = (h : G) * y * ((h : G)⁻¹ * (k : G)) := by rw [← hcomm_inv]
              _ = (h : G) * y * (h : G)⁻¹ * (k : G) := by group
        letI : ConnectedSpace (PrimeSpectrum (MatrixComponents.coordinateHopf (Ms s))) := ih.1
        letI : Algebra.Smooth Ω (MatrixComponents.coordinateHopf (Ms s)) := ih.2.1
        exact connectedSpace_coordinateHopf_inf_centralizer (Ms s) hMs_pointclosed ih.2.2
          (h : G) hha h3 hh3
  have hfin := hmain (Finset.univ : Finset H)
  rwa [hMs_univ] at hfin

theorem le_closedIdentityComponent_inf_centralizer_of_finite_elemAbelian_three
    (M H : Subgroup (ModGL Tag.E6 Ω)) [Finite H]
    (hM : IsPointClosed Ω
      (transportPoints (modGLPoint Tag.E6 Ω)
        (M : Set (ModGL Tag.E6 Ω))))
    [Algebra.Smooth Ω (MatrixComponents.coordinateHopf M)]
    [ConnectedSpace (PrimeSpectrum (MatrixComponents.coordinateHopf M))]
    (hM2 : IsPGroup 2 M)
    (hH3 : CFSG.Open.IsElemAbelian 3 H)
    (hHM : H ≤ Subgroup.normalizer (M : Set (ModGL Tag.E6 Ω)))
    (hGadM : M ≤ adjointGroup Tag.E6 Ω)
    (h3 : (3 : Ω) ≠ 0) :
    (M ⊓ Subgroup.centralizer (H : Set (ModGL Tag.E6 Ω))) ≤
      closedIdentityComponent
        (adjointGroup Tag.E6 Ω ⊓
          Subgroup.centralizer (H : Set (ModGL Tag.E6 Ω))) := by
  classical
  let Z : Subgroup (ModGL Tag.E6 Ω) :=
    M ⊓ Subgroup.centralizer (H : Set (ModGL Tag.E6 Ω))
  let Zg : Subgroup (ModGL Tag.E6 Ω) :=
    adjointGroup Tag.E6 Ω ⊓
      Subgroup.centralizer (H : Set (ModGL Tag.E6 Ω))
  have hZconn : ConnectedSpace (PrimeSpectrum (MatrixComponents.coordinateHopf Z)) := by
    have h := (connectedSpace_coordinateHopf_inf_centralizer_of_finite_elemAbelian_three
      M hM hM2 H hH3 hHM h3).1
    simpa [Z] using h
  have hZsmooth : Algebra.Smooth Ω (MatrixComponents.coordinateHopf Z) := by
    have h := (connectedSpace_coordinateHopf_inf_centralizer_of_finite_elemAbelian_three
      M hM hM2 H hH3 hHM h3).2.1
    simpa [Z] using h
  have hZpc : IsPointClosed Ω
      (transportPoints (modGLPoint Tag.E6 Ω)
        (Z : Set (ModGL Tag.E6 Ω))) := by
    dsimp [Z]
    exact isPointClosed_inf hM (isPointClosed_centralizer _)
  have hZle : Z ≤ closedIdentityComponent Z := by
    intro t ht
    let φ := (MatrixComponents.coordinatePointsMulEquiv Z hZpc).symm ⟨t, ht⟩
    have hcomp : (MatrixComponents.coordinateHopf Z).componentPointsHom
        (CommAlgCat.of Ω Ω) φ = 1 := by
      letI : ConnectedSpace (PrimeSpectrum (MatrixComponents.coordinateHopf Z)) := hZconn
      exact componentPointsHom_eq_one_of_connectedSpace (MatrixComponents.coordinateHopf Z) φ
    letI : Group (ConnectedComponents (PrimeSpectrum (MatrixComponents.coordinateHopf Z))) :=
      TauCeti.FiniteTypeCommHopfAlgCat.instGroupConnectedComponents
        (MatrixComponents.coordinateHopf Z)
    have hrat : (MatrixComponents.coordinateHopf Z).rationalComponentMap φ = 1 :=
      (componentPointsHom_eq_one_iff (MatrixComponents.coordinateHopf Z) φ).mp hcomp
    have hmem : φ ∈ MatrixComponents.identityComponentPointsSubgroup Z :=
      (TauCeti.FiniteTypeCommHopfAlgCat.rationalComponentMap_eq_one_iff
        (MatrixComponents.coordinateHopf Z) φ).mp hrat
    have hcoe : (MatrixComponents.coordinatePointsMulEquiv Z hZpc φ : ModGL Tag.E6 Ω) = t := by
      exact congrArg (fun u : Z => (u : ModGL Tag.E6 Ω))
        (MulEquiv.apply_symm_apply (MatrixComponents.coordinatePointsMulEquiv Z hZpc) ⟨t, ht⟩)
    rw [← hcoe]
    exact (MatrixComponents.coordinatePoints_mem_closedIdentityComponent_iff Z hZpc φ).mpr hmem
  have hZleZg : Z ≤ Zg := by
    rintro t ⟨htM, htH⟩
    exact ⟨hGadM htM, htH⟩
  exact hZle.trans (closedIdentityComponent_mono hZleZg)

end FiniteFixedCentralizer

end CFSG.StandardType.SCFourCover
