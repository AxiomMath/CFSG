module

public import CFSG.SignalizerFunctorTheorem.NonLocal.SpTwoTwo
public import CFSG.RankThree.PartOne.KC.SymplecticSubfieldExceptional
public import CFSG.ClassicalGroups.Symplectic.ProjectivePerfect
public import CFSG.ClassicalGroups.Symplectic.Simple
public import CFSG.Monster.Existence.Compat.Sp8
public import CFSG.Open.StatedDefs
public import Mathlib.Algebra.Group.TypeTags.Finite
public import Mathlib.Algebra.Group.TypeTags.Hom
public import Mathlib.Algebra.Group.Subgroup.Finite
public import Mathlib.Algebra.Module.ZMod
public import Mathlib.Data.Finset.Card
public import Mathlib.FieldTheory.Finiteness
public import Mathlib.GroupTheory.IsPerfect
public import Mathlib.GroupTheory.SpecificGroups.Alternating
public import Mathlib.GroupTheory.Subgroup.Simple
public import Mathlib.LinearAlgebra.BilinearForm.Properties
public import Mathlib.LinearAlgebra.Dimension.Constructions
public import Mathlib.LinearAlgebra.Dimension.Finite
public import Mathlib.LinearAlgebra.Dimension.Finrank
public import Mathlib.LinearAlgebra.Dimension.Free
public import Mathlib.SetTheory.Cardinal.Finite
public import CFSG.Assembly.QuasithinDefs
public import CFSG.Fischer.Uniq.CompTau
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBDerivedNormalSectionBound
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBHeldSmallCorePrimeCore
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalDescentEndpoint
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalFiveStructure
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalFixedTransfer
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalPointActionModels
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalPointPlusBorelModel
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalScalarSquareField
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalScalarSquareStructure
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalSixComponentsCover
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalSixModelGeometry
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalTraceZeroCoordinates
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBProjectiveInvolutionStructure
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBSymplecticBField
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBSymplecticBLinear
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueKProper
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueKProperGroups
public import CFSG.LocalAnalysis.ComponentClassification.DisjointSolvableKernels
public import CFSG.LocalAnalysis.ComponentClassification.LayerMultiplication
public import CFSG.LocalAnalysis.ComponentClassification.MinimalBCenter
public import CFSG.LocalAnalysis.ComponentClassification.OrdinaryComponentJoins
public import CFSG.LocalAnalysis.ComponentClassification.TwoLayer
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCatalogSpExclusion
public import CFSG.LocalAnalysis.ComponentClassification.UniversalOrbitBlock
public import CFSG.LocalAnalysis.ComponentInitial.OrthogonalFamilyLemmasFive
public import CFSG.LocalAnalysis.ComponentInitial.OrthogonalFamilyLemmasSix
public import CFSG.LocalAnalysis.ComponentInitial.OrthogonalReflectionSplitting
public import CFSG.LocalAnalysis.ComponentInitial.OrthogonalStandardFormsRegular
public import CFSG.LocalAnalysis.ZStar.BrauerSylowFusion
public import CFSG.LocalAnalysis.ZStar.PrincipalBlockTraceApplication
public import CFSG.Monster.Existence.Defs
public import CFSG.Open.MonsterY443Defs
public import CFSG.Quasithin.Background.Basic
public import CFSG.RankThree.Classical.SteinbergBJSymplecticSquareZeroCentralizer
public import CFSG.SignalizerFunctorTheorem.NonLocal.Cross
public import CFSG.SignalizerFunctorTheorem.NonLocal.SpData
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.External.Isaacs.VII.lemma_7_7
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.FiniteFieldFixedSubfieldCard
public import TauCeti.LinearAlgebra.Dimension.IsQuadraticExtension
public import TauCeti.LinearAlgebra.QuadraticForm.OrthogonalBasis
public import TauCeti.LinearAlgebra.QuadraticForm.OrthogonalGroup.LowRank

public section

namespace CFSG.RankThree.GF2n.Tim79a

open CFSG.Open

theorem statedSp_two_not_perfect {F : Type} [Field F] [Finite F] (hF : Nat.card F = 2) :
    commutator (StatedSp 2 F) ≠ ⊤ := by
  intro h
  have h1 : Nat.card (commutator (StatedSp 2 F)) = Nat.card (StatedSp 2 F) := by
    rw [h, Subgroup.card_top]
  have h2 : Nat.card (commutator (StatedSp 2 F)) = 360 := by
    rw [Nat.card_congr (CFSG.SignalizerFunctorTheorem.NonLocal.commutatorSpTwoEquiv hF).toEquiv,
      nat_card_alternatingGroup, Nat.card_fin]
    rfl
  have h3 : Nat.card (StatedSp 2 F) = 720 := by
    rw [Nat.card_congr (CFSG.SignalizerFunctorTheorem.NonLocal.spTwoTwoEquiv hF).toEquiv,
      CFSG.RankThree.PartOne.KCSpComm.card_sympFour]
  omega

theorem isSimpleGroup_statedSp_of_card_two {n : ℕ} (hn : 3 ≤ n) {F : Type} [Field F] [Finite F]
    (hF : Nat.card F = 2) : IsSimpleGroup (StatedSp n F) := by
  have hP : IsSimpleGroup (StatedProj (StatedSp n F)) :=
    CFSG.ClassicalGroups.Symplectic.isSimpleGroup_statedProj_statedSp F n (by omega)
      (Or.inr (Or.inr ⟨hF, hn⟩))
  exact MulEquiv.isSimpleGroup
    (CFSG.Monster.Existence.Compat.statedProjEquivOfBot (StatedSp n F)
      (CFSG.Monster.Existence.Compat.statedScalars_eq_bot hF)).symm

theorem commutator_statedSp_eq_top {n : ℕ} (hn : 3 ≤ n) {F : Type} [Field F] [Finite F]
    (hF : Nat.card F = 2) : commutator (StatedSp n F) = ⊤ :=
  (CFSG.ClassicalGroups.Symplectic.isPerfect_statedSp n F
    (Or.inr (Or.inr ⟨hF, hn⟩))).commutator_eq_top

theorem card_prod_le_of_pairing {W : Type*} [CommGroup W] [Finite W] {ι : Type*} [Fintype ι]
    [DecidableEq ι] (A : ι → Subgroup W) (σ : ι → ι) (hσ : ∀ i, σ (σ i) = i)
    (D : ι → W →* W) (hkill : ∀ i k, k ≠ σ i → ∀ a ∈ A k, D i a = 1)
    (hinj : ∀ i, ∀ a ∈ A (σ i), D i a = 1 → a = 1) :
    ∏ i, Nat.card (A i) ≤ Nat.card W := by
  let Φ : (∀ i, A i) →* W :=
    { toFun := fun a => ∏ i, (a i : W)
      map_one' := by simp
      map_mul' := fun a b => by simp [Finset.prod_mul_distrib] }
  have hΦ : Function.Injective Φ := by
    rw [injective_iff_map_eq_one]
    intro a ha
    funext i
    have hprod : ∏ k, (a k : W) = 1 := ha
    have hD : D (σ i) (∏ k, (a k : W)) = 1 := by rw [hprod, map_one]
    have hk : ∀ k ∈ (Finset.univ : Finset ι), k ≠ i → D (σ i) (a k : W) = 1 := by
      intro k _ hki
      exact hkill (σ i) k (by rw [hσ i]; exact hki) (a k : W) (a k).2
    rw [map_prod, Finset.prod_eq_single i hk (fun h => absurd (Finset.mem_univ i) h)] at hD
    have hai : (a i : W) = 1 := hinj (σ i) (a i : W) (by rw [hσ i]; exact (a i).2) hD
    exact Subtype.ext hai
  rw [← Nat.card_pi]
  exact Nat.card_le_card_of_injective Φ hΦ

theorem natCard_monoidHom_le_pow {E A : Type*} [CommGroup E] [Finite E] [CommGroup A] [Finite A]
    (hE : ∀ e : E, e * e = 1) {r : ℕ} (hr : Nat.card E = 2 ^ r) :
    Nat.card (E →* A) ≤ Nat.card A ^ r := by
  have h2 : ∀ x : Additive E, (2 : ℕ) • x = 0 := fun x => by
    rw [two_nsmul]
    exact hE (Additive.toMul x)
  letI : Module (ZMod 2) (Additive E) := AddCommGroup.zmodModule h2
  have h1 : Nat.card (Additive E) = 2 ^ Module.finrank (ZMod 2) (Additive E) := by
    rw [Module.natCard_eq_pow_finrank (K := ZMod 2), Nat.card_zmod]
  have hrank : Module.finrank (ZMod 2) (Additive E) = r := by
    have h3 : Nat.card (Additive E) = 2 ^ r := by
      rw [← Nat.card_congr (Additive.ofMul : E ≃ Additive E), hr]
    exact Nat.pow_right_injective (le_refl 2) (h1.symm.trans h3)
  let b : Module.Basis (Fin (Module.finrank (ZMod 2) (Additive E))) (ZMod 2) (Additive E) :=
    Module.finBasis (ZMod 2) (Additive E)
  let Φ : (E →* A) → (Fin (Module.finrank (ZMod 2) (Additive E)) → Additive A) :=
    fun f i => MonoidHom.toAdditive f (b i)
  have hΦ : Function.Injective Φ := by
    intro f g hfg
    refine MonoidHom.toAdditive.injective (AddMonoidHom.ext fun x => ?_)
    have key : ∀ (φ : Additive E →+ Additive A) (c : ZMod 2) (y : Additive E),
        φ (c • y) = c.val • φ y := by
      intro φ c y
      conv_lhs => rw [← ZMod.natCast_zmod_val c, Nat.cast_smul_eq_nsmul]
      exact map_nsmul φ _ _
    rw [← b.sum_repr x, map_sum, map_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    have hi : MonoidHom.toAdditive f (b i) = MonoidHom.toAdditive g (b i) := congrFun hfg i
    rw [key, key, hi]
  calc Nat.card (E →* A)
      ≤ Nat.card (Fin (Module.finrank (ZMod 2) (Additive E)) → Additive A) :=
        Nat.card_le_card_of_injective Φ hΦ
    _ = Nat.card A ^ r := by
        rw [Nat.card_fun, Nat.card_fin, ← Nat.card_congr (Additive.ofMul : A ≃ Additive A),
          hrank]

end CFSG.RankThree.GF2n.Tim79a
