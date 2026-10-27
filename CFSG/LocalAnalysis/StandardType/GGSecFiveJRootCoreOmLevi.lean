module

public import CFSG.HardMathSupport.Dickson.Sec6.I1431D4Aux.OrthL2.Levi
public import CFSG.RankThree.PartOne.KC.OrthogonalFixedDerived
import CFSG.HardMathSupport.Dickson.Sec6.I1431D4Aux.OrthL2.BlockLevi
public import CFSG.Assembly.QuasithinDefs
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBDerivedNormalSectionBound
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBHeldSmallCorePrimeCore
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalDescentEndpoint
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalFiveStructure
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalPointActionModels
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalPointPlusBorelModel
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalScalarSquareField
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalScalarSquareStructure
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalSixComponentsCover
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalSixStructure
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalTraceZeroCoordinates
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBProjectiveInvolutionStructure
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueKProper
public import CFSG.LocalAnalysis.ComponentClassification.DisjointSolvableKernels
public import CFSG.LocalAnalysis.ComponentClassification.LayerMultiplication
public import CFSG.LocalAnalysis.ComponentClassification.MinimalBCenter
public import CFSG.LocalAnalysis.ComponentClassification.OrdinaryComponentJoins
public import CFSG.LocalAnalysis.ComponentClassification.TwoLayer
public import CFSG.LocalAnalysis.ComponentClassification.UniversalOrbitBlock
public import CFSG.LocalAnalysis.ComponentInitial.LayerComponentOrbit
public import CFSG.LocalAnalysis.ComponentInitial.OrthogonalFamilyLemmasSix
public import CFSG.LocalAnalysis.ComponentInitial.OrthogonalReflectionSplitting
public import CFSG.LocalAnalysis.ComponentInitial.OrthogonalStandardFormsRegular
public import CFSG.LocalAnalysis.ComponentInitial.UnitaryHigherEvenOrthogonalModel
public import CFSG.LocalAnalysis.RankThreeEvenClassification.ComponentCore
public import CFSG.LocalAnalysis.SectionRank.Ccomm.Supercritical
public import CFSG.Quasithin.Background.Basic
public import CFSG.RankThree.GroupTheory.SteinbergBYSectionNineResidual
public import CFSG.RankThree.LocalRank.SelectorCases
public import CFSG.RankThree.PartOne.Assembly
public import CFSG.RankThree.PartOne.KC.OrthogonalD4WitnessEven
public import CFSG.RankThree.PartOne.KC.OrthogonalD4WitnessOdd
public import CFSG.RankThree.PartOne.KC.OrthogonalSubfieldCentralizer
public import CFSG.RankThree.PartOne.S11d.LieCentralizerBlock
public import CFSG.RankThree.PartOne.S11d.LieCentralizerOrth
public import CFSG.RankThree.PartOne.S9.Sylow.ExclusionBasic
public import CFSG.RankThree.SteinbergR3EOrthogonalCoprimeCyclic
public import CFSG.RankThree.Theta.ThreeComponentOrbitCover
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Defs
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.FiniteFieldFixedSubfieldCard
public import Certificates.Certificate116
public import Certificates.Certificate119
public import Certificates.Certificate122
public import Certificates.Certificate123
public import TauCeti.LinearAlgebra.Dimension.IsQuadraticExtension
public import TauCeti.LinearAlgebra.QuadraticForm.OrthogonalBasis
import CFSG.HardMathSupport.Dickson.Sec6.Up34Chev2Aux.OrthBlocksComp
import CFSG.HardMathSupport.Solomon.UniquenessMaximal.Inputs

public section

namespace CFSG.StandardType

open Polynomial Module CFSG.RankThree.PartOne.KCPrimary CFSG.RankThree.PartOne.KCOrthogonal
  CFSG.ClassicalGroups.Orthogonal CFSG.RankThree.Classical2 QuadraticMap
open CFSG.LocalAnalysis.ComponentInitial
open CFSG.ComponentClassification.CatalogueBOrthogonalFourSplit
open CFSG.HardMathSupport.Dickson.Sec6.I1431.OrthL2
open scoped MatrixGroups

theorem supportedFixedDerived_eq_levi_of_card_ne_three {K : Type} [Field K] [Finite K]
    {V : Type} [AddCommGroup V] [Module K V] [FiniteDimensional K V] {Q : QuadraticForm K V}
    {p : ℕ} {x : V ≃ₗ[K] V} (hx : OddOrderIsometry Q p x) (A B : HypPair Q) (hAB : A.Orth B)
    (hspan : Submodule.span K {A.e, A.f, B.e, B.f} = fixedSpace x) (hK : Nat.card K ≠ 2)
    (hK3 : Nat.card K ≠ 3) :
    supportedFixedDerived Q x = leviV Q A.e B.e A.f B.f ⊔ leviV Q A.e B.f A.f B.e := by
  classical
  let m : Matrix (Fin 2) (Fin 2) K →ₗ[K] V := matrixToOriginal A B
  have hinj : Function.Injective m := matrixToOriginal_injective A B hAB
  have hrange : LinearMap.range m = fixedSpace x := by
    rw [← hspan]
    apply le_antisymm
    · rintro _ ⟨X, rfl⟩
      rw [show m X = matrixToOriginal A B X from rfl, matrixToOriginal_apply]
      refine Submodule.sub_mem _ (Submodule.add_mem _ (Submodule.add_mem _ ?_ ?_) ?_) ?_ <;>
        exact Submodule.smul_mem _ _ (Submodule.subset_span (by simp))
    · rw [Submodule.span_le]
      intro v hv
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hv
      rcases hv with rfl | rfl | rfl | rfl
      · exact ⟨!![1, 0; 0, 0], by simp [m, matrixToOriginal_apply]⟩
      · exact ⟨!![0, 0; 0, 1], by simp [m, matrixToOriginal_apply]⟩
      · exact ⟨!![0, 1; 0, 0], by simp [m, matrixToOriginal_apply]⟩
      · exact ⟨!![0, 0; -1, 0], by simp [m, matrixToOriginal_apply]⟩
  let ePsi : Matrix (Fin 2) (Fin 2) K ≃ₗ[K] fixedSpace x :=
    (LinearEquiv.ofInjective m hinj).trans (LinearEquiv.ofEq _ _ hrange)
  have hePsi : ∀ X, ((ePsi X : fixedSpace x) : V) = m X := fun X => rfl
  let psi : (Q.comp (fixedSpace x).subtype).IsometryEquiv (determinantForm K) :=
    { toLinearEquiv := ePsi.symm
      map_app' := fun w => by
        obtain ⟨X, rfl⟩ := ePsi.surjective w
        show determinantForm K (ePsi.symm (ePsi X)) = Q ((ePsi X : fixedSpace x) : V)
        rw [LinearEquiv.symm_apply_apply, hePsi, determinantForm_apply]
        exact (matrixToOriginal_form A B hAB X).symm }
  let Θ := TauCeti.QuadraticMap.orthogonalGroupCongr psi
  let Φ : ↥(supportedBlock Q x (X - 1)) ≃* DeterminantIsometries K :=
    (fixedBlockEquiv hx).trans Θ
  have hΦ : ∀ (g : ↥(supportedBlock Q x (X - 1)))
      (T : Matrix (Fin 2) (Fin 2) K → Matrix (Fin 2) (Fin 2) K),
      (∀ X, g.1 (m X) = m (T X)) → ∀ X, (Φ g).val X = T X := by
    intro g T hT X
    have h1 : (Φ g).val X = ePsi.symm ((fixedBlockEquiv hx g).val (ePsi X)) :=
      TauCeti.QuadraticMap.coe_orthogonalGroupCongr_apply psi (fixedBlockEquiv hx g) X
    rw [h1]
    apply ePsi.injective
    rw [LinearEquiv.apply_symm_apply]
    refine Subtype.ext ?_
    rw [coe_fixedBlockEquiv, hePsi, hePsi]
    exact hT X
  have hsFD : ∀ g : V ≃ₗ[K] V, g ∈ supportedFixedDerived Q x ↔
      ∃ hg : g ∈ supportedBlock Q x (X - 1), Φ ⟨g, hg⟩ ∈ specialImage K := by
    intro g
    rw [mem_supportedFixedDerived]
    refine exists_congr fun hg => ?_
    have e1 : restrictFixed Q x ⟨g, hg⟩ =
        ((fixedBlockEquiv hx ⟨g, hg⟩ : ↥(TauCeti.QuadraticMap.orthogonalGroup
          (Q.comp (fixedSpace x).subtype))) : fixedSpace x ≃ₗ[K] fixedSpace x) := rfl
    rw [e1, orthDerived, ← Subgroup.map_subtype_commutator]
    have hmem : ∀ y : ↥(TauCeti.QuadraticMap.orthogonalGroup (Q.comp (fixedSpace x).subtype)),
        (y : fixedSpace x ≃ₗ[K] fixedSpace x) ∈
          (commutator ↥(TauCeti.QuadraticMap.orthogonalGroup (Q.comp (fixedSpace x).subtype))).map
            (TauCeti.QuadraticMap.orthogonalGroup (Q.comp (fixedSpace x).subtype)).subtype ↔
          y ∈ commutator ↥(TauCeti.QuadraticMap.orthogonalGroup
            (Q.comp (fixedSpace x).subtype)) := fun y =>
      Subgroup.mem_map_iff_mem (Subgroup.subtype_injective
        (TauCeti.QuadraticMap.orthogonalGroup (Q.comp (fixedSpace x).subtype)))
    refine (hmem _).trans ?_
    have hcomm : (commutator ↥(TauCeti.QuadraticMap.orthogonalGroup
        (Q.comp (fixedSpace x).subtype))).map Θ.toMonoidHom =
          commutator (DeterminantIsometries K) := by
      rw [commutator_def, Subgroup.map_commutator, Subgroup.map_top,
        MonoidHom.range_eq_top.mpr Θ.surjective, ← commutator_def]
    rw [← determinant_commutator_eq hK hK3, ← hcomm]
    exact (Subgroup.mem_map_iff_mem Θ.injective).symm
  have hAe : A.e ∈ fixedSpace x := hspan ▸ Submodule.subset_span (by simp)
  have hAf : A.f ∈ fixedSpace x := hspan ▸ Submodule.subset_span (by simp)
  have hBe : B.e ∈ fixedSpace x := hspan ▸ Submodule.subset_span (by simp)
  have hBf : B.f ∈ fixedSpace x := hspan ▸ Submodule.subset_span (by simp)
  have hm₁ : ∀ c : K, eichler Q A.e (c • B.f) ∈ supportedBlock Q x (X - 1) := fun c =>
    eichler_mem_supportedBlock_fixed hx hAe (Submodule.smul_mem _ c hBf)
  have hm₂ : ∀ c : K, eichler Q B.e (c • A.f) ∈ supportedBlock Q x (X - 1) := fun c =>
    eichler_mem_supportedBlock_fixed hx hBe (Submodule.smul_mem _ c hAf)
  have hm₃ : ∀ c : K, eichler Q A.e (c • B.e) ∈ supportedBlock Q x (X - 1) := fun c =>
    eichler_mem_supportedBlock_fixed hx hAe (Submodule.smul_mem _ c hBe)
  have hm₄ : ∀ c : K, eichler Q B.f (c • A.f) ∈ supportedBlock Q x (X - 1) := fun c =>
    eichler_mem_supportedBlock_fixed hx hBf (Submodule.smul_mem _ c hAf)
  have hΦ₁ : ∀ c : K, Φ ⟨eichler Q A.e (c • B.f), hm₁ c⟩ = specialRho (1, sl2Lower K c) := by
    intro c
    refine Subtype.ext (LinearEquiv.ext fun X => ?_)
    rw [hΦ _ (fun X => X * (sl2Lower K (-c) : Matrix (Fin 2) (Fin 2) K))
      (fun X => eichler_right_lower A B hAB X c), specialRho_apply]
    simp [sl2Lower_neg]
  have hΦ₂ : ∀ c : K, Φ ⟨eichler Q B.e (c • A.f), hm₂ c⟩ = specialRho (1, sl2Upper K c) := by
    intro c
    refine Subtype.ext (LinearEquiv.ext fun X => ?_)
    rw [hΦ _ (fun X => X * (sl2Upper K (-c) : Matrix (Fin 2) (Fin 2) K))
      (fun X => eichler_right_upper A B hAB X c), specialRho_apply]
    simp [sl2Upper_neg]
  have hΦ₃ : ∀ c : K, Φ ⟨eichler Q A.e (c • B.e), hm₃ c⟩ = specialRho (sl2Upper K c, 1) := by
    intro c
    refine Subtype.ext (LinearEquiv.ext fun X => ?_)
    rw [hΦ _ (fun X => (sl2Upper K c : Matrix (Fin 2) (Fin 2) K) * X)
      (fun X => eichler_left_upper A B hAB X c), specialRho_apply]
    simp
  have hΦ₄ : ∀ c : K, Φ ⟨eichler Q B.f (c • A.f), hm₄ c⟩ = specialRho (sl2Lower K c, 1) := by
    intro c
    refine Subtype.ext (LinearEquiv.ext fun X => ?_)
    rw [hΦ _ (fun X => (sl2Lower K c : Matrix (Fin 2) (Fin 2) K) * X)
      (fun X => eichler_left_lower A B hAB X c), specialRho_apply]
    simp
  have hgen : ∀ (g : V ≃ₗ[K] V) (hg : g ∈ supportedBlock Q x (X - 1)) (z : SL(2, K) × SL(2, K)),
      Φ ⟨g, hg⟩ = specialRho z → g ∈ supportedFixedDerived Q x := fun g hg z hz =>
    (hsFD g).mpr ⟨hg, by rw [hz]; exact ⟨z, rfl⟩⟩
  apply le_antisymm
  · intro g hg
    obtain ⟨hgF, hΦg⟩ := (hsFD g).mp hg
    set H : Subgroup (DeterminantIsometries K) := Subgroup.map Φ.toMonoidHom
      (Subgroup.comap (supportedBlock Q x (X - 1)).subtype
        (leviV Q A.e B.e A.f B.f ⊔ leviV Q A.e B.f A.f B.e))
    have hmemH : specialImage K ≤ H := by
      rw [← determinantFactors_sup]
      refine sup_le ?_ ?_
      · refine range_le_of_sl2_generators (specialRho.comp (MonoidHom.inl _ _)) H ?_ ?_
        · intro c
          exact ⟨⟨eichler Q A.e (c • B.e), hm₃ c⟩,
            Subgroup.mem_sup_right (Subgroup.subset_closure (Or.inl ⟨c, rfl⟩)), hΦ₃ c⟩
        · intro c
          exact ⟨⟨eichler Q B.f (c • A.f), hm₄ c⟩,
            Subgroup.mem_sup_right (Subgroup.subset_closure (Or.inr ⟨c, rfl⟩)), hΦ₄ c⟩
      · refine range_le_of_sl2_generators (specialRho.comp (MonoidHom.inr _ _)) H ?_ ?_
        · intro c
          exact ⟨⟨eichler Q B.e (c • A.f), hm₂ c⟩,
            Subgroup.mem_sup_left (Subgroup.subset_closure (Or.inr ⟨c, rfl⟩)), hΦ₂ c⟩
        · intro c
          exact ⟨⟨eichler Q A.e (c • B.f), hm₁ c⟩,
            Subgroup.mem_sup_left (Subgroup.subset_closure (Or.inl ⟨c, rfl⟩)), hΦ₁ c⟩
    obtain ⟨l, hl, hΦl⟩ := hmemH hΦg
    have hlg : l = ⟨g, hgF⟩ := Φ.injective hΦl
    rw [hlg] at hl
    exact hl
  · refine sup_le ?_ ?_
    · rw [leviV, Subgroup.closure_le]
      rintro _ (⟨c, rfl⟩ | ⟨c, rfl⟩)
      · exact hgen _ (hm₁ c) (1, sl2Lower K c) (hΦ₁ c)
      · exact hgen _ (hm₂ c) (1, sl2Upper K c) (hΦ₂ c)
    · rw [leviV, Subgroup.closure_le]
      rintro _ (⟨c, rfl⟩ | ⟨c, rfl⟩)
      · exact hgen _ (hm₃ c) (sl2Upper K c, 1) (hΦ₃ c)
      · exact hgen _ (hm₄ c) (sl2Lower K c, 1) (hΦ₄ c)

end CFSG.StandardType

end
