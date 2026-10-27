module

public import CFSG.LocalAnalysis.StandardType.GGQTwoDUnitBigS1
import CFSG.RankThree.PartOne.S11d.OrthCaseH
import CFSG.RankThree.Classical.SteinbergBJOrthogonalHighWitt
import CFSG.Assembly.QuasithinDefs
import CFSG.LocalAnalysis.ComponentClassification.CatalogueBHeldSmallCorePrimeCore
import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalDescentEndpoint
import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalFiveStructure
import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalPointPlusBorelModel
import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalScalarSquareField
import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalScalarSquareStructure
import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalSixComponentsCover
import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalSixStructure
import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalTraceZeroCoordinates
import CFSG.LocalAnalysis.ComponentClassification.CatalogueBProjectiveInvolutionStructure
import CFSG.LocalAnalysis.ComponentClassification.CatalogueBSymplecticBField
import CFSG.LocalAnalysis.ComponentClassification.CatalogueBSymplecticBLinear
import CFSG.LocalAnalysis.ComponentClassification.CatalogueBSymplecticRepresentationOdd
import CFSG.LocalAnalysis.ComponentClassification.CatalogueKProper
import CFSG.LocalAnalysis.ComponentClassification.DisjointSolvableKernels
import CFSG.LocalAnalysis.ComponentClassification.LayerMultiplication
import CFSG.LocalAnalysis.ComponentClassification.MinimalBCenter
import CFSG.LocalAnalysis.ComponentClassification.OrdinaryComponentJoins
import CFSG.LocalAnalysis.ComponentClassification.TwoLayer
import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCatalogSpExclusion
import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCatalogSpSuzukiCentralizer
import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCatalogSpWedge
import CFSG.LocalAnalysis.ComponentClassification.UniversalOrbitBlock
import CFSG.LocalAnalysis.ComponentInitial.LayerComponentOrbit
import CFSG.LocalAnalysis.ComponentInitial.LinearInvolutionFixedField
import CFSG.LocalAnalysis.ComponentInitial.OrthogonalFamilyLemmasSix
import CFSG.LocalAnalysis.ComponentInitial.OrthogonalStandardFormsRegular
import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.X7bPairs
import CFSG.LocalAnalysis.RankThreeEvenClassification.ComponentCore
import CFSG.LocalAnalysis.SectionRank.Ccomm.Supercritical
import CFSG.Quasithin.Background.Basic
import CFSG.RankThree.GroupTheory.SteinbergBYSectionNineResidual
import CFSG.RankThree.LocalRank.SelectorCases
import CFSG.RankThree.PartOne.KC.OrthogonalD4WitnessEven
import CFSG.RankThree.PartOne.KC.OrthogonalD4WitnessOdd
import CFSG.RankThree.PartOne.KC.OrthogonalSubfieldCentralizer
import CFSG.RankThree.PartOne.S11d.OutClassicalTwo
import CFSG.RankThree.PartOne.S11d.OutLinear
import CFSG.RankThree.PartOne.S11d.OutSymplectic
import CFSG.RankThree.PartOne.S11d.OutUnitary
import CFSG.RankThree.PartOne.S9.Sylow.ExclusionBasic
import CFSG.RankThree.SteinbergR3EOrthogonalCoprimeCyclic
import CFSG.RankThree.Theta.ThreeComponentOrbitCover
import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.External.Huppert.IV.theorem_3_3
import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.FiniteFieldFixedSubfieldCard
import CFSG.Walter.Defs
import Certificates.Certificate1
import Certificates.Certificate116
import Certificates.Certificate119
import Certificates.Certificate122
import Certificates.Certificate123
import Certificates.Certificate2
import TauCeti.LinearAlgebra.Dimension.IsQuadraticExtension

public section

namespace CFSG.StandardType.QTwo

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

open CFSG.Open CFSG.RankThree.Classical

theorem qtwoDB44_Omega_le_orthogonalGroup {n : ℕ}
    (Q : QuadraticForm (ZMod 2) (Fin n ⊕ Fin n → ZMod 2)) :
    qtwoDB44_Omega Q ≤ TauCeti.QuadraticMap.orthogonalGroup Q := by
  show ⁅TauCeti.QuadraticMap.orthogonalGroup Q, TauCeti.QuadraticMap.orthogonalGroup Q⁆ ≤ _
  refine Subgroup.commutator_le.mpr fun g₁ hg₁ g₂ hg₂ => ?_
  rw [commutatorElement_def]
  exact Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.mul_mem _ hg₁ hg₂)
    (Subgroup.inv_mem _ hg₁)) (Subgroup.inv_mem _ hg₂)

theorem qtwoDB44_mem_Omega_of_pow_three {d : ℕ} (hd : 4 ≤ d)
    {Q : QuadraticForm (ZMod 2) (Fin d ⊕ Fin d → ZMod 2)}
    (hQ : ∀ x y, QuadraticMap.polar Q x y = spForm d (ZMod 2) x y)
    {y : StatedSp d (ZMod 2)} (hy : ∀ x, Q (spEnd y x) = Q x) (h3 : y ^ 3 = 1) :
    qtwoDB44_linEquiv d y ∈ qtwoDB44_Omega Q := by
  have hdim : Module.finrank (ZMod 2) (Fin d ⊕ Fin d → ZMod 2) = 2 * d := by
    simp [Module.finrank_fintype_fun_eq_card, two_mul]
  have hQnd : (QuadraticMap.polarBilin Q).Nondegenerate := by
    have h : QuadraticMap.polarBilin Q = spForm d (ZMod 2) :=
      LinearMap.ext₂ fun x y => hQ x y
    rw [h]
    exact spForm_nondegenerate
  have hT := CFSG.RankThree.PartOne.exists_threeSingular_of_dim (K := ZMod 2) Q hQnd hd hdim
  obtain ⟨-, -, -, -, -, -, hodd, -⟩ :=
    CFSG.RankThree.Classical.orthogonal_high_Witt_derived_quotient_and_odd_lifts hQnd hT
  have hmem := (qtwoDB44_linEquiv_mem_orthogonalGroup Q y).mpr hy
  refine hodd _ hmem ?_
  have h3' : (qtwoDB44_linEquiv d y) ^ 3 = 1 := by rw [← map_pow, h3, map_one]
  rcases (Nat.dvd_prime Nat.prime_three).mp (orderOf_dvd_of_pow_eq_one h3') with h | h <;>
    rw [h] <;> decide

theorem qtwoDB44_embedding {G : Type} [Group G] {N : Subgroup G} {d : ℕ}
    (eN : ↥N ≃* StatedSp d (ZMod 2)) {Q : QuadraticForm (ZMod 2) (Fin d ⊕ Fin d → ZMod 2)}
    (hQ : ∀ x y, QuadraticMap.polar Q x y = spForm d (ZMod 2) x y) :
    ∃ ψ : ↥(qtwoDB44_Omega Q) →* G, Function.Injective ψ ∧
      ∀ (y : StatedSp d (ZMod 2)) (h : qtwoDB44_linEquiv d y ∈ qtwoDB44_Omega Q),
        ψ ⟨qtwoDB44_linEquiv d y, h⟩ = ((eN.symm y : ↥N) : G) := by
  classical
  have hO : qtwoDB44_Omega Q ≤ (qtwoDB44_linEquiv d).range :=
    (qtwoDB44_Omega_le_orthogonalGroup Q).trans (qtwoDB44_orthogonalGroup_le_range hQ)
  let linEq : StatedSp d (ZMod 2) ≃* ↥(qtwoDB44_linEquiv d).range :=
    MonoidHom.ofInjective (qtwoDB44_linEquiv_injective d)
  refine ⟨N.subtype.comp (eN.symm.toMonoidHom.comp
    (linEq.symm.toMonoidHom.comp (Subgroup.inclusion hO))), ?_, ?_⟩
  · intro a b hab
    exact Subgroup.inclusion_injective hO (linEq.symm.injective (eN.symm.injective
      (Subtype.val_injective hab)))
  · intro y h
    have hy : linEq.symm (Subgroup.inclusion hO ⟨qtwoDB44_linEquiv d y, h⟩) = y := by
      rw [MulEquiv.symm_apply_eq]
      exact Subtype.ext rfl
    show ((eN.symm (linEq.symm (Subgroup.inclusion hO ⟨qtwoDB44_linEquiv d y, h⟩)) : ↥N) : G) =
      ((eN.symm y : ↥N) : G)
    rw [hy]

theorem qtwoDB44_subgroup_le_range {G : Type} [Group G] {N : Subgroup G} {d : ℕ}
    (eN : ↥N ≃* StatedSp d (ZMod 2)) {Q : QuadraticForm (ZMod 2) (Fin d ⊕ Fin d → ZMod 2)}
    (ψ : ↥(qtwoDB44_Omega Q) →* G)
    (hψ : ∀ (y : StatedSp d (ZMod 2)) (h : qtwoDB44_linEquiv d y ∈ qtwoDB44_Omega Q),
      ψ ⟨qtwoDB44_linEquiv d y, h⟩ = ((eN.symm y : ↥N) : G))
    {J : Subgroup G} (hJN : J ≤ N) (hperf : J ≤ ⁅J, J⁆)
    (hQJ : ∀ n : ↥N, (n : G) ∈ J → ∀ x, Q (spEnd (eN n) x) = Q x) :
    J ≤ ψ.range := by
  classical
  intro g hg
  let n : ↥N := ⟨g, hJN hg⟩
  let J' : Subgroup ↥N := J.subgroupOf N
  have hJ'N : J'.map N.subtype = J := Subgroup.map_subgroupOf_eq_of_le hJN
  have hJ'perf : J' ≤ ⁅J', J'⁆ := by
    intro a ha
    have h1 : (a : G) ∈ ⁅J, J⁆ := hperf ha
    rw [← hJ'N, ← Subgroup.map_commutator] at h1
    obtain ⟨b, hb, hba⟩ := h1
    have : b = a := Subtype.ext hba
    rwa [this] at hb
  have hJ'le : ⁅J', J'⁆ ≤ J' := by
    refine Subgroup.commutator_le.mpr fun g₁ hg₁ g₂ hg₂ => ?_
    rw [commutatorElement_def]
    exact J'.mul_mem (J'.mul_mem (J'.mul_mem hg₁ hg₂) (J'.inv_mem hg₁)) (J'.inv_mem hg₂)
  let H : Subgroup (StatedSp d (ZMod 2)) := J'.map eN.toMonoidHom
  have hHperf : ⁅H, H⁆ = H := by
    rw [← Subgroup.map_commutator]
    exact congrArg (Subgroup.map eN.toMonoidHom) (le_antisymm hJ'le hJ'perf)
  have hH : ∀ y ∈ H, ∀ x, Q (spEnd y x) = Q x := by
    rintro _ ⟨n', hn', rfl⟩ x
    exact hQJ n' hn' x
  have hmem := qtwoDB44_perfect_le_orthDerived hHperf hH (eN n) ⟨n, hg, rfl⟩
  refine ⟨⟨qtwoDB44_linEquiv d (eN n), hmem⟩, ?_⟩
  rw [hψ (eN n) hmem]
  simp [n]

end CFSG.StandardType.QTwo

end
