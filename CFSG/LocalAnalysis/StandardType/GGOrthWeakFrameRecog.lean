module

public import CFSG.LieType.Universal.Catalog
public import CFSG.GroupTheory.WeirSylow.OrthogonalModels
public import CFSG.RankThree.Classical2.OrthogonalIsotropicUnipotent
import CFSG.ClassicalGroups.Orthogonal.Simple
import CFSG.ClassicalInvolution.SmallCases.UpgradeCoverClassical
import CFSG.LieType.Universal.SpinOmega.Kernel
import CFSG.RankThree.PartOne.S11d.OrthModels
public import CFSG.ClassicalInvolution.Orders.OrthogonalCount
public import CFSG.LieType.Universal.Spin.Roots
public import CFSG.LieType.Universal.Unitary
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBDerivedNormalSectionBound
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalPointActionModels
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalPointDataModelWitness
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalSemilinearDataCompatibility
public import CFSG.LocalAnalysis.ComponentInitial.OrthogonalReflectionSplitting
public import CFSG.LocalAnalysis.ComponentInitial.UnitaryHigherEvenOrthogonalModel
public import CFSG.LocalAnalysis.SectionRank.SignLines
public import TauCeti.LinearAlgebra.QuadraticForm.OrthogonalBasis
import CFSG.Assembly.QuasithinDefs
import CFSG.LieType.Universal.SpinOmega.Range
import CFSG.LocalAnalysis.ComponentClassification.CatalogueBHeldSmallCorePrimeCore
import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalDescentEndpoint
import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalFiveStructure
import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalFixedTransfer
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
import CFSG.RankThree.PartOne.KC.OrthogonalBinaryDickson
import CFSG.RankThree.PartOne.S11d.LieGoodConclusion
import CFSG.RankThree.PartOne.S11d.OutClassicalTwo
import CFSG.RankThree.PartOne.S11d.OutLinear
import CFSG.RankThree.PartOne.S11d.OutSymplectic
import CFSG.RankThree.PartOne.S11d.OutUnitary
import CFSG.RankThree.PartOne.S9.Sylow.ExclusionBasic
import CFSG.RankThree.Theta.ThreeComponentOrbitCover
import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.External.Huppert.IV.theorem_3_3
import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.FiniteFieldFixedSubfieldCard
import CFSG.Walter.Defs
import Certificates.Certificate1
import Certificates.Certificate119
import Certificates.Certificate122
import Certificates.Certificate2
import TauCeti.LinearAlgebra.CliffordAlgebra.Monomials
import TauCeti.LinearAlgebra.Dimension.IsQuadraticExtension

public section

namespace CFSG.StandardType

namespace OrthTorus

open CFSG.LieType.Universal
open CFSG.LieType.Universal.Spin
open CFSG.RankThree.Classical2 (orthDerived)

section SpinDerived

private noncomputable def spinDerivedHomPlus {K : Type} [Field K] {n : ℕ} (hn : 3 ≤ n) :
    spinGroup (quadPlus n K) →* ↥(orthDerived (quadPlus n K)) :=
  (spinAction (quadPlus n K)).codRestrict _ fun x => by
    show spinAction (quadPlus n K) x ∈
      ⁅TauCeti.QuadraticMap.orthogonalGroup (quadPlus n K),
        TauCeti.QuadraticMap.orthogonalGroup (quadPlus n K)⁆
    exact (range_spinAction_quadPlus_eq_commutator (K := K) (n := n) hn) ▸
      MonoidHom.mem_range.mpr ⟨x, rfl⟩

private theorem coe_spinDerivedHomPlus {K : Type} [Field K] {n : ℕ} (hn : 3 ≤ n)
    (x : spinGroup (quadPlus n K)) :
    ↑(spinDerivedHomPlus hn x) = spinAction (quadPlus n K) x :=
  rfl

private theorem spinDerivedHomPlus_ker {K : Type} [Field K] {n : ℕ} (hn : 3 ≤ n) :
    (spinDerivedHomPlus (K := K) hn).ker = (spinAction (quadPlus n K)).ker := by
  ext x
  rw [MonoidHom.mem_ker, MonoidHom.mem_ker, Subtype.ext_iff, coe_spinDerivedHomPlus,
    Subgroup.coe_one]

private theorem spinDerivedHomPlus_injective {K : Type} [Field K] {n : ℕ} (hn : 3 ≤ n)
    [Finite K] [CharP K 2] : Function.Injective (spinDerivedHomPlus (K := K) hn) := by
  rw [injective_iff_map_eq_one]
  intro x hx
  have hx' : x ∈ (spinAction (quadPlus n K)).ker := by
    rw [← spinDerivedHomPlus_ker hn]
    exact hx
  have hbot : (spinAction (quadPlus n K)).ker = ⊥ := by
    haveI := isCentral_cliffordAlgebra_quadPlus K n
    exact ker_spinAction_eq_bot_of_isCentral _ (CharP.cast_eq_zero K 2)
  rw [hbot, Subgroup.mem_bot] at hx'
  exact hx'

private theorem spinDerivedHomPlus_surjective {K : Type} [Field K] {n : ℕ} (hn : 3 ≤ n) :
    Function.Surjective (spinDerivedHomPlus (K := K) hn) := by
  intro y
  have hy : ((y : ↥(orthDerived (quadPlus n K))) : (Fin n ⊕ Fin n → K) ≃ₗ[K]
      (Fin n ⊕ Fin n → K)) ∈ (spinAction (quadPlus n K)).range := by
    rw [range_spinAction_quadPlus_eq_commutator (K := K) (n := n) hn]
    exact y.2
  obtain ⟨x, hx⟩ := hy
  exact ⟨x, Subtype.ext (by rw [coe_spinDerivedHomPlus]; exact hx)⟩

private noncomputable def spinDerivedEquivPlus {K : Type} [Field K] {n : ℕ} (hn : 3 ≤ n)
    [Finite K] [CharP K 2] :
    spinGroup (quadPlus n K) ≃* ↥(orthDerived (quadPlus n K)) where
  toFun := spinDerivedHomPlus hn
  invFun y := Classical.choose (spinDerivedHomPlus_surjective hn y)
  left_inv x :=
    spinDerivedHomPlus_injective hn (Classical.choose_spec (spinDerivedHomPlus_surjective hn _))
  right_inv y := Classical.choose_spec (spinDerivedHomPlus_surjective hn y)
  map_mul' := map_mul _

private noncomputable def spinDerivedHomMinus {K : Type} [Field K] {n : ℕ} {b c : K}
    (hn : 4 ≤ n) (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0) [Finite K] :
    spinGroup (quadMinus n K b c) →* ↥(orthDerived (quadMinus n K b c)) :=
  (spinAction (quadMinus n K b c)).codRestrict _ fun x => by
    show spinAction (quadMinus n K b c) x ∈
      ⁅TauCeti.QuadraticMap.orthogonalGroup (quadMinus n K b c),
        TauCeti.QuadraticMap.orthogonalGroup (quadMinus n K b c)⁆
    exact (range_spinAction_quadMinus_eq_commutator (K := K) (n := n) (b := b) (c := c) hn
      hirr) ▸ MonoidHom.mem_range.mpr ⟨x, rfl⟩

private theorem coe_spinDerivedHomMinus {K : Type} [Field K] {n : ℕ} {b c : K}
    (hn : 4 ≤ n) (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0) [Finite K]
    (x : spinGroup (quadMinus n K b c)) :
    ↑(spinDerivedHomMinus hn hirr x) = spinAction (quadMinus n K b c) x :=
  rfl

private theorem spinDerivedHomMinus_ker {K : Type} [Field K] {n : ℕ} {b c : K}
    (hn : 4 ≤ n) (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0) [Finite K] :
    (spinDerivedHomMinus (K := K) hn hirr).ker = (spinAction (quadMinus n K b c)).ker := by
  ext x
  rw [MonoidHom.mem_ker, MonoidHom.mem_ker, Subtype.ext_iff, coe_spinDerivedHomMinus,
    Subgroup.coe_one]

private theorem spinDerivedHomMinus_injective {K : Type} [Field K] {n : ℕ} {b c : K}
    (hn : 4 ≤ n) (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0) [Finite K] [CharP K 2] :
    Function.Injective (spinDerivedHomMinus (K := K) hn hirr) := by
  rw [injective_iff_map_eq_one]
  intro x hx
  have hx' : x ∈ (spinAction (quadMinus n K b c)).ker := by
    rw [← spinDerivedHomMinus_ker hn hirr]
    exact hx
  have hbot : (spinAction (quadMinus n K b c)).ker = ⊥ := by
    haveI := isCentral_cliffordAlgebra_quadMinus n b c hirr
    exact ker_spinAction_eq_bot_of_isCentral _ (CharP.cast_eq_zero K 2)
  rw [hbot, Subgroup.mem_bot] at hx'
  exact hx'

private theorem spinDerivedHomMinus_surjective {K : Type} [Field K] {n : ℕ} {b c : K}
    (hn : 4 ≤ n) (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0) [Finite K] :
    Function.Surjective (spinDerivedHomMinus (K := K) hn hirr) := by
  intro y
  have hy : ((y : ↥(orthDerived (quadMinus n K b c))) :
      (Fin (n - 1) ⊕ Fin (n - 1) ⊕ Fin 2 → K) ≃ₗ[K]
        (Fin (n - 1) ⊕ Fin (n - 1) ⊕ Fin 2 → K)) ∈
      (spinAction (quadMinus n K b c)).range := by
    rw [range_spinAction_quadMinus_eq_commutator (K := K) (n := n) (b := b) (c := c) hn hirr]
    exact y.2
  obtain ⟨x, hx⟩ := hy
  exact ⟨x, Subtype.ext (by rw [coe_spinDerivedHomMinus]; exact hx)⟩

private noncomputable def spinDerivedEquivMinus {K : Type} [Field K] {n : ℕ} {b c : K}
    (hn : 4 ≤ n) (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0) [Finite K] [CharP K 2] :
    spinGroup (quadMinus n K b c) ≃* ↥(orthDerived (quadMinus n K b c)) where
  toFun := spinDerivedHomMinus hn hirr
  invFun y := Classical.choose (spinDerivedHomMinus_surjective hn hirr y)
  left_inv x := spinDerivedHomMinus_injective hn hirr
    (Classical.choose_spec (spinDerivedHomMinus_surjective hn hirr _))
  right_inv y := Classical.choose_spec (spinDerivedHomMinus_surjective hn hirr y)
  map_mul' := map_mul _

end SpinDerived

private theorem nonempty_orthDerived_of_statedOmega {K L : Type} [Field K] [Field L]
    {ι : Type} [Fintype ι] [DecidableEq ι]
    {QK : (ι → K) → K} {QL : (ι → L) → L} (φ : K ≃+* L)
    (hQ : ∀ v : ι → K, QL (φ ∘ v) = φ (QK v))
    (Q : QuadraticForm K (ι → K)) (Q' : QuadraticForm L (ι → L))
    (hQK : ⇑Q = QK) (hQL : ⇑Q' = QL)
    (hE : ⁅TauCeti.QuadraticMap.orthogonalGroup Q,
      TauCeti.QuadraticMap.orthogonalGroup Q⁆ = CFSG.ClassicalGroups.Orthogonal.elementaryGroup Q)
    (hE' : ⁅TauCeti.QuadraticMap.orthogonalGroup Q',
      TauCeti.QuadraticMap.orthogonalGroup Q'⁆ =
        CFSG.ClassicalGroups.Orthogonal.elementaryGroup Q') :
    Nonempty (↥(orthDerived Q) ≃* ↥(orthDerived Q')) := by
  have hmap : (CFSG.Open.StatedOmega QK).map
      (CFSG.Adapters.RankTwoModelTransports.glCongr (ι := ι) φ).toMonoidHom =
      CFSG.Open.StatedOmega QL :=
    CFSG.ClassicalInvolution.Upgrade.map_statedOmega (ι := ι) (QK := QK) (QL := QL) φ hQ
  have hψ : ↥(CFSG.Open.StatedOmega QK) ≃* ↥(CFSG.Open.StatedOmega QL) :=
    ((CFSG.Open.StatedOmega QK).equivMapOfInjective
        (CFSG.Adapters.RankTwoModelTransports.glCongr (ι := ι) φ).toMonoidHom
        (CFSG.Adapters.RankTwoModelTransports.glCongr (ι := ι) φ).injective).trans
      (MulEquiv.subgroupCongr hmap)
  have hS : ↥(CFSG.Open.StatedOmega QK) ≃* ↥(orthDerived Q) :=
    (CFSG.ClassicalGroups.Orthogonal.statedOmegaEquiv hQK hE).trans
      (MulEquiv.subgroupCongr hE.symm)
  have hS' : ↥(CFSG.Open.StatedOmega QL) ≃* ↥(orthDerived Q') :=
    (CFSG.ClassicalGroups.Orthogonal.statedOmegaEquiv hQL hE').trans
      (MulEquiv.subgroupCongr hE'.symm)
  exact ⟨hS.symm.trans (hψ.trans hS')⟩

private theorem nonempty_orthDerived_quadPlus_ringEquiv {K L : Type} [Field K] [Field L]
    {n : ℕ} (hn : 3 ≤ n) (φ : K ≃+* L) :
    Nonempty (↥(orthDerived (quadPlus n K)) ≃* ↥(orthDerived (quadPlus n L))) :=
  nonempty_orthDerived_of_statedOmega (ι := Fin n ⊕ Fin n) φ
    (fun v => CFSG.ClassicalInvolution.Upgrade.statedQuadPlus_comp φ v)
    (quadPlus n K) (quadPlus n L) (coe_quadPlus n K) (coe_quadPlus n L)
    (CFSG.ClassicalGroups.Orthogonal.commutator_orthogonalGroup_quadPlus hn)
    (CFSG.ClassicalGroups.Orthogonal.commutator_orthogonalGroup_quadPlus hn)

private theorem nonempty_orthDerived_quadMinus_ringEquiv {K L : Type} [Field K] [Field L]
    [Finite K] [Finite L] {n : ℕ} (hn : 4 ≤ n) (φ : K ≃+* L) {b c : K}
    (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0)
    (hirr' : ∀ s : L, s ^ 2 + φ b * s + φ c ≠ 0) :
    Nonempty (↥(orthDerived (quadMinus n K b c)) ≃*
      ↥(orthDerived (quadMinus n L (φ b) (φ c)))) :=
  nonempty_orthDerived_of_statedOmega (ι := Fin (n - 1) ⊕ Fin (n - 1) ⊕ Fin 2) φ
    (fun v => CFSG.ClassicalInvolution.Upgrade.statedQuadMinus_comp φ rfl rfl v)
    (quadMinus n K b c) (quadMinus n L (φ b) (φ c))
    (coe_quadMinus n K b c) (coe_quadMinus n L (φ b) (φ c))
    (CFSG.ClassicalGroups.Orthogonal.commutator_orthogonalGroup_quadMinus hn hirr)
    (CFSG.ClassicalGroups.Orthogonal.commutator_orthogonalGroup_quadMinus hn hirr')

private theorem pos_of_card_eq_two_pow {F : Type} [Field F] [Finite F] {f : ℕ}
    (hcard : Nat.card F = 2 ^ f) : 0 < f := by
  rcases Nat.eq_zero_or_pos f with h | h
  · subst h
    rw [pow_zero] at hcard
    have h1 : 1 < Nat.card F := Finite.one_lt_card
    omega
  · exact h

private theorem irreducible_image {F L : Type} [Field F] [Field L] (e : F ≃+* L) {b c : F}
    (hirr : ∀ s : F, s ^ 2 + b * s + c ≠ 0) :
    ∀ s : L, s ^ 2 + e b * s + e c ≠ 0 := by
  intro s hs
  refine hirr (e.symm s) ?_
  have h := congrArg e.symm hs
  simpa using h

private theorem nonempty_orthDerived_quadMinus_coeffs {K : Type} [Field K] [Finite K] {n : ℕ}
    {b c b' c' : K} (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0)
    (hirr' : ∀ s : K, s ^ 2 + b' * s + c' ≠ 0) :
    Nonempty (↥(orthDerived (quadMinus n K b c)) ≃*
      ↥(orthDerived (quadMinus n K b' c'))) := by
  obtain ⟨g⟩ := CFSG.GroupTheory.WeirSylow.binForm_isometry
    (b := b) (c := c) (b' := b') (c' := c') hirr hirr'
  have hiso : Nonempty ((quadMinus n K b c).IsometryEquiv (quadMinus n K b' c')) :=
    ⟨(CFSG.GroupTheory.WeirSylow.quadMinusIsometry n b c).trans
      (((QuadraticMap.IsometryEquiv.refl _).prod g.symm).trans
        (CFSG.GroupTheory.WeirSylow.quadMinusIsometry n b' c').symm)⟩
  exact ⟨CFSG.RankThree.PartOne.orthDerivedEquiv hiso.some⟩


theorem nonempty_lieUniversal_plus_equiv_orthDerived {F : Type} [Field F] [Finite F] [CharP F 2]
    {V : Type} [AddCommGroup V] [Module F V] [FiniteDimensional F V] {Q : QuadraticForm F V}
    (hQ : (QuadraticMap.polarBilin Q).Nondegenerate) {r f : ℕ} (hr : 3 ≤ r)
    (hcard : Nat.card F = 2 ^ f) (hdim : Module.finrank F V = 2 * r)
    (hplus : CFSG.GroupTheory.WeirSylow.IsPlusType Q) :
    Nonempty ((lieUniversal .POmegaPlus r 2 f Nat.prime_two).K ≃* ↥(orthDerived Q)) := by
  classical
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hM : lieUniversal .POmegaPlus r 2 f Nat.prime_two =
      ⟨spinGroup (quadPlus r (GaloisField 2 f)),
        plusDatum r (GaloisField 2 f) hr⟩ := by
    simp only [lieUniversal, hr, ↓reduceDIte]
  rw [hM]
  change Nonempty (spinGroup (quadPlus r (GaloisField 2 f)) ≃* ↥(orthDerived Q))
  have hf : 0 < f := pos_of_card_eq_two_pow hcard
  let e : F ≃+* GaloisField 2 f :=
    CFSG.ClassicalModels.finiteFieldEquivGaloisField F 2 f hf hcard
  obtain ⟨isoP⟩ := CFSG.GroupTheory.WeirSylow.nonempty_isometry_quadPlus hQ hdim hplus
  obtain ⟨tr⟩ := nonempty_orthDerived_quadPlus_ringEquiv (K := F) (L := GaloisField 2 f) hr e
  exact ⟨(spinDerivedEquivPlus (K := GaloisField 2 f) hr).trans
    (tr.symm.trans (CFSG.RankThree.PartOne.orthDerivedEquiv isoP).symm)⟩

theorem nonempty_lieUniversal_minus_equiv_orthDerived {F : Type} [Field F] [Finite F] [CharP F 2]
    {V : Type} [AddCommGroup V] [Module F V] [FiniteDimensional F V] {Q : QuadraticForm F V}
    (hQ : (QuadraticMap.polarBilin Q).Nondegenerate) {r f : ℕ} (hr : 4 ≤ r)
    (hcard : Nat.card F = 2 ^ f) (hdim : Module.finrank F V = 2 * r)
    (hminus : ¬ CFSG.GroupTheory.WeirSylow.IsPlusType Q) :
    Nonempty ((lieUniversal .POmegaMinus r 2 f Nat.prime_two).K ≃* ↥(orthDerived Q)) := by
  classical
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hM : lieUniversal .POmegaMinus r 2 f Nat.prime_two =
      ⟨spinGroup (quadMinus r (GaloisField 2 f) (minusCoeffs 2 f).1 (minusCoeffs 2 f).2),
        Twisted.minusDatum r (minusCoeffs_irr 2 f)⟩ := by
    simp only [lieUniversal]
  rw [hM]
  change Nonempty (spinGroup (quadMinus r (GaloisField 2 f) (minusCoeffs 2 f).1
    (minusCoeffs 2 f).2) ≃* ↥(orthDerived Q))
  have hf : 0 < f := pos_of_card_eq_two_pow hcard
  let e : F ≃+* GaloisField 2 f :=
    CFSG.ClassicalModels.finiteFieldEquivGaloisField F 2 f hf hcard
  rcases CFSG.GroupTheory.WeirSylow.exists_isometry_quadPlus_or_quadMinus Q hQ (by omega) hdim with
    isoP | ⟨b, c, hirr, isoM⟩
  · obtain ⟨isoP⟩ := isoP
    exact absurd (CFSG.GroupTheory.WeirSylow.IsPlusType.of_isometryEquiv isoP.symm
      (CFSG.GroupTheory.WeirSylow.isPlusType_quadPlus F r)) hminus
  obtain ⟨isoM⟩ := isoM
  have hirrL := irreducible_image e hirr
  obtain ⟨tr⟩ := nonempty_orthDerived_quadMinus_ringEquiv (K := F) (L := GaloisField 2 f) hr e
    hirr hirrL
  obtain ⟨co⟩ := nonempty_orthDerived_quadMinus_coeffs (K := GaloisField 2 f) (n := r)
    (b := (minusCoeffs 2 f).1) (c := (minusCoeffs 2 f).2) (b' := e b) (c' := e c)
    (minusCoeffs_irr 2 f) hirrL
  exact ⟨(spinDerivedEquivMinus (K := GaloisField 2 f) hr (minusCoeffs_irr 2 f)).trans
    (co.trans (tr.symm.trans (CFSG.RankThree.PartOne.orthDerivedEquiv isoM).symm))⟩

end OrthTorus

end CFSG.StandardType

end
