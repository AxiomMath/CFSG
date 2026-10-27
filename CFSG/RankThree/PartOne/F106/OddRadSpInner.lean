module

public import CFSG.RankThree.PartOne.F106.OddRadAt
public import CFSG.RankThree.PartOne.KC.SymplecticIsotypicSpecial
public import CFSG.RankThree.PartOne.KC.PrimaryDecomposition
public import CFSG.RankThree.Classical.SteinbergBJSymplecticCrossPrimeBlocks
import CFSG.RankThree.PartOne.F106.OddRadTools
import CFSG.RankThree.PartOne.KC.SymplecticIsotypicBlocks
import CFSG.RankThree.PartOne.KC.SymplecticInnerPlaneCore
import CFSG.RankThree.PartOne.S11d.PSpGood
import CFSG.RankThree.GroupTheory.SubnormalCores
import CFSG.GroupTheory.LocalCores.Components
import CFSG.GroupTheory.ABGLocalTools.Constraint
import CFSG.GroupTheory.PerfectResidualNodes
public import CFSG.Assembly.QuasithinDefs
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueKProper
public import CFSG.LocalAnalysis.ComponentClassification.LBalanceComponentLifts
public import CFSG.LocalAnalysis.ComponentInitial.LayerComponentOrbit
public import CFSG.LocalAnalysis.SectionRank.Sporadic.TitsGen
public import CFSG.Perm.ChainSpec
public import CFSG.Quasithin.Background.Basic
public import CFSG.RankThree.GroupTheory.SteinbergBYSectionNineResidual
public import CFSG.RankThree.LocalRank.SelectorCases
public import CFSG.RankThree.PartOne.N143.Weyl613Defs
public import CFSG.RankThree.PartOne.N143X.KF64WSimple
public import Certificates.Certificate2267
public import Certificates.Certificate8033
import CFSG.LocalAnalysis.ComponentClassification.CatalogueBDerivedNormalSectionBound
import CFSG.LocalAnalysis.ComponentClassification.CatalogueBHeldSmallCorePrimeCore
import CFSG.LocalAnalysis.ComponentClassification.CatalogueBHigherLinearFieldDeterminant
import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalDescentEndpoint
import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalFiveStructure
import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalFixedTransfer
import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalPointActionModels
import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalPointPlusBorelModel
import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalScalarSquareField
import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalScalarSquareStructure
import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalSixComponentsCover
import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalSixModelGeometry
import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalTraceZeroCoordinates
import CFSG.LocalAnalysis.ComponentClassification.CatalogueBProjectiveInvolutionStructure
import CFSG.LocalAnalysis.ComponentClassification.CatalogueBSymplecticBField
import CFSG.LocalAnalysis.ComponentClassification.CatalogueBSymplecticBLinear
import CFSG.LocalAnalysis.ComponentClassification.CatalogueBSymplecticRepresentationOdd
import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCatalogSpExclusion
import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCatalogSpSuzukiCentralizer
import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCatalogSpWedge
import CFSG.LocalAnalysis.ComponentInitial.LinearInvolutionFixedField
import CFSG.LocalAnalysis.ComponentInitial.OrthogonalFamilyLemmasFive
import CFSG.LocalAnalysis.ComponentInitial.OrthogonalFamilyLemmasSix
import CFSG.LocalAnalysis.ComponentInitial.OrthogonalReflectionSplitting
import CFSG.LocalAnalysis.ComponentInitial.OrthogonalStandardFormsRegular
import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.X7bPairs
import CFSG.LocalAnalysis.SectionRank.Ccomm.Supercritical
import CFSG.RankThree.PartOne.S11d.OutClassicalTwo
import CFSG.RankThree.PartOne.S11d.OutSymplectic
import CFSG.RankThree.PartOne.S11d.OutUnitary
import CFSG.RankThree.PartOne.S11d.PSLDescent
import CFSG.RankThree.PartOne.S9.Sylow.ExclusionBasic
import CFSG.RankThree.Theta.ThreeComponentOrbitCover
import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.External.Huppert.IV.theorem_3_3
import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.FiniteFieldFixedSubfieldCard
import CFSG.Walter.Defs
import Certificates.Certificate1
import Certificates.Certificate2
import TauCeti.LinearAlgebra.Dimension.IsQuadraticExtension
import TauCeti.LinearAlgebra.QuadraticForm.OrthogonalBasis
import TauCeti.LinearAlgebra.QuadraticForm.OrthogonalGroup.LowRank

public section

namespace CFSG.RankThree.PartOne.F106.OddRadSp

open Polynomial CFSG.RankThree.PartOne.KCPrimary CFSG.RankThree.PartOne.KCUnitary
  CFSG.RankThree.PartOne.KCSpIsotypic CFSG.Assembly.LowTwoRank CFSG.RankThree.Classical
open CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag (proj)
open scoped commutatorElement

theorem mul_comm_of_mem_radical_of_component {G : Type*} [Group G] [Finite G] {J : Subgroup G}
    (hJ : IsComponent J) {y : G} (hy : y ∈ solvableRadical G) {j : G} (hj : j ∈ J) :
    j * y = y * j := by
  have hSn : (solvableRadical G).Normal := CFSG.ABGLocalTools.solvableRadical_normal
  have hSs : Group.IsSolvable ↥(solvableRadical G) :=
    CFSG.ABGLocalTools.solvableRadical_isSolvable
  have h1 : ⁅j, y⁆ ∈ ⁅J, solvableRadical G⁆ := Subgroup.commutator_mem_commutator hj hy
  rw [(CFSG.LocalCores.component_solvable_centralizer hSs hSn.isSubnormal).1 J hJ,
    Subgroup.mem_bot, commutatorElement_eq_one_iff_mul_comm] at h1
  exact h1

theorem exists_involution_radical_of_not_odd {G : Type*} [Group G] [Finite G]
    (h : ¬ Odd (Nat.card ↥(solvableRadical ↥(perfectResidual G)))) :
    ∃ y : G, y ∈ perfectResidual G ∧ y ∈ solvableRadical G ∧ y ^ 2 = 1 ∧ y ≠ 1 := by
  classical
  have h2 := even_iff_two_dvd.mp (Nat.not_odd_iff_even.mp h)
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨z, hz⟩ := exists_prime_orderOf_dvd_card' 2 h2
  have hsub : (perfectResidual G).IsSubnormal := Subgroup.Normal.isSubnormal inferInstance
  have h1 := (CFSG.RankThree.solvable_radical_subnormal_intersection hsub).1
  refine ⟨((z : ↥(perfectResidual G)) : G), (z : ↥(perfectResidual G)).2, ?_, ?_, ?_⟩
  · have : ((z : ↥(perfectResidual G)) : G) ∈ inSubgroup solvableRadical (perfectResidual G) :=
      ⟨z.1, z.2, rfl⟩
    rw [h1] at this
    exact this.2
  · have := pow_orderOf_eq_one z
    rw [hz] at this
    have h3 := congrArg (fun w : ↥(solvableRadical ↥(perfectResidual G)) =>
      ((w : ↥(perfectResidual G)) : G)) this
    simpa using h3
  · intro h1'
    have : z = 1 := by
      apply Subtype.ext
      apply Subtype.ext
      exact h1'
    rw [this, orderOf_one] at hz
    exact absurd hz (by norm_num)

section Blocks

variable {K : Type} [Field K] {f r : ℕ}

theorem charP_two_of_card_eq_two_pow [Finite K] (hK : Nat.card K = 2 ^ f) : CharP K 2 := by
  have := Fintype.ofFinite K
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  exact charP_of_card_eq_prime_pow (f := f) (by rw [Fintype.card_eq_nat_card, hK])

theorem blocks_of_orderOf_five [Finite K] (hK : Nat.card K = 2 ^ f) (hf : 1 ≤ f) (hr : 1 ≤ r)
    (x : StatedSp r K) (hx : orderOf x = 5) :
    ∃ _blocks : SpPrimaryBlocks 2 f 5 x (proj r K x), Squarefree (minpoly K (spEnd x)) := by
  have hchar : CharP K 2 := charP_two_of_card_eq_two_pow hK
  have hpK : ((5 : ℕ) : K) ≠ 0 := by
    have h2 : (2 : K) = 0 := CharTwo.two_eq_zero
    have h5 : ((5 : ℕ) : K) = 1 := by
      push_cast
      linear_combination (2 : K) * h2
    rw [h5]; exact one_ne_zero
  have ha : orderOf (proj r K x) = 5 := by
    rw [orderOf_injective (proj r K) (proj_injective_sp hK hf hr) x]
    exact hx
  obtain ⟨-, hblocks⟩ := symplectic_cross_prime_primary_centralizer_blocks (ℓ := 2) (f := f)
    (p := 5) Nat.prime_two hf hK (by norm_num) (by norm_num) (by norm_num) hr (proj r K x) ha
  have hx5 : x ^ 5 = 1 := by
    have := pow_orderOf_eq_one x
    rwa [hx] at this
  exact ⟨hblocks x rfl hx, (altPrimaryData_spLin hpK hx5).squarefree⟩

theorem involution_radical_trivial_on_block [Finite K] (hK : Nat.card K = 2 ^ f)
    {x : StatedSp r K} (hsq : Squarefree (minpoly K (spEnd x))) {h : primaryFactors (spEnd x)}
    (facts : SpBlockFacts (spForm r K) (spLin r K x) h)
    {y : ↥(Subgroup.centralizer ({x} : Set (StatedSp r K)))}
    (hy : y ∈ solvableRadical ↥(Subgroup.centralizer ({x} : Set (StatedSp r K))))
    (hy2 : y ^ 2 = 1) :
    ∀ v ∈ primaryComponent (spEnd x) (h : K[X]), spEnd (y : StatedSp r K) v = v := by
  classical
  have hfin : Finite (StatedSp r K) := inferInstance
  have hcomm : 2 ≤ primaryMultiplicity (spEnd x) (h : K[X]) →
      ∀ g ∈ spPull x (h : K[X]), g * (y : StatedSp r K) = (y : StatedSp r K) * g := by
    intro hm g hg
    have hJ : IsComponent ((spPull x (h : K[X])).subgroupOf
        (Subgroup.centralizer ({x} : Set (StatedSp r K)))) := by
      refine ⟨CFSG.LocalCores.isQuasisimple_of_mulEquiv
        (Subgroup.subgroupOfEquivOfLe (spPull_le_centralizer x _)).symm
        (spPull_isQuasisimple facts hm), ?_⟩
      have : ((spPull x (h : K[X])).subgroupOf
          (Subgroup.centralizer ({x} : Set (StatedSp r K)))).Normal :=
        ⟨fun n hn g => spPull_normalized x _ g g.2 n hn⟩
      exact this.isSubnormal
    have := mul_comm_of_mem_radical_of_component hJ hy
      (j := ⟨g, spPull_le_centralizer x _ hg⟩) hg
    exact congrArg
      (fun z : ↥(Subgroup.centralizer ({x} : Set (StatedSp r K))) => (z : StatedSp r K)) this
  have hYc : spLin r K (y : StatedSp r K) ∈ gl_centralizer (spLin r K x) := by
    rw [mem_gl_centralizer]
    exact spEnd_comm_iff.mp (Subgroup.mem_centralizer_singleton_iff.mp y.2)
  have hYcomm : 2 ≤ primaryMultiplicity (spEnd x) (h : K[X]) →
      ∀ g ∈ specialBlock (spForm r K) (spLin r K x) (h : K[X]),
        Commute (spLin r K (y : StatedSp r K)) g := by
    intro hm g hg
    have hgU : g ∈ unitaryCentralizer (spForm r K) (spLin r K x) :=
      specialBlock_le_unitaryCentralizer hg
    rw [unitaryCentralizer_spForm_eq_map] at hgU
    obtain ⟨g₀, -, rfl⟩ := hgU
    have hg₀ : g₀ ∈ spPull x (h : K[X]) := hg
    exact Commute.map (show Commute (y : StatedSp r K) g₀ from (hcomm hm g₀ hg₀).symm)
      (spLin r K)
  obtain ⟨c, hc⟩ := facts.scalar _ hYc hYcomm
  have hchar : CharP K 2 := charP_two_of_card_eq_two_pow hK
  have h2K : (2 : K) = 0 := CharTwo.two_eq_zero
  have hyy : ∀ v : Fin r ⊕ Fin r → K,
      spEnd (y : StatedSp r K) (spEnd (y : StatedSp r K) v) = v := by
    intro v
    have h2 : (y : StatedSp r K) ^ 2 = 1 := by
      have := congrArg
        (fun z : ↥(Subgroup.centralizer ({x} : Set (StatedSp r K))) => (z : StatedSp r K)) hy2
      simpa using this
    have h := congrArg (fun g : Module.End K (Fin r ⊕ Fin r → K) => g v) (spEnd_pow h2)
    simpa [pow_two, Module.End.mul_apply] using h
  intro v hv
  have : Fact (Irreducible (h : K[X])) := ⟨irreducible_of_mem_primaryFactors h.2⟩
  have hne := primaryComponent_ne_bot hsq h.2
  obtain ⟨w, hw0⟩ := (Submodule.ne_bot_iff _).mp hne
  obtain ⟨hwmem, hwne⟩ := hw0
  have hcc : c * c = 1 := by
    have h1 := hyy (w : Fin r ⊕ Fin r → K)
    have h2 := hc ⟨w, hwmem⟩
    have h3 := hc (c • ⟨w, hwmem⟩)
    change spEnd (y : StatedSp r K) w = ((c • (⟨w, hwmem⟩ : primaryComponent (spEnd x)
      (h : K[X])) : primaryComponent (spEnd x) (h : K[X])) : Fin r ⊕ Fin r → K) at h2
    rw [h2] at h1
    change spEnd (y : StatedSp r K) ((c • (⟨w, hwmem⟩ : primaryComponent (spEnd x)
      (h : K[X])) : primaryComponent (spEnd x) (h : K[X])) : Fin r ⊕ Fin r → K) = _ at h3
    have hw' : (⟨w, hwmem⟩ : primaryComponent (spEnd x) (h : K[X])) ≠ 0 := fun h0 =>
      hwne (congrArg Subtype.val h0)
    have h4 : c • c • (⟨w, hwmem⟩ : primaryComponent (spEnd x) (h : K[X])) = ⟨w, hwmem⟩ :=
      Subtype.ext (h3.symm.trans h1)
    rw [← mul_smul] at h4
    have h5 : (c * c) • (⟨w, hwmem⟩ : primaryComponent (spEnd x) (h : K[X])) =
        (1 : AdjoinRoot (h : K[X])) • ⟨w, hwmem⟩ := by rw [h4, one_smul]
    exact smul_left_injective _ hw' h5
  have h2E : (2 : AdjoinRoot (h : K[X])) = 0 := by
    rw [← map_ofNat (algebraMap K (AdjoinRoot (h : K[X]))) 2, h2K, map_zero]
  have hsq0 : (c - 1) * (c - 1) = 0 := by linear_combination hcc - (c - 1) * h2E
  have hc1 : c = 1 := sub_eq_zero.mp (mul_self_eq_zero.mp hsq0)
  have := hc ⟨v, hv⟩
  rw [hc1, one_smul] at this
  exact this

theorem eq_one_of_trivial_on_blocks {ℓ f' p : ℕ} {x : StatedSp r K}
    (blocks : SpPrimaryBlocks ℓ f' p x (proj r K x)) {y : StatedSp r K}
    (hid : ∀ h : primaryFactors (spEnd x), ∀ v ∈ primaryComponent (spEnd x) (h : K[X]),
      spEnd y v = v) : y = 1 := by
  classical
  have hall : ∀ v : Fin r ⊕ Fin r → K, spEnd y v = v := by
    intro v
    have hv : v ∈ ⨆ k : primaryFactors (spEnd x), primaryComponent (spEnd x) (k : K[X]) := by
      rw [blocks.isInternal.submodule_iSup_eq_top]
      trivial
    refine Submodule.iSup_induction (fun k : primaryFactors (spEnd x) =>
      primaryComponent (spEnd x) (k : K[X])) (motive := fun v => spEnd y v = v) hv ?_ ?_ ?_
    · intro k v hv
      exact hid k v hv
    · exact map_zero _
    · intro a b ha hb
      rw [map_add, ha, hb]
  apply spLin_injective
  refine Units.ext (LinearMap.ext fun v => ?_)
  rw [map_one]
  exact hall v

end Blocks

section Large

variable {K : Type} [Field K] [Finite K] {f r : ℕ}

theorem eq_one_of_mem_radical_centralizer_sp (hK : Nat.card K = 2 ^ f) (hf : 2 ≤ f) (hr : 1 ≤ r)
    (x : StatedSp r K) (hx : orderOf x = 5)
    {y : ↥(Subgroup.centralizer ({x} : Set (StatedSp r K)))}
    (hy : y ∈ solvableRadical ↥(Subgroup.centralizer ({x} : Set (StatedSp r K))))
    (hy2 : y ^ 2 = 1) : y = 1 := by
  obtain ⟨blocks, hsq⟩ := blocks_of_orderOf_five hK (by omega) hr x hx
  have hfacts : ∀ h : primaryFactors (spEnd x), SpBlockFacts (spForm r K) (spLin r K x) h :=
    spBlockFacts (by norm_num) (calc 3 < 2 ^ 2 := by norm_num
      _ ≤ 2 ^ f := Nat.pow_le_pow_right (by norm_num) hf) hK hsq blocks
  apply Subtype.ext
  exact eq_one_of_trivial_on_blocks blocks fun h v hv =>
    involution_radical_trivial_on_block hK hsq (hfacts h) hy hy2 v hv

theorem odd_card_radical_perfectResidual_centralizer_sp (hK : Nat.card K = 2 ^ f) (hf : 2 ≤ f)
    (hr : 1 ≤ r) (x : StatedSp r K) (hx : orderOf x = 5) :
    Odd (Nat.card ↥(solvableRadical ↥(perfectResidual
      ↥(Subgroup.centralizer ({x} : Set (StatedSp r K)))))) := by
  by_contra hodd
  obtain ⟨y, -, hy, hy2, hy1⟩ := exists_involution_radical_of_not_odd hodd
  exact hy1 (eq_one_of_mem_radical_centralizer_sp hK hf hr x hx hy hy2)

end Large

section Transport

variable {K : Type} [Field K] [Finite K] {f r : ℕ}

theorem oddRadConcl_conj_of_centralizer (hK : Nat.card K = 2 ^ f) (hf : 1 ≤ f) (hr : 1 ≤ r)
    (h : ∀ x : StatedSp r K, orderOf x = 5 →
      Odd (Nat.card ↥(solvableRadical ↥(perfectResidual
        ↥(Subgroup.centralizer ({x} : Set (StatedSp r K)))))))
    (a : StatedProj (StatedSp r K)) (ha : orderOf a = 5) :
    OddRadConcl (StatedProj (StatedSp r K)) (MulAut.conj a) := by
  obtain ⟨x, rfl⟩ := CFSG.LocalAnalysis.ComponentInitial.SymplecticHigher.proj_surjective
    (r := r) (K := K) a
  have hinj := proj_injective_sp hK hf hr
  have hx : orderOf x = 5 := by
    rw [← orderOf_injective (proj r K) hinj x]
    exact ha
  unfold OddRadConcl
  rw [eqLocus_conj_eq_centralizer]
  have h1 := card_radical_residual_of_embedding (proj r K) hinj x
  rw [MonoidHom.range_eq_top.2
    (CFSG.LocalAnalysis.ComponentInitial.SymplecticHigher.proj_surjective (r := r) (K := K)),
    top_inf_eq] at h1
  rw [← h1]
  exact h x hx

theorem oddRadConcl_conj_sp (hK : Nat.card K = 2 ^ f) (hf : 2 ≤ f) (hr : 1 ≤ r)
    (a : StatedProj (StatedSp r K)) (ha : orderOf a = 5) :
    OddRadConcl (StatedProj (StatedSp r K)) (MulAut.conj a) :=
  oddRadConcl_conj_of_centralizer hK (by omega) hr
    (fun x hx => odd_card_radical_perfectResidual_centralizer_sp hK hf hr x hx) a ha

end Transport

end CFSG.RankThree.PartOne.F106.OddRadSp
