module

public import CFSG.Walter.W67.Section6.Core62J
public import CFSG.LocalAnalysis.RankTwoShapes.FixedPointFreeThree
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.External.Hall.Basic
public import CFSG.CharacterTheory.BrauerThirdMainTheorem.CentralResidueMaps
public import CFSG.CharacterTheory.BrauerThirdMainTheorem.NormalizerClassLifting
public import CFSG.CharacterTheory.BrauerThirdMainTheorem.PrincipalClassDefects
public import CFSG.CharacterTheory.Semidihedral.ElementStructure
public import CFSG.CharacterTheory.Semidihedral.Principal.DegreeZeroGram
public import CFSG.CharacterTheory.TwoRankLowerBound.BrauerCharacterCriterion
public import CFSG.LinearAlgebra.LinearGroups.LinearTwo
public import CFSG.LocalAnalysis.ComponentClassification.BlockTwoProductAction
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueSchreierLinearTwo
public import CFSG.LocalAnalysis.ComponentClassification.DisjointSolvableKernels
public import CFSG.LocalAnalysis.ComponentClassification.MinimalBCenter
public import CFSG.LocalAnalysis.ComponentClassification.NormalizedProductSylow
public import CFSG.LocalAnalysis.ComponentClassification.TwoActionFixedInvolution
public import CFSG.LocalAnalysis.ComponentClassification.TwoActionInvariantSylow
public import CFSG.LocalAnalysis.LargeEvenClassification.C8FourSubgroupExhaustion
public import CFSG.LocalAnalysis.LargeEvenClassification.C8FourSubgroupRanks
public import CFSG.LocalAnalysis.LargeEvenClassification.CyclicCongruenceCut
public import CFSG.LocalAnalysis.LargeEvenClassification.CyclicFourLarge
public import CFSG.LocalAnalysis.LargeEvenClassification.CyclicTwoFourGenerators
public import CFSG.LocalAnalysis.LargeEvenClassification.MacWilliamsReduction
public import CFSG.LocalAnalysis.LargeEvenClassification.SmallCfourFullObstruction
public import CFSG.LocalAnalysis.LargeEvenClassification.SmallCfourProperSubgroups
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.CentralInvolutionStructure
public import CFSG.LocalAnalysis.ZStar.BrauerSylowFusion
public import CFSG.LocalAnalysis.ZStar.PrincipalBlockTraceApplication
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFchapter1section1.proposition_4_c
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.SE.Proposition82
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.FiniteFieldPrimeOrderFixedSubfield
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.OrderThreeNormalizer
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.PGammaL2PSLRangeCentralizer
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section3.FirstCaseKleinInvolutionCount
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section3.FirstCaseKleinRestrictionSixCount
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section3.FirstCaseKleinUDecomposition
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section4.SecondCaseEquationEleven
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section4.SecondCaseEquationTen
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section4.SecondCaseEquationTenStructuralIdentities
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section4.SecondCasePSL2FieldProjectionArithmetic
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section4.SecondCasePSL2OrderPSubgroupCount
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Suzuki.OddGraphReconstruction
public import CFSG.Walter.Bender1970.S2
public import CFSG.Walter.Bender1970.S3.Basic
public import CFSG.Walter.Bender1970.S3.Tools
public import CFSG.Walter.PSL2Facts
public import CFSG.Walter.W67.Section6.Core62I
public import CFSG.Walter.W67.Section6.JRSylow
public import Certificates.Certificate1
public import Certificates.Certificate10
public import Certificates.Certificate100
public import Certificates.Certificate101
public import Certificates.Certificate102
public import Certificates.Certificate103
public import Certificates.Certificate104
public import Certificates.Certificate105
public import Certificates.Certificate106
public import Certificates.Certificate107
public import Certificates.Certificate108
public import Certificates.Certificate109
public import Certificates.Certificate11
public import Certificates.Certificate12
public import Certificates.Certificate2
public import Certificates.Certificate3
public import Certificates.Certificate4
public import Certificates.Certificate42
public import Certificates.Certificate44
public import Certificates.Certificate5
public import Certificates.Certificate6
public import Certificates.Certificate7
public import Certificates.Certificate8
public import Certificates.Certificate9
public import Certificates.Certificate96
public import Certificates.Certificate97
public import Certificates.Certificate98
public import Certificates.Certificate99

public section

namespace CFSG.Walter.W67.Sec65

variable {G : Type} [Group G] [Finite G]

open BenderSuzuki.External

open scoped commutatorElement

theorem conj_mem_of_relIndex_eq_seven {X M N : Subgroup G} (hMX : M ≤ X)
    (hXM : X ≤ Subgroup.normalizer (M : Set G)) (hNX : N ≤ Subgroup.normalizer (X : Set G))
    (hNM : N ≤ Subgroup.normalizer (M : Set G)) (hidx : M.relIndex X = 7)
    (hodd : Odd (Nat.card N))
    (h3 : ∀ t ∈ N, (∃ k : ℕ, t ^ 3 ^ k = 1) → ∀ x ∈ X, t * x * t⁻¹ * x⁻¹ ∈ M) :
    ∀ n ∈ N, ∀ x ∈ X, n * x * n⁻¹ * x⁻¹ ∈ M := by
  have : (M.subgroupOf X).Normal := (Subgroup.normal_subgroupOf_iff_le_normalizer hMX).mpr hXM
  have key : ∀ t : N, Sec6.quotAct hNX hNM t = 1 ↔
      ∀ x ∈ X, (t : G) * x * (t : G)⁻¹ * x⁻¹ ∈ M := by
    intro t
    refine ⟨fun h x hx => ?_, fun h => ?_⟩
    · have h' := DFunLike.congr_fun h ((⟨x, hx⟩ : X) : X ⧸ M.subgroupOf X)
      rw [Sec6.quotAct_mk, MulAut.one_apply, QuotientGroup.eq_iff_div_mem,
        Subgroup.mem_subgroupOf] at h'
      simpa [div_eq_mul_inv] using h'
    · refine MulEquiv.ext fun v => ?_
      induction v using QuotientGroup.induction_on with
      | H s =>
        rw [Sec6.quotAct_mk, MulAut.one_apply, QuotientGroup.eq_iff_div_mem,
          Subgroup.mem_subgroupOf]
        simpa [div_eq_mul_inv] using h s s.2
  have hcard : Nat.card (X ⧸ M.subgroupOf X) = 7 := hidx
  have : Fact (Nat.Prime 7) := ⟨by norm_num⟩
  have : IsCyclic (X ⧸ M.subgroupOf X) := isCyclic_of_prime_card hcard
  have hAut : Nat.card (MulAut (X ⧸ M.subgroupOf X)) = 6 := by
    rw [IsCyclic.card_mulAut, hcard, Nat.totient_prime (by norm_num)]
  have hg : Nat.gcd 6 (Nat.card N) ∣ 3 := by
    have h := Nat.Coprime.gcd_mul_left_cancel 3 (Nat.coprime_two_left.mpr hodd)
    rw [show (2 : ℕ) * 3 = 6 by norm_num] at h
    rw [h]
    exact Nat.gcd_dvd_left 3 _
  intro n hn x hx
  obtain ⟨a, m, hm3, hnm⟩ := Nat.exists_eq_pow_mul_and_not_dvd (orderOf_pos n).ne' 3 (by norm_num)
  have hcop : Nat.Coprime (Nat.gcd 6 (Nat.card N)) m :=
    Nat.Coprime.coprime_dvd_left hg ((Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mpr hm3)
  have h6 : Sec6.quotAct hNX hNM ⟨n, hn⟩ ^ 6 = 1 := by
    rw [← hAut]
    exact pow_card_eq_one'
  have hN : Sec6.quotAct hNX hNM ⟨n, hn⟩ ^ Nat.card N = 1 := by
    rw [← map_pow, pow_card_eq_one', map_one]
  have hm : Sec6.quotAct hNX hNM ⟨n, hn⟩ ^ m = 1 := by
    rw [← map_pow, key]
    have := h3 (n ^ m) (N.pow_mem hn m) ⟨a, by rw [← pow_mul, mul_comm m, ← hnm,
      pow_orderOf_eq_one]⟩
    simpa using this
  have h1 : Sec6.quotAct hNX hNM ⟨n, hn⟩ = 1 :=
    (pow_eq_one_iff_of_coprime hcop).mp ⟨pow_gcd_eq_one.mpr ⟨h6, hN⟩, hm⟩
  exact (key ⟨n, hn⟩).mp h1 x hx

theorem lowerCentralSeries_two_eq_bot_of_fpf {M : Subgroup G} {ρ : G}
    (hρM : ρ ∈ Subgroup.normalizer (M : Set G)) (hρ3 : ρ ^ 3 = 1)
    (hfpf : M ⊓ Subgroup.centralizer ({ρ} : Set G) = ⊥) : M.lowerCentralSeries 2 = ⊥ := by
  have hα3 : Sec6.conjAut hρM ^ 3 = 1 := by
    refine MulEquiv.ext fun s => Subtype.ext ?_
    rw [Sec6.conjAut_pow_apply, hρ3, MulAut.one_apply]
    group
  have hαfpf : ∀ x : M, Sec6.conjAut hρM x = x → x = 1 := by
    intro x hx
    have hx' : ρ * x * ρ⁻¹ = x := congrArg Subtype.val hx
    have hmem : (x : G) ∈ M ⊓ Subgroup.centralizer ({ρ} : Set G) := by
      refine Subgroup.mem_inf.mpr ⟨x.2, Subgroup.mem_centralizer_singleton_iff.mpr ?_⟩
      rw [mul_inv_eq_iff_eq_mul] at hx'
      exact hx'.symm
    rw [hfpf, Subgroup.mem_bot] at hmem
    exact Subtype.ext hmem
  have hcen := (CFSG.RankTwoShapes.fixedPointFree_three_class_two _ hα3 hαfpf).1
  have h2 : (⊤ : Subgroup M).lowerCentralSeries 2 = ⊥ := by
    rw [Subgroup.lowerCentralSeries_succ, Subgroup.lowerCentralSeries_succ,
      Subgroup.lowerCentralSeries_zero, Subgroup.commutator_eq_bot_iff_le_centralizer]
    exact hcen.trans (Subgroup.center_le_centralizer _)
  rw [← Subgroup.top_subtype_lowerCentralSeries, h2, Subgroup.map_bot]

theorem engelSymbol_eq_one_of_lowerCentralSeries {H : Type*} [Group H] {S : Subgroup H}
    {c n : ℕ} (hS : S.lowerCentralSeries c = ⊥) (hcn : c + 1 ≤ n) :
    ∀ u z : H, u ∈ S → z ∈ S → BenderSuzuki.External.engelSymbol n u z = 1 := by
  intro u z hu hz
  have key : ∀ k, iteratedInverseFirstCommutator k u z ∈ S.lowerCentralSeries k := by
    intro k
    induction k with
    | zero => exact hu
    | succ k ih =>
      have e : iteratedInverseFirstCommutator (k + 1) u z =
          ⁅(iteratedInverseFirstCommutator k u z)⁻¹, z⁻¹⁆ := by
        simp [iteratedInverseFirstCommutator, inverseFirstCommutator, commutatorElement_def]
      rw [e, Subgroup.lowerCentralSeries_succ]
      exact Subgroup.commutator_mem_commutator (Subgroup.inv_mem _ ih) (Subgroup.inv_mem _ hz)
  have hle : S.lowerCentralSeries (n - 1) ≤ S.lowerCentralSeries c :=
    S.lowerCentralSeries_antitone (by omega)
  rw [hS] at hle
  exact Subgroup.mem_bot.mp (hle (key (n - 1)))

end CFSG.Walter.W67.Sec65
