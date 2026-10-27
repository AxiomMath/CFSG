module

public import CFSG.LocalAnalysis.StandardType.FF81.CatQ1.Defs
public import CFSG.LocalAnalysis.StandardType.FF81.CatQ1.ClassicalTorus
public import CFSG.LocalAnalysis.StandardType.FF81.CatQ1.ClassicalTorusU
public import CFSG.LocalAnalysis.StandardType.FF81.CatQ1.ClassicalCellSixU
public import CFSG.LocalAnalysis.StandardType.FF81.CatQ1.ClassicalSubfieldU
import CFSG.LocalAnalysis.ComponentInitial.UnitaryHigherIsotropicRadical
import CFSG.HardMathSupport.Lang.Coordinator.OuterFixedOrderPSU
import CFSG.Assembly.OrderReductions.InvertedSubgroup
import CFSG.Assembly.OrderReductions.OddInversion
import CFSG.CharacterTheory.BrauerThirdMainTheorem.CentralResidueMaps
import CFSG.CharacterTheory.BrauerThirdMainTheorem.NormalizerClassLifting
import CFSG.CharacterTheory.BrauerThirdMainTheorem.PrincipalClassDefects
import CFSG.CharacterTheory.Semidihedral.Principal.DegreeZeroGram
import CFSG.CharacterTheory.TwoRankLowerBound.BrauerCharacterCriterion
import CFSG.LieType.Ree.SuzukiSimple
import CFSG.LieType.Universal.SpinOmega.Range
import CFSG.LinearAlgebra.LinearGroups.CoordinateData
import CFSG.LocalAnalysis.ComponentClassification.BlockCentralSylowEquality
import CFSG.LocalAnalysis.ComponentClassification.BlockFourFactorSupport
import CFSG.LocalAnalysis.ComponentClassification.BlockLargeProductInvolutions
import CFSG.LocalAnalysis.ComponentClassification.BlockMovedFactorSylowCentral
import CFSG.LocalAnalysis.ComponentClassification.BlockNormalizerOrder
import CFSG.LocalAnalysis.ComponentClassification.BlockPermutationSylowLifting
import CFSG.LocalAnalysis.ComponentClassification.BlockStrictFullSylowAbelian
import CFSG.LocalAnalysis.ComponentClassification.GrSLitHeMax
import CFSG.LocalAnalysis.ComponentClassification.KProper
import CFSG.LocalAnalysis.ComponentClassification.LabeledBlockPermutation
import CFSG.LocalAnalysis.ComponentClassification.OutcomeLocalOddCentralizer
import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCatalogG2EvenCanonicalField
import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCorrCriticalStandard
import CFSG.LocalAnalysis.RankThreeEvenClassification.ComponentCore
import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFchapter1section1.proposition_4_c
import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.SE.Proposition82
import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.FiniteFieldPrimeOrderFixedSubfield
import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.OrderThreeNormalizer
import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.PGammaL2PSLRangeCentralizer
import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section3.FirstCaseKleinInvolutionCount
import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section3.FirstCaseKleinRestrictionSixCount
import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section3.FirstCaseKleinUDecomposition
import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section4.SecondCaseEquationEleven
import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section4.SecondCaseEquationTen
import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section4.SecondCaseEquationTenStructuralIdentities
import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section4.SecondCasePSL2FieldProjectionArithmetic
import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section4.SecondCasePSL2OrderPSubgroupCount
import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Suzuki.OddGraphReconstruction
import Certificates.Certificate1
import Certificates.Certificate10
import Certificates.Certificate11
import Certificates.Certificate12
import Certificates.Certificate2
import Certificates.Certificate3
import Certificates.Certificate4
import Certificates.Certificate42
import Certificates.Certificate44
import Certificates.Certificate5
import Certificates.Certificate6
import Certificates.Certificate7
import Certificates.Certificate8
import Certificates.Certificate9

public section

namespace CFSG.StandardType.FF81.CatQ1

open Matrix CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher

private theorem cq1_ne_three_of_dvd_pow_add_one {ℓ f : ℕ} (hℓf : 1 ≤ f)
    (h : 3 ∣ ℓ ^ f + 1) : ℓ ≠ 3 := by
  intro hℓ3
  rw [hℓ3] at h
  have h3pow : 3 ∣ 3 ^ f := dvd_pow_self 3 (by omega)
  have h1 : 3 ∣ (3 ^ f + 1) - 3 ^ f := Nat.dvd_sub h h3pow
  have h1' : (3 ^ f + 1) - 3 ^ f = 1 := by omega
  rw [h1'] at h1
  obtain ⟨k, hk⟩ := h1
  omega

theorem exists_scalar_of_primeFormConjHom_pow_three {ℓ f n : ℕ} {F : Type} [Field F]
    (h : UnitaryFieldData ℓ f F) (hn : 3 ≤ n)
    {A : primeFormUnitary h ((1 : GL (Fin n) F) : Matrix (Fin n) (Fin n) F)}
    (hA : primeFormConjHom h ((1 : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) A ^ 3 = 1) :
    ∃ c : F, c ≠ 0 ∧ h.bar c * c = 1 ∧
      ((A : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) ^ 3 =
        c • (1 : Matrix (Fin n) (Fin n) F) := by
  have hA3 : primeFormConjHom h ((1 : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) (A ^ 3) = 1 := by
    rw [map_pow, hA]
  obtain ⟨c, hcn, hcA⟩ :=
    eq_scalar_of_primeFormConjHom_eq_one h isPrimeFormGram_one hn hA3
  have hnorm : (c : F) * h.bar (c : F) = 1 := hcn
  have hcne : (c : F) ≠ 0 := by
    intro hc0
    rw [hc0, zero_mul] at hnorm
    exact zero_ne_one hnorm
  refine ⟨(c : F), hcne, ?_, ?_⟩
  · rw [mul_comm, hnorm]
  · have hcAg : ((A : GL (Fin n) F)) ^ 3 = GeneralLinearGroup.scalar (Fin n) c := by
      rw [← Subgroup.coe_pow]
      exact hcA
    calc ((A : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) ^ 3
        = (((A : GL (Fin n) F)) ^ 3 : GL (Fin n) F) :=
          (Units.val_pow_eq_pow_val (A : GL (Fin n) F) 3).symm
      _ = (GeneralLinearGroup.scalar (Fin n) c : Matrix (Fin n) (Fin n) F) := by rw [hcAg]
      _ = (c : F) • (1 : Matrix (Fin n) (Fin n) F) := by
          rw [GeneralLinearGroup.coe_scalar, Matrix.scalar_apply, Matrix.smul_one_eq_diagonal]

theorem fixedTooBig_primeFormP_of_mem_D {ℓ f n : ℕ} {F : Type} [Field F] [Finite F]
    (h : UnitaryFieldData ℓ f F) (hn : 3 ≤ n) (hne : ¬(n = 3 ∧ ℓ ^ f = 2))
    (h4 : 4 ≤ CFSG.Open.pRank 3 (⊤ : Subgroup (primeFormP h
      ((1 : GL (Fin n) F) : Matrix (Fin n) (Fin n) F))))
    {β : MulAut (primeFormP h ((1 : GL (Fin n) F) : Matrix (Fin n) (Fin n) F))} (hβ : β ^ 3 = 1)
    (hD : β ∈ primeFormD h ((1 : GL (Fin n) F) : Matrix (Fin n) (Fin n) F))
    (hout : ∀ k, β ≠ MulAut.conj k) : FixedTooBig β := by
  rw [primeFormD, MonoidHom.mem_range] at hD
  obtain ⟨A, rfl⟩ := hD
  obtain ⟨c, hcne, hnorm, hAc⟩ := exists_scalar_of_primeFormConjHom_pow_three h hn hβ
  by_cases hg : 3 ∣ Nat.gcd n (ℓ ^ f + 1)
  · have h3q : 3 ∣ ℓ ^ f + 1 := dvd_trans hg (Nat.gcd_dvd_right n (ℓ ^ f + 1))
    have h3n : 3 ∣ n := dvd_trans hg (Nat.gcd_dvd_left n (ℓ ^ f + 1))
    have hℓ : ℓ ≠ 3 := cq1_ne_three_of_dvd_pow_add_one h.one_le h3q
    have hn6 : 6 ≤ n := by
      obtain ⟨k, hk⟩ := h3n
      by_contra hlt
      have hn3 : n = 3 := by omega
      rw [hn3] at h4
      have hle := pRank_primeFormP_three_le_two h hℓ
      omega
    by_cases hcube : ∃ b : F, b ^ 3 = c
    · obtain ⟨b, hb3⟩ := hcube
      have hb0 : b ≠ 0 := by
        intro hb0
        apply hcne
        rw [← hb3, hb0]
        exact zero_pow (by norm_num : 3 ≠ 0)
      have hA' : ((A : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) ^ 3 =
          (b ^ 3) • (1 : Matrix (Fin n) (Fin n) F) := by rw [hAc, hb3]
      obtain ⟨T, hT, hfix⟩ :=
        exists_torus_fixed_of_cube_unitary h (by omega) h3q hb0 hA'
      exact fixedTooBig_of_torus T hT hfix
    · have hc : ∀ x : F, x ^ 3 ≠ c := fun x hx => hcube ⟨x, hx⟩
      obtain ⟨x, hx9, hxfix⟩ := exists_order_nine_fixed_of_unitary_nonCube h hn6 hAc hc
      exact Or.inr (Or.inr ⟨x, hxfix, hx9⟩)
  · have hmem : primeFormConjHom h ((1 : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) A ∈
        primeFormD h ((1 : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) := by
      rw [primeFormD]
      exact MonoidHom.mem_range.mpr ⟨A, rfl⟩
    have hinner := CFSG.HardMathSupport.Lang.Coordinator.mem_inner_of_mem_primeFormD h hn hne
      (p := 3) (by norm_num) hg hmem hβ
    obtain ⟨k, hk⟩ := MonoidHom.mem_range.mp hinner
    exact absurd hk.symm (hout k)

open CFSG.Open CFSG.LocalAnalysis.ComponentInitial Matrix
  CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher in
theorem outerThreeBig_primeFormP {ℓ f : ℕ} {F : Type} [Field F] [Finite F]
    (h : UnitaryFieldData ℓ f F) {n : ℕ} (hn : 3 ≤ n) (hne : ¬(n = 3 ∧ ℓ ^ f = 2)) :
    OuterThreeBig (primeFormP h ((1 : GL (Fin n) F) : Matrix (Fin n) (Fin n) F)) := by
  intro h4 β hβ hout
  by_cases hσ : primeFormFieldFactor h isPrimeFormGram_one hn hne β = 1
  · have hD : β ∈ primeFormD h ((1 : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) := by
      rw [← ker_primeFormFieldFactor h isPrimeFormGram_one hn hne]
      exact hσ
    exact fixedTooBig_primeFormP_of_mem_D h hn hne h4 hβ hD hout
  · obtain ⟨e, F₀, _, _, h₀, ι, hf, hinj, hfix⟩ :=
      exists_subfield_embedding_fixed_primeFormP h hn hne hβ hσ
    exact fixedTooBig_of_embedding ι hinj hfix
      (twentySeven_dvd_card_primeFormP_of_cube h h₀ hn hf h4)

end CFSG.StandardType.FF81.CatQ1
