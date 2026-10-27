module

public import CFSG.Timmesfeld.Orders.Bang
public import CFSG.Open.Defs
import CFSG.LocalAnalysis.SeitzReduction.F4PilotCatTypeDetOrders
import CFSG.LocalAnalysis.SeitzReduction.UnitaryPilotCatTypeDet
import CFSG.Assembly.OrderReductions.InvertedSubgroup
import CFSG.Assembly.OrderReductions.OddInversion
import CFSG.CharacterTheory.BrauerThirdMainTheorem.CentralResidueMaps
import CFSG.CharacterTheory.BrauerThirdMainTheorem.NormalizerClassLifting
import CFSG.CharacterTheory.BrauerThirdMainTheorem.PrincipalClassDefects
import CFSG.CharacterTheory.Semidihedral.Principal.DegreeZeroGram
import CFSG.CharacterTheory.TwoRankLowerBound.BrauerCharacterCriterion
import CFSG.LieType.Ree.LargeReeEightTorus
import CFSG.LinearAlgebra.LinearGroups.CoordinateData
import CFSG.LocalAnalysis.ComponentClassification.BlockCentralSylowEquality
import CFSG.LocalAnalysis.ComponentClassification.BlockFourFactorSupport
import CFSG.LocalAnalysis.ComponentClassification.BlockLargeProductInvolutions
import CFSG.LocalAnalysis.ComponentClassification.BlockMovedFactorSylowCentral
import CFSG.LocalAnalysis.ComponentClassification.BlockNormalizerOrder
import CFSG.LocalAnalysis.ComponentClassification.BlockPermutationSylowLifting
import CFSG.LocalAnalysis.ComponentClassification.BlockStrictFullSylowAbelian
import CFSG.LocalAnalysis.ComponentClassification.CatalogueBDerivedNormalSectionBound
import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalDescentEndpoint
import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalFiveStructure
import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalPointActionModels
import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalPointPlusBorelModel
import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalScalarSquareField
import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalScalarSquareStructure
import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalSixComponentsCover
import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalSixModelGeometry
import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalTraceZeroCoordinates
import CFSG.LocalAnalysis.ComponentClassification.CatalogueBProjectiveInvolutionStructure
import CFSG.LocalAnalysis.ComponentClassification.GrSLitHeMax
import CFSG.LocalAnalysis.ComponentClassification.KProper
import CFSG.LocalAnalysis.ComponentClassification.LabeledBlockPermutation
import CFSG.LocalAnalysis.ComponentClassification.OutcomeLocalOddCentralizer
import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCorrCriticalStandard
import CFSG.LocalAnalysis.ComponentInitial.OrthogonalFamilyLemmasFive
import CFSG.LocalAnalysis.ComponentInitial.OrthogonalFamilyLemmasSix
import CFSG.LocalAnalysis.ComponentInitial.OrthogonalReflectionSplitting
import CFSG.LocalAnalysis.ComponentInitial.OrthogonalStandardFormsRegular
import CFSG.LocalAnalysis.SectionRank.BruhatLift
import CFSG.LocalAnalysis.SectionRank.ClassicalOdd
import CFSG.LocalAnalysis.SectionRank.EvenCover.LinearStep
import CFSG.LocalAnalysis.SectionRank.LargeRee.SLTwo
import CFSG.LocalAnalysis.SectionRank.LargeReeCover
import CFSG.LocalAnalysis.SeitzReduction.F4PilotCatAlt
import CFSG.LocalAnalysis.SeitzReduction.UnitaryPilotCatAlt
import CFSG.Sporadic.Schreier.TitsOther
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
import TauCeti.LinearAlgebra.Dimension.IsQuadraticExtension
import TauCeti.LinearAlgebra.QuadraticForm.OrthogonalBasis

public section

namespace CFSG.StandardType.SCFourCover

open CFSG.Open CFSG.Timmesfeld CFSG.Timmesfeld.Orders

theorem exists_ppd_dvd_ordD_four {n κ : ℕ} (hn : 1 ≤ n) (hκ : κ = 3 ∨ κ = 4 ∨ κ = 6)
    (h6 : κ * n ≠ 6) : ∃ p, IsPrimitivePrimeDivisor p (κ * n) ∧ p ∣ ordD 4 (2 ^ n) := by
  obtain ⟨p, hp⟩ := exists_isPrimitivePrimeDivisor (k := κ * n)
    (by rcases hκ with rfl | rfl | rfl <;> omega) h6
  refine ⟨p, hp, ((CFSG.SeitzReduction.F4Pilot.profile_idxD (n := 4) (f := n) (by norm_num)
    hn).prim p (κ * n) hp (by rcases hκ with rfl | rfl | rfl <;> omega)).2 ?_⟩
  rcases hκ with rfl | rfl | rfl
  · exact Or.inr ⟨3, by simp, 2, by ring⟩
  · exact Or.inl ⟨1, by ring⟩
  · exact Or.inr ⟨3, by simp, 1, by ring⟩

theorem exists_ppd_dvd_ordA_two {m : ℕ} (hm : 1 ≤ m) (h2 : m ≠ 2) :
    ∃ p, IsPrimitivePrimeDivisor p (3 * m) ∧ p ∣ ordA 2 (2 ^ m) := by
  obtain ⟨p, hp⟩ := exists_isPrimitivePrimeDivisor (k := 3 * m) (by omega) (by omega)
  exact ⟨p, hp, ((CFSG.SeitzReduction.F4Pilot.profile_idxA (n := 2) (f := m) (by norm_num)
    hm).prim p (3 * m) hp (by omega)).2 ⟨3, by simp, 1, by ring⟩⟩

theorem exists_ppd_dvd_ordTwistedA_two {m : ℕ} (hm : 2 ≤ m) :
    ∃ p, IsPrimitivePrimeDivisor p (6 * m) ∧ p ∣ ordTwistedA 2 (2 ^ m) := by
  obtain ⟨p, hp⟩ := exists_isPrimitivePrimeDivisor (k := 6 * m) (by omega) (by omega)
  refine ⟨p, hp, ((CFSG.SeitzReduction.UnitaryPilot.profile_idxU (n := 2) (g := m) le_rfl
    (by omega)).prim p (6 * m) hp (by omega)).2
    ⟨3, by simp, Or.inr ⟨by decide, ⟨1, by ring⟩, fun h => ?_⟩⟩⟩
  have := Nat.le_of_dvd (by omega) h
  omega

theorem exists_ppd_dvd_ordA_two_nine {n : ℕ} (hn : 1 ≤ n) :
    ∃ p, IsPrimitivePrimeDivisor p (9 * n) ∧ p ∣ ordA 2 (2 ^ (3 * n)) := by
  obtain ⟨p, hp, hd⟩ := exists_ppd_dvd_ordA_two (m := 3 * n) (by omega) (by omega)
  exact ⟨p, by rwa [show 3 * (3 * n) = 9 * n by ring] at hp, hd⟩

theorem exists_ppd_dvd_ordTwistedA_two_eighteen {n : ℕ} (hn : 1 ≤ n) :
    ∃ p, IsPrimitivePrimeDivisor p (18 * n) ∧ p ∣ ordTwistedA 2 (2 ^ (3 * n)) := by
  obtain ⟨p, hp, hd⟩ := exists_ppd_dvd_ordTwistedA_two (m := 3 * n) (by omega)
  exact ⟨p, by rwa [show 6 * (3 * n) = 18 * n by ring] at hp, hd⟩

private theorem gcd_four_noJ1 {k : ℕ} (hk : 1 ≤ k) : Nat.gcd 4 ((2 ^ k) ^ 4 - 1) = 1 := by
  have h2 : 2 ∣ (2 ^ k) ^ 4 := dvd_pow (dvd_pow_self 2 (by omega)) (by norm_num)
  have h1 : 1 ≤ (2 ^ k) ^ 4 := Nat.one_le_pow _ _ (Nat.two_pow_pos k)
  exact Nat.Coprime.pow_left 2 (Nat.coprime_two_left.2 (Nat.odd_iff.2 (by omega)))

theorem ordD_four_two_pow_le {g n : ℕ} (hn : 1 ≤ n) (hgn : g ∣ n) :
    ordD 4 (2 ^ g) ≤ ordD 4 (2 ^ n) := by
  have hg : 1 ≤ g := Nat.pos_of_dvd_of_pos hgn hn
  have h : 2 ^ g ≤ 2 ^ n := Nat.pow_le_pow_right two_pos (Nat.le_of_dvd hn hgn)
  unfold ordD
  rw [gcd_four_noJ1 hg, gcd_four_noJ1 hn, Nat.div_one, Nat.div_one]
  exact Nat.mul_le_mul (Nat.mul_le_mul (Nat.pow_le_pow_left h _)
    (Nat.sub_le_sub_right (Nat.pow_le_pow_left h _) _))
    (Finset.prod_le_prod' fun i _ => Nat.sub_le_sub_right (Nat.pow_le_pow_left h _) _)

private theorem two_pow_mod_three_noJ1 {g : ℕ} (hg : Odd g) : 2 ^ g % 3 = 2 := by
  obtain ⟨k, rfl⟩ := hg
  rw [pow_succ, pow_mul, Nat.mul_mod, Nat.pow_mod]
  norm_num

private theorem gcd_three_sub_noJ1 {k : ℕ} (hk : Odd k) : Nat.gcd (2 + 1) (2 ^ k - 1) = 1 := by
  have h := two_pow_mod_three_noJ1 hk
  refine (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).2 ?_
  generalize 2 ^ k = x at h ⊢
  omega

private theorem gcd_three_add_noJ1 {k : ℕ} (hk : Odd k) : Nat.gcd (2 + 1) (2 ^ k + 1) = 3 := by
  have h := two_pow_mod_three_noJ1 hk
  refine Nat.gcd_eq_left ?_
  generalize 2 ^ k = x at h ⊢
  omega

private theorem toNat_factor_le_noJ1 {q q' : ℕ} (h : q ≤ q') (i : ℕ) :
    ((q : ℤ) ^ i - (-1) ^ i).toNat ≤ ((q' : ℤ) ^ i - (-1) ^ i).toNat := by
  have : (q : ℤ) ^ i ≤ (q' : ℤ) ^ i := pow_le_pow_left₀ (by positivity) (by exact_mod_cast h) i
  exact Int.toNat_le_toNat (by linarith)

theorem ordA_two_two_pow_le {g m : ℕ} (hg : Odd g) (hm : Odd m) (hgm : g ∣ m) :
    ordA 2 (2 ^ g) ≤ ordA 2 (2 ^ m) := by
  have h : 2 ^ g ≤ 2 ^ m := Nat.pow_le_pow_right two_pos (Nat.le_of_dvd hm.pos hgm)
  unfold ordA
  rw [gcd_three_sub_noJ1 hg, gcd_three_sub_noJ1 hm, Nat.div_one, Nat.div_one]
  exact Nat.mul_le_mul (Nat.pow_le_pow_left h _)
    (Finset.prod_le_prod' fun i _ => Nat.sub_le_sub_right (Nat.pow_le_pow_left h _) _)

theorem ordTwistedA_two_two_pow_le {g m : ℕ} (hg : Odd g) (hm : Odd m) (hgm : g ∣ m) :
    ordTwistedA 2 (2 ^ g) ≤ ordTwistedA 2 (2 ^ m) := by
  have h : 2 ^ g ≤ 2 ^ m := Nat.pow_le_pow_right two_pos (Nat.le_of_dvd hm.pos hgm)
  unfold ordTwistedA
  rw [gcd_three_add_noJ1 hg, gcd_three_add_noJ1 hm]
  exact Nat.div_le_div_right (Nat.mul_le_mul (Nat.pow_le_pow_left h _)
    (Finset.prod_le_prod' fun i _ => toNat_factor_le_noJ1 h i))

end CFSG.StandardType.SCFourCover

end
