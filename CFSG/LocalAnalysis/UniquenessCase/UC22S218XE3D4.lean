module

public import CFSG.LocalAnalysis.UniquenessCase.UC22S218D4
public import CFSG.RankThree.PartTwo.Sec11.KS11Lie4ProofD4
import CFSG.LocalAnalysis.ComponentInitial.RootDiagonalConjugation
import CFSG.CGT.PushingUpLit.CGT6K1.InnerEven
import CFSG.CharacterTheory.BrauerThirdMainTheorem.CentralResidueMaps
import CFSG.CharacterTheory.BrauerThirdMainTheorem.NormalizerClassLifting
import CFSG.CharacterTheory.BrauerThirdMainTheorem.PrincipalClassDefects
import CFSG.CharacterTheory.Semidihedral.Principal.DegreeZeroGram
import CFSG.CharacterTheory.TwoRankLowerBound.BrauerCharacterCriterion
import CFSG.LieType.Ree.LargeReeEightTorus
import CFSG.LieType.Ree.LargeReeInvolutionTwoCentralizers
import CFSG.LocalAnalysis.ComponentClassification.BlockCentralSylowEquality
import CFSG.LocalAnalysis.ComponentClassification.BlockFourFactorSupport
import CFSG.LocalAnalysis.ComponentClassification.BlockLargeProductInvolutions
import CFSG.LocalAnalysis.ComponentClassification.BlockMovedFactorSylowCentral
import CFSG.LocalAnalysis.ComponentClassification.BlockNormalizerOrder
import CFSG.LocalAnalysis.ComponentClassification.BlockPermutationSylowLifting
import CFSG.LocalAnalysis.ComponentClassification.BlockStrictFullSylowAbelian
import CFSG.LocalAnalysis.ComponentClassification.CatLeafOddB
import CFSG.LocalAnalysis.ComponentClassification.GrSLitHeMax
import CFSG.LocalAnalysis.ComponentClassification.KProper
import CFSG.LocalAnalysis.ComponentClassification.LabeledBlockPermutation
import CFSG.LocalAnalysis.ComponentClassification.OutcomeLocalOddCentralizer
import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCorrCriticalStandard
import CFSG.LocalAnalysis.ComponentInitial.UnitaryHigherEvenOrthogonalModel
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

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

open CFSG.Open Subgroup
open CFSG.Blueprint.Chevalley (TwistTag ModGL xUnit yUnit)
open CFSG.LieType.Chevalley
open CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley (rootDiagUnit root_diagonal_conjugation)
open CFSG.RankThree.PartTwo.Sec11.KS11Lie4Proof


theorem uc22s218_d4_shortSL2_le_centralizer {K : Type} [Field K] (σ : K ≃+* K)
    (l : Fin TwistTag.D4.tag.rank → Kˣ)
    (hl : ∀ j ∈ TwistTag.D4.orbit d4Outer, l j = 1) :
    (d4ShortSL2 K σ.toRingHom).map
      (graphFixedRootGroup TwistTag.D4 K σ.toRingHom).subtype ≤
        centralizer {rootDiagUnit TwistTag.D4.tag l} := by
  have hroot : ∀ j ∈ TwistTag.D4.orbit d4Outer, ∀ c : K,
      xUnit TwistTag.D4.tag K j c ∈ centralizer {rootDiagUnit TwistTag.D4.tag l} ∧
        yUnit TwistTag.D4.tag K j c ∈ centralizer {rootDiagUnit TwistTag.D4.tag l} := by
    intro j hj c
    obtain ⟨hx, hy, -⟩ := root_diagonal_conjugation TwistTag.D4.tag K l
    have hx' := hx j c
    have hy' := hy j c
    rw [hl j hj, Units.val_one, one_mul] at hx'
    rw [hl j hj, inv_one, Units.val_one, one_mul] at hy'
    constructor <;> rw [mem_centralizer_iff] <;> rintro _ rfl
    · exact mul_inv_eq_iff_eq_mul.1 hx'
    · exact mul_inv_eq_iff_eq_mul.1 hy'
  have hgen : (orbitRankOneHom TwistTag.D4 K σ.toRingHom d4Outer).range ≤
      centralizer {rootDiagUnit TwistTag.D4.tag l} := by
    rw [orbitRankOneHom_range, Subgroup.closure_le]
    rintro _ (⟨c, rfl⟩ | ⟨c, rfl⟩)
    · dsimp only
      rw [coe_orbitX]
      apply Subgroup.list_prod_mem
      intro z hz
      obtain ⟨k, _, rfl⟩ := List.mem_map.1 hz
      exact (hroot _ (TwistTag.D4.perm_pow_mem_orbit (TwistTag.D4.orbitMin_mem d4Outer) k) _).1
    · dsimp only
      rw [coe_orbitY]
      apply Subgroup.list_prod_mem
      intro z hz
      obtain ⟨k, _, rfl⟩ := List.mem_map.1 hz
      exact (hroot _ (TwistTag.D4.perm_pow_mem_orbit (TwistTag.D4.orbitMin_mem d4Outer) k) _).2
  rintro _ ⟨z, hz, rfl⟩
  exact hgen (show (z : ModGL TwistTag.D4.tag K) ∈
    (orbitRankOneHom TwistTag.D4 K σ.toRingHom d4Outer).range from hz)

theorem uc22s218_d4_fixed_torus_centralizes_shortSL2 {K : Type} [Field K]
    (σ : K ≃+* K) (t : (trialityFixedField K σ.toRingHom)ˣ) :
    (d4ShortSL2 K σ.toRingHom).map
      (graphFixedRootGroup TwistTag.D4 K σ.toRingHom).subtype ≤
        centralizer {trialityTorusHom σ (trialityFixedUnit K σ t, t ^ 2)} := by
  have hσu : Units.map σ.toRingHom.toMonoidHom (trialityFixedUnit K σ t) =
      trialityFixedUnit K σ t := Units.ext (sigma_trialityFixedUnit t)
  rw [trialityTorusHom_apply, trialityOuter_mul_middle_eq, map_pow]
  simp only [hσu]
  apply uc22s218_d4_shortSL2_le_centralizer
  intro j hj
  have hj' : j = ⟨0, by decide⟩ ∨ j = ⟨1, by decide⟩ ∨ j = ⟨3, by decide⟩ := by
    have hset : TwistTag.D4.orbit d4Outer =
        {⟨0, by decide⟩, ⟨1, by decide⟩, ⟨3, by decide⟩} := by decide
    rwa [hset, Finset.mem_insert, Finset.mem_insert, Finset.mem_singleton] at hj
  rcases hj' with rfl | rfl | rfl <;> change _ = 1
  · exact mul_inv_cancel _
  · exact mul_inv_cancel _
  · exact mul_inv_cancel _


theorem uc22s218_d4_exists_levi_torus {K : Type} [Field K] [Finite K] [CharP K 2]
    (σ : K ≃+* K) (hσ3 : σ ^ 3 = 1) {n p : ℕ} (hn : 1 ≤ n)
    (hK : Nat.card K = (2 ^ n) ^ 3) (hk : Nat.card (trialityFixedField K σ.toRingHom) = 2 ^ n)
    (hpq : p ∣ 2 ^ (6 * n) - 1) {s r : ℕ} (_hs : Odd s) (hsn : s ∣ n)
    (hr : r.Prime) (hrs : r ∣ 2 ^ s - 1) :
    ∃ x ∈ (graphFixedRootTorus TwistTag.D4 K σ.toRingHom).subgroupOf
        (graphFixedRootGroup TwistTag.D4 K σ.toRingHom), orderOf x = r ∧
      ∃ S : Subgroup ↥(graphFixedRootGroup TwistTag.D4 K σ.toRingHom), S ≤ centralizer {x} ∧
        IsL2 ↥S (3 * n) ∧ p ∣ Nat.card S := by
  have : Finite (ModGL TwistTag.D4.tag K) := finite_modGL
  have : Fact r.Prime := ⟨hr⟩
  obtain ⟨t, ht⟩ := exists_prime_orderOf_dvd_card' (G := (trialityFixedField K σ.toRingHom)ˣ) r
    (by rw [Nat.card_units, hk]; exact hrs.trans (Nat.pow_sub_one_dvd_pow_sub_one 2 hsn))
  let φ := (trialityTorusHom σ).codRestrict
    (graphFixedRootGroup TwistTag.D4 K σ.toRingHom)
      (trialityTorusHom_mem_graphFixedRootGroup hσ3)
  have hφ : Function.Injective φ := fun u v h =>
    trialityTorusHom_injective_all hσ3 (congrArg Subtype.val h)
  let x := φ (trialityFixedUnit K σ t, t ^ 2)
  refine ⟨x, Subgroup.mem_subgroupOf.2 ⟨trialityTorusHom_mem_graphFixedTorus hσ3 _, x.2⟩,
    ?_, d4ShortSL2 K σ.toRingHom, ?_, ?_, ?_⟩
  · have htK : orderOf (trialityFixedUnit K σ t) = orderOf t :=
      orderOf_injective (trialityFixedUnit K σ)
        (Units.map_injective (trialityFixedField K σ.toRingHom).subtype_injective) t
    rw [orderOf_injective φ hφ, Prod.orderOf, htK,
      Nat.lcm_eq_left (orderOf_pow_dvd (x := t) 2), ht]
  · intro z hz
    have hC := uc22s218_d4_fixed_torus_centralizes_shortSL2 σ t
      (Subgroup.mem_map_of_mem _ hz)
    rw [mem_centralizer_iff] at hC ⊢
    rintro _ rfl
    exact Subtype.ext (hC _ rfl)
  · obtain ⟨e⟩ := nonempty_mulEquiv_d4ShortSL2 hσ3
    let := Fintype.ofFinite (orbitField TwistTag.D4 K σ.toRingHom d4Outer)
    exact CFSG.CGT.PushingUpLit.CGT6K1.lieModel_PSL_two_of_mulEquiv_SL_two (by omega)
      (by rw [← Nat.card_eq_fintype_card, natCard_orbitField_d4Outer hσ3, hK,
        ← pow_mul, mul_comm]) e.symm
  · rw [card_d4ShortSL2 hσ3, hK]
    have he : ((2 ^ n) ^ 3) ^ 2 = 2 ^ (6 * n) := by
      rw [← pow_mul, ← pow_mul]
      congr 1
      ring
    rw [he]
    exact dvd_mul_of_dvd_right hpq _

end CFSG.LocalAnalysis.UniquenessCase.UC22
