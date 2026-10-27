module

public import CFSG.LocalAnalysis.StandardType.GGTableBTwE6DeltaOutdiag
public import CFSG.LocalAnalysis.ComponentClassification.CatLeafInputs
import CFSG.LocalAnalysis.StandardType.GGTwE6DD2Recipe
import CFSG.LocalAnalysis.StandardType.GGTwInndiagRootBridge
import CFSG.LocalAnalysis.StandardType.GGTwE6ThreeLift
import CFSG.HardMathSupport.Lang.Coordinator.OuterFixedOrderTwistedE6Descent
import CFSG.HardMathSupport.Lang.Coordinator.OuterFixedOrderTwistedE6Fixed
public import CFSG.CharacterTheory.BrauerThirdMainTheorem.CentralResidueMaps
public import CFSG.CharacterTheory.BrauerThirdMainTheorem.NormalizerClassLifting
public import CFSG.CharacterTheory.BrauerThirdMainTheorem.PrincipalClassDefects
public import CFSG.CharacterTheory.Semidihedral.Principal.DegreeZeroGram
public import CFSG.CharacterTheory.TwoRankLowerBound.BrauerCharacterCriterion
public import CFSG.LocalAnalysis.ComponentClassification.BlockCentralSylowEquality
public import CFSG.LocalAnalysis.ComponentClassification.BlockFourFactorSupport
public import CFSG.LocalAnalysis.ComponentClassification.BlockLargeProductInvolutions
public import CFSG.LocalAnalysis.ComponentClassification.BlockMovedFactorSylowCentral
public import CFSG.LocalAnalysis.ComponentClassification.BlockNormalizerOrder
public import CFSG.LocalAnalysis.ComponentClassification.BlockPermutationSylowLifting
public import CFSG.LocalAnalysis.ComponentClassification.BlockStrictFullSylowAbelian
public import CFSG.LocalAnalysis.ComponentClassification.CatLeafBasic
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitHeMax
public import CFSG.LocalAnalysis.ComponentClassification.KProper
public import CFSG.LocalAnalysis.ComponentClassification.LabeledBlockPermutation
public import CFSG.LocalAnalysis.ComponentClassification.OutcomeLocalOddCentralizer
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCorrCriticalStandard
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
public import Certificates.Certificate1
public import Certificates.Certificate10
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

public section

namespace CFSG.StandardType.TwE6D3

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
open CFSG.Assembly.LowTwoRank (StatedLieTag)
open CFSG.ComponentClassification.CatLeaf (lieOrderNumerator)
open CFSG.ComponentClassification.FixedCommutingProduct (fixedSubgroup)
open CFSG.HardMathSupport.Lang.Coordinator CFSG.StandardType.NoOffTwE6Three

section Arith

theorem odd_two_pow_pow_sub_one {d k : ℕ} (hd : 1 ≤ d) (hk : 1 ≤ k) : Odd ((2 ^ d) ^ k - 1) := by
  obtain ⟨m, hm⟩ : 2 ∣ (2 ^ d) ^ k := dvd_pow (dvd_pow_self 2 (by omega)) (by omega)
  have h1 : 1 ≤ (2 ^ d) ^ k := Nat.one_le_pow _ _ (by positivity)
  exact ⟨m - 1, by omega⟩

theorem odd_two_pow_pow_add_one {d k : ℕ} (hd : 1 ≤ d) (hk : 1 ≤ k) : Odd ((2 ^ d) ^ k + 1) := by
  obtain ⟨m, hm⟩ : 2 ∣ (2 ^ d) ^ k := dvd_pow (dvd_pow_self 2 (by omega)) (by omega)
  exact ⟨m, by omega⟩

theorem not_two_pow_dvd_lieOrderNumerator {d : ℕ} (hd : 1 ≤ d) :
    ¬ 2 ^ (36 * d + 1) ∣ lieOrderNumerator .twistedE6 0 (2 ^ d) := by
  have hodd : Odd (((2 ^ d) ^ 12 - 1) * ((2 ^ d) ^ 9 + 1) * ((2 ^ d) ^ 8 - 1) *
      ((2 ^ d) ^ 6 - 1) * ((2 ^ d) ^ 5 + 1) * ((2 ^ d) ^ 2 - 1)) := by
    refine Odd.mul (Odd.mul (Odd.mul (Odd.mul (Odd.mul ?_ ?_) ?_) ?_) ?_) ?_
    · exact odd_two_pow_pow_sub_one hd (by norm_num)
    · exact odd_two_pow_pow_add_one hd (by norm_num)
    · exact odd_two_pow_pow_sub_one hd (by norm_num)
    · exact odd_two_pow_pow_sub_one hd (by norm_num)
    · exact odd_two_pow_pow_add_one hd (by norm_num)
    · exact odd_two_pow_pow_sub_one hd (by norm_num)
  have hN : lieOrderNumerator .twistedE6 0 (2 ^ d) = 2 ^ (36 * d) *
      (((2 ^ d) ^ 12 - 1) * ((2 ^ d) ^ 9 + 1) * ((2 ^ d) ^ 8 - 1) *
        ((2 ^ d) ^ 6 - 1) * ((2 ^ d) ^ 5 + 1) * ((2 ^ d) ^ 2 - 1)) := by
    simp only [lieOrderNumerator]
    rw [show 36 * d = d * 36 by ring, pow_mul]
    ring
  rw [hN, pow_succ]
  intro h
  have h2 : 2 ∣ ((2 ^ d) ^ 12 - 1) * ((2 ^ d) ^ 9 + 1) * ((2 ^ d) ^ 8 - 1) *
      ((2 ^ d) ^ 6 - 1) * ((2 ^ d) ^ 5 + 1) * ((2 ^ d) ^ 2 - 1) :=
    (Nat.mul_dvd_mul_iff_left (by positivity)).1 h
  obtain ⟨m, hm⟩ := hodd
  omega

end Arith

section Outer


theorem exists_moved_of_outer {K : Type} [Field K] [Finite K] {n : ℕ} (hn : 1 ≤ n)
    (hK : Nat.card K = (2 ^ n) ^ 2) {D : Subgroup (TwE6Delta.RecipeR K n)}
    (hD : 2 ^ (12 * n + 1) ∣ Nat.card D) {φ : MulAut (TwE6Delta.RecipeR K n)} (hφ : φ ^ 3 = 1)
    (hI : φ ∉ TwE6Delta.RecipeI K n) : ∃ x ∈ D, φ x ≠ x := by
  by_contra hcon
  have hcon : ∀ x ∈ D, φ x = x := fun x hx => by_contra fun h => hcon ⟨x, hx, h⟩
  haveI : CharP K 2 := charP_two_of_card (m := n * 2) (by rw [hK, pow_mul])
  have hinj : Function.Injective (iterateFrobenius K 2 n) := (iterateFrobenius K 2 n).injective
  set σ : K ≃+* K := RingEquiv.ofBijective (iterateFrobenius K 2 n)
    ⟨hinj, Finite.surjective_of_injective hinj⟩ with hσdef
  have hσ : ∀ c, σ c = c ^ 2 ^ n := fun c => iterateFrobenius_def 2 n c
  have hK2 : Nat.card K = 2 ^ (2 * n) := by rw [hK, ← pow_mul, mul_comm]
  obtain ⟨ε, hε⟩ := TwE6DD2.exists_recipeEquiv hn hK σ hσ
  set β : MulAut (twistedE6RootGroup K σ) := MulAut.congr ε.symm φ with hβdef
  have hβφ : MulAut.congr ε β = φ := by
    refine MulEquiv.ext fun x => ?_
    show ε (ε.symm (φ (ε (ε.symm x)))) = φ x
    simp only [MulEquiv.apply_symm_apply]
  have hβ3 : β ^ 3 = 1 := by rw [hβdef, ← map_pow, hφ, map_one]
  obtain ⟨-, -, -, -, -, -, -, -, ⟨Θ, hΘ, -, hker, -, -, -⟩, -, -, -, -, -⟩ :=
    twisted_E6_all_characteristic_exact_automorphism_normal_form Nat.prime_two hn K hK σ hσ
  have hkerr : Θ.ker = (RecipeExcLang.twConj K σ).range := by
    rw [hker, ← inn_sup_compatParamAut_eq_range_twConj σ,
      range_compatParamAut_eq_twistedE6Diag σ]
    rfl
  have hη1 : Θ β ≠ 1 := by
    intro h1
    have hmem : β ∈ (RecipeExcLang.twConj K σ).range := by
      rw [← hkerr, MonoidHom.mem_ker]
      exact h1
    exact hI (hβφ ▸ (hε β).2 hmem)
  obtain ⟨d, hd, hd0, r, ε', hε', ψ, hψ⟩ :=
    twisted_E6_field_descent_of_prime_order Nat.prime_two hn K hK2 σ hσ Θ hΘ Nat.prime_three
      (by norm_num) β hβ3 hη1
  have hle : fixedSubgroup β ≤ fixedSubgroup (β ^ r) := by
    intro x hx
    have hx' : β x = x := hx
    show (β ^ r) x = x
    clear hψ
    induction r with
    | zero => rfl
    | succ k ih => rw [pow_succ', MulAut.mul_apply, ih, hx']
  have hmapψ : (fixedSubgroup (β ^ r)).map (ψ : twistedE6RootGroup K σ ≃* _).toMonoidHom ≤
      fixedSubgroup (fieldActor (t := TwistTag.E6) σ ε') := by
    rintro _ ⟨x, hx, rfl⟩
    have h := congrArg (fun g : MulAut (twistedE6RootGroup K σ) => g (ψ x)) hψ
    have hx' : (β ^ r) x = x := hx
    simp only [MulAut.mul_apply, MulAut.inv_apply, MulEquiv.symm_apply_apply] at h
    change fieldActor (t := TwistTag.E6) σ ε' (ψ x) = ψ x
    rw [← h, hx']
  have hσ' : ∀ c, σ c = c ^ 2 ^ (d * 3) := fun c => by rw [hσ, hd, mul_comm]
  have hdvd := card_fixedSubgroup_fieldActor_dvd Nat.prime_two hd0 (by norm_num : 1 ≤ 3) K
    (by rw [hK2, hd, show 2 * (3 * d) = 2 * (d * 3) by ring]) σ ε' hσ' hε'
  have hψinj : Function.Injective (ψ : twistedE6RootGroup K σ ≃* _).toMonoidHom :=
    ψ.injective
  have hcard : Nat.card (fixedSubgroup β) ∣ lieOrderNumerator .twistedE6 0 (2 ^ d) := by
    refine Nat.dvd_trans ?_ hdvd
    have h1 := Subgroup.card_dvd_of_le hmapψ
    rw [Subgroup.card_map_of_injective hψinj] at h1
    exact (Subgroup.card_dvd_of_le hle).trans h1
  have hDle : D.map ε.symm.toMonoidHom ≤ fixedSubgroup β := by
    rintro _ ⟨x, hx, rfl⟩
    show β (ε.symm x) = ε.symm x
    rw [hβdef, MulAut.congr_apply]
    simp only [MulEquiv.symm_symm, MulEquiv.trans_apply, MulEquiv.apply_symm_apply]
    rw [hcon x hx]
  have hDcard : Nat.card D ∣ Nat.card (fixedSubgroup β) := by
    have h1 := Subgroup.card_dvd_of_le hDle
    rwa [Subgroup.card_map_of_injective ε.symm.injective] at h1
  refine not_two_pow_dvd_lieOrderNumerator hd0 ?_
  have h36 : 36 * d + 1 = 12 * n + 1 := by omega
  rw [h36]
  exact hD.trans (hDcard.trans hcard)

end Outer

end CFSG.StandardType.TwE6D3
