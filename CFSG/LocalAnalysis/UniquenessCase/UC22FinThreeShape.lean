module

public import CFSG.LocalAnalysis.UniquenessCase.UC22Defs
public import CFSG.Open.StatedDefs
public import Mathlib.FieldTheory.Finite.GaloisField
import CFSG.Open.StatedAPI
import CFSG.Open.StatedCenterThree
import CFSG.Adapters.ProjectiveSpecialLinear
import CFSG.Adapters.LieModelOrders
import CFSG.LieType.Steinberg.CentralExt.LinearPerfect
import CFSG.Timmesfeld.Orders.Distinct
import CFSG.LocalAnalysis.UniquenessCase.UC6N588D3
import CFSG.LocalAnalysis.EvenBN.GMSK.SzFacts
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.JankoOne
public import CFSG.CGT.Timmesfeld75.Statements
public import CFSG.Foundations
public import CFSG.GroupTheory.LocalCores.Fitting
public import CFSG.LocalAnalysis.ComponentClassification.DisjointSolvableKernels
public import CFSG.LocalAnalysis.ComponentClassification.LBalanceComponentLifts
public import CFSG.LocalAnalysis.ComponentClassification.LayerMultiplication
public import CFSG.LocalAnalysis.ComponentClassification.MinimalBCenter
public import CFSG.LocalAnalysis.ComponentClassification.OrdinaryComponentJoins
public import CFSG.LocalAnalysis.ComponentClassification.TwoLayer
public import CFSG.LocalAnalysis.ComponentClassification.UniversalOrbitBlock
public import CFSG.LocalAnalysis.ComponentInitial.LayerComponentOrbit
public import CFSG.LocalAnalysis.RankThreeUC.Asc1930
public import CFSG.Quasithin.Background.A1bGroups
public import CFSG.RankThree.PartOne.S10.ThetaContract
public import CFSG.RankThree.PartOne.S12.InputsBase
import CFSG.Adapters.Certificate43Check
import CFSG.CGT.Timmesfeld75.L2Pair
import CFSG.CGT.Timmesfeld75.ListWCBasic
import CFSG.CharacterTheory.CyclicBlocks.Family
import CFSG.CharacterTheory.Semidihedral.Principal.LargePrimeTorusSylowCentralizers
import CFSG.CharacterTheory.Semidihedral.Principal.PrimeTorusBlockAlignment
import CFSG.CharacterTheory.Wreathed.FourPointInvolutionHexagon
import CFSG.CharacterTheory.Wreathed.OrderThirtyTwoWreathFusion
import CFSG.ClassicalGroups
import CFSG.ClassicalInvolution.Models.SymplecticPairs.ShortRoot
import CFSG.Combinatorics.AperiodicCentralInvolution
import CFSG.Combinatorics.AperiodicFiveOfSix
import CFSG.Combinatorics.AperiodicOppositeComponents
import CFSG.Combinatorics.AperiodicSixteenGraphDistances
import CFSG.Combinatorics.OuterLayerPredecessors
import CFSG.GH74.BNPair.Defs
import CFSG.GH74.GLS.IVK.L2.F1
import CFSG.GH74.KGroups.L3EpsNoNormalThree
import CFSG.GH74.KGroups.L3EpsOutExp
import CFSG.GH74.KGroups.L3EpsOuterLin
import CFSG.LieType.SeitzGeneration.NonabHeisThreeCore
import CFSG.LieType.SeitzGeneration.NonabHeisThreeUnitary
import CFSG.LieType.SeitzGeneration.UnitaryBlocks
import CFSG.LieType.SeitzGeneration.UnitaryHyperScope
import CFSG.LinearAlgebra.LinearGroups.UnitaryThreeOverNine
import CFSG.LinearAlgebra.LinearGroups.UnitaryThreeOverNineInvolutions
import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalSixStructure
import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCatalogG2EvenCanonicalField
import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCatalogSpExclusion
import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCatalogSpSuzukiCentralizer
import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCatalogSpWedge
import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.X7bPairs
import CFSG.LocalAnalysis.SectionRank.QTK.CentreFact.Bounded
import CFSG.LocalAnalysis.SectionRank.QTK.EvenOrth
import CFSG.LocalAnalysis.SectionRank.QTK.Exc
import CFSG.LocalAnalysis.SectionRank.QTK.OddOrth
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.StatementsComponents
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.StatementsEightK
import CFSG.LocalAnalysis.UniquenessCase.UC22S20b
import CFSG.Mathlib.LinearAlgebra.BilinForm.Determinant
import CFSG.Permutation.UnitaryThreeRecognition.Model
import CFSG.Quasithin.EmptyFaithful.Setting
import CFSG.RankThree.CentralLiftSO.SplitTorusWeyl
import CFSG.RankThree.OddKernel.CompleteRankComparison
import CFSG.RankThree.PartOne.KF.ClsPSL
import CFSG.RankThree.PartOne.KF.SU5Model
import CFSG.RankThree.PartOne.KF.SymCtxMatrix
import CFSG.RankThree.PartOne.KF.ToralQuot
import CFSG.RankThree.PartOne.KF.UnitaryModel
import CFSG.RankThree.PartOne.S11c.Sec66PSL
import CFSG.RankThree.PartOne.S11c.Sec66Sp
import CFSG.RankThree.PartOne.S11c.SuFiveD
import CFSG.RankThree.PartOne.S11d.OutSymplectic
import CFSG.RankThree.PartOne.S11d.OutUnitary
import CFSG.RankThree.PartOne.S9.Sylow.ExclusionBasic
import CFSG.Sporadic.Recognition.JankoWongPSLNine
import CFSG.Sporadic.Schreier.J4SProfileNode
import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.PSL2NormalizedRootSylowCount

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

open Subgroup

namespace P22fin3

theorem card_eq_of_equiv_statedSL_three {Q : Type} [Group Q] {n : ℕ} (hn : n ≠ 0)
    (e : Q ≃* CFSG.Open.StatedSL 3 (GaloisField 2 n)) :
    Nat.card Q = 2 ^ (n * 3) * (((2 ^ n) ^ 2 - 1) * ((2 ^ n) ^ 3 - 1)) := by
  rw [Nat.card_congr e.toEquiv, CFSG.Open.StatedAPI.card_statedSL_three, GaloisField.card 2 n hn,
    pow_mul]

theorem odd_card_part {n : ℕ} (hn : n ≠ 0) : Odd (((2 ^ n) ^ 2 - 1) * ((2 ^ n) ^ 3 - 1)) :=
  (CFSG.Timmesfeld.Orders.odd_pow_sub_one (Nat.pos_of_ne_zero hn) two_pos).mul
    (CFSG.Timmesfeld.Orders.odd_pow_sub_one (Nat.pos_of_ne_zero hn) three_pos)

theorem not_isSp4_of_equiv_statedSL_three {Q : Type} [Group Q] {n a : ℕ} (hn : 2 < n)
    (e : Q ≃* CFSG.Open.StatedSL 3 (GaloisField 2 n)) : ¬ IsSp4 Q a := by
  intro h
  have ha : 1 ≤ a := h.admissible.2.1
  have hB : Nat.card Q = CFSG.Open.ordBC 2 (2 ^ a) := by
    simpa [CFSG.EvenSmallLie.CatalogOrders.lieOrd] using h.card_eq_lieOrd (by norm_num)
  rw [CFSG.Timmesfeld.Orders.ordBC_two_eq ha, card_eq_of_equiv_statedSL_three (by omega) e] at hB
  have hodd : Odd (((2 ^ a) ^ 2 - 1) * ((2 ^ a) ^ 4 - 1)) :=
    (CFSG.Timmesfeld.Orders.odd_pow_sub_one ha two_pos).mul
      (CFSG.Timmesfeld.Orders.odd_pow_sub_one ha four_pos)
  have h34 := CFSG.Timmesfeld.Orders.eq_of_two_pow_mul_odd (odd_card_part (by omega)) hodd hB
  rw [← h34] at hB
  have hR := Nat.eq_of_mul_eq_mul_left (by positivity) hB
  rw [← pow_mul 2 a 4, ← h34, pow_mul] at hR
  have h3 : 0 < (2 ^ n) ^ 3 - 1 := by
    have : 1 < (2 ^ n) ^ 3 := Nat.one_lt_pow three_ne_zero (Nat.one_lt_two_pow (by omega))
    omega
  have h2 : (2 ^ n) ^ 2 - 1 = (2 ^ a) ^ 2 - 1 := Nat.eq_of_mul_eq_mul_right h3 hR
  have h22 : (2 ^ n) ^ 2 = (2 ^ a) ^ 2 := by
    have := Nat.one_le_two_pow (n := n * 2)
    have := Nat.one_le_two_pow (n := a * 2)
    rw [← pow_mul, ← pow_mul] at h2 ⊢
    omega
  rw [← pow_mul, ← pow_mul] at h22
  have := Nat.pow_right_injective le_rfl h22
  omega

theorem not_isSU3_of_equiv_statedSL_three {Q : Type} [Group Q] {n a : ℕ} (hn : 2 < n)
    (e : Q ≃* CFSG.Open.StatedSL 3 (GaloisField 2 n)) : ¬ IsSU3 Q a := by
  rintro ⟨-, hU⟩
  have ha : 1 ≤ a := hU.admissible.2.1
  have hB : Nat.card (Q ⧸ center Q) = CFSG.Open.ordTwistedA 2 (2 ^ a) := by
    simpa [CFSG.EvenSmallLie.CatalogOrders.lieOrd] using hU.card_eq_lieOrd (by norm_num)
  have hK : Nat.card (GaloisField 2 n) = 2 ^ n := GaloisField.card 2 n (by omega)
  have hZ : Nat.card (center Q) = Nat.gcd 3 (2 ^ n - 1) := by
    rw [Nat.card_congr (Subgroup.centerCongr e).toEquiv]
    by_cases h3 : 3 ∣ 2 ^ n - 1
    · rw [CFSG.Open.StatedCenterThree.card_center_statedSL_three (by rwa [hK]),
        Nat.gcd_eq_left h3]
    · have hd := CFSG.LieType.Steinberg.card_center_specialLinearGroup_dvd (n := 3)
        (by norm_num) (GaloisField 2 n)
      rw [hK, show Nat.gcd 3 (2 ^ n - 1) = 1 from
        (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).2 h3, Nat.dvd_one] at hd
      rw [show Nat.gcd 3 (2 ^ n - 1) = 1 from
        (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).2 h3, ← hd]
      exact Nat.card_congr (Subgroup.centerCongr
        (CFSG.Assembly.LowTwoRank.specialLinearGroupEquivStatedSL 3 _).symm).toEquiv
  have hQ := Subgroup.card_eq_card_quotient_mul_card_subgroup (center Q)
  rw [card_eq_of_equiv_statedSL_three (by omega) e, hB, hZ, pow_mul] at hQ
  have hA : CFSG.Open.ordA 2 (2 ^ n) = CFSG.Open.ordTwistedA 2 (2 ^ a) := by
    rw [CFSG.LocalAnalysis.UniquenessCase.UC6.N588.ordA_two_eq]
    exact Nat.div_eq_of_eq_mul_left (Nat.gcd_pos_of_pos_left _ (by norm_num)) hQ
  exact CFSG.Timmesfeld.Orders.ordA_ne_ordTwistedA (by norm_num) (by omega) le_rfl ha hA

theorem not_isL2_of_equiv_statedSL_three {Q : Type} [Group Q] {n a : ℕ} (hn : 2 < n)
    (e : Q ≃* CFSG.Open.StatedSL 3 (GaloisField 2 n)) : ¬ IsL2 Q a := by
  intro h
  have ha : 1 ≤ a := h.admissible.2.1
  have hB : Nat.card Q = CFSG.Open.ordA 1 (2 ^ a) := by
    simpa [CFSG.EvenSmallLie.CatalogOrders.lieOrd] using h.card_eq_lieOrd (by norm_num)
  rw [CFSG.LocalAnalysis.UniquenessCase.UC6.N588.ordA_one_eq,
    Nat.coprime_two_left.mpr (CFSG.Timmesfeld.Orders.odd_two_pow_sub_one ha), Nat.div_one,
    card_eq_of_equiv_statedSL_three (by omega) e] at hB
  have h3a := CFSG.Timmesfeld.Orders.eq_of_two_pow_mul_odd (odd_card_part (by omega))
    (CFSG.Timmesfeld.Orders.odd_pow_sub_one ha two_pos) hB
  subst h3a
  have hR := Nat.eq_of_mul_eq_mul_left (by positivity) hB
  rw [pow_mul] at hR
  generalize hT : 2 ^ n = T at hR
  have hT8 : 8 ≤ T := by
    rw [← hT]
    calc 8 = 2 ^ 3 := by norm_num
      _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) (by omega)
  have h23 : T ^ 2 ≤ T ^ 3 := Nat.pow_le_pow_right (by omega) (by norm_num)
  have h1 : T ≤ T ^ 2 := Nat.le_self_pow (by norm_num) T
  have hsq : (T ^ 3) ^ 2 - 1 = (T ^ 3 - 1) * (T ^ 3 + 1) := by
    have := Nat.sq_sub_sq (T ^ 3) 1
    rw [one_pow] at this
    rw [this, mul_comm]
  rw [hsq, mul_comm] at hR
  have hpos : 0 < T ^ 3 - 1 := by omega
  have := Nat.eq_of_mul_eq_mul_left hpos hR
  omega

theorem not_isSz_of_equiv_statedSL_three {Q : Type} [Group Q] {n a : ℕ} (hn : 2 < n)
    (e : Q ≃* CFSG.Open.StatedSL 3 (GaloisField 2 n)) : ¬ IsSz Q a := by
  intro h
  refine CFSG.LocalAnalysis.EvenBN.GMSK.not_three_dvd_card_of_lieModel_twistedB2 h ?_
  rw [card_eq_of_equiv_statedSL_three (by omega) e]
  have h3 : 3 ∣ (2 ^ n) ^ 2 - 1 := by
    have := Nat.sub_dvd_pow_sub_pow 4 1 n
    rw [one_pow] at this
    rwa [← pow_mul, mul_comm, pow_mul]
  exact (h3.mul_right _).mul_left _

theorem not_isL2Odd_of_equiv_statedSL_three {Q : Type} [Group Q] {n r : ℕ} (hn : 2 < n)
    (e : Q ≃* CFSG.Open.StatedSL 3 (GaloisField 2 n)) (hr2 : r ≠ 2) : ¬ IsL2Odd Q r := by
  intro h
  have hrP : r.Prime := h.admissible.1
  have hrodd : Odd r := hrP.odd_of_ne_two hr2
  have hB : Nat.card Q = CFSG.Open.ordA 1 r := by
    simpa [CFSG.EvenSmallLie.CatalogOrders.lieOrd] using h.card_eq_lieOrd (by norm_num)
  have hEq : r * (r ^ 2 - 1) =
      2 * (2 ^ (n * 3) * (((2 ^ n) ^ 2 - 1) * ((2 ^ n) ^ 3 - 1))) := by
    rw [← CFSG.LocalAnalysis.UniquenessCase.UC6.N588.two_mul_ordA_one hrodd, ← hB,
      card_eq_of_equiv_statedSL_three (by omega) e]
  have hcop : Nat.Coprime (2 * 2 ^ (n * 3)) r :=
    Nat.Coprime.mul_left (Nat.coprime_two_left.2 hrodd)
      ((Nat.coprime_two_left.2 hrodd).pow_left _)
  have hdvd : 2 * 2 ^ (n * 3) ∣ r ^ 2 - 1 :=
    hcop.dvd_of_dvd_mul_left ⟨((2 ^ n) ^ 2 - 1) * ((2 ^ n) ^ 3 - 1), by rw [hEq]; ring⟩
  obtain ⟨j, rfl⟩ := hrodd
  have hj : (2 * j + 1) ^ 2 - 1 = 4 * (j * (j + 1)) := by
    rw [show (2 * j + 1) ^ 2 = 4 * (j * (j + 1)) + 1 by ring, Nat.add_sub_cancel]
  have h2pow : 2 ^ (n * 3) = 2 * 2 ^ (n * 3 - 1) := by
    rw [← pow_succ']
    congr 1
    omega
  rw [hj, h2pow, ← mul_assoc, show 2 * 2 = 4 by norm_num] at hdvd
  have hdvd' := Nat.dvd_of_mul_dvd_mul_left (by norm_num) hdvd
  have hle : 2 ^ (n * 3 - 1) ≤ j + 1 := by
    rcases Nat.even_or_odd j with hje | hjo
    · have hc : Nat.Coprime (2 ^ (n * 3 - 1)) (j + 1) :=
        (Nat.coprime_two_left.2 hje.add_one).pow_left _
      have := hc.dvd_of_dvd_mul_right hdvd'
      have hj0 : j ≠ 0 := by rintro rfl; exact Nat.not_prime_one hrP
      exact (Nat.le_of_dvd (Nat.pos_of_ne_zero hj0) this).trans (Nat.le_succ j)
    · have hc : Nat.Coprime (2 ^ (n * 3 - 1)) j := (Nat.coprime_two_left.2 hjo).pow_left _
      exact Nat.le_of_dvd (Nat.succ_pos j) (hc.dvd_of_dvd_mul_left hdvd')
  have hS : 2 ^ (n * 3) ≤ 2 * j + 2 := by
    rw [h2pow]
    omega
  rw [pow_mul] at hEq hS
  generalize hT : 2 ^ n = T at hEq hS
  have hT8 : 8 ≤ T := by
    rw [← hT]
    calc 8 = 2 ^ 3 := by norm_num
      _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) (by omega)
  generalize hA : T ^ 2 = A at hEq
  generalize hS3 : T ^ 3 = S at hEq hS
  have hSA : S = T * A := by rw [← hS3, ← hA]; ring
  have hA1 : 1 ≤ A := by rw [← hA]; exact Nat.one_le_pow _ _ (by omega)
  have h8A : 8 * A ≤ S := hSA ▸ Nat.mul_le_mul_right A hT8
  have hmono : (S - 1) * ((S - 1) ^ 2 - 1) ≤ (2 * j + 1) * ((2 * j + 1) ^ 2 - 1) :=
    Nat.mul_le_mul (by omega) (Nat.sub_le_sub_right (Nat.pow_le_pow_left (by omega) 2) 1)
  obtain ⟨s, rfl⟩ : ∃ s, S = s + 2 := ⟨S - 2, by omega⟩
  have hs : 2 * (A - 1) < s := by omega
  have hlt : 2 * ((s + 2) * ((A - 1) * (s + 2 - 1))) < (s + 2 - 1) * ((s + 2 - 1) ^ 2 - 1) := by
    rw [show s + 2 - 1 = s + 1 by omega, show (s + 1) ^ 2 - 1 = (s + 2) * s by
      rw [show (s + 1) ^ 2 = (s + 2) * s + 1 by ring, Nat.add_sub_cancel]]
    calc 2 * ((s + 2) * ((A - 1) * (s + 1))) = (s + 1) * (s + 2) * (2 * (A - 1)) := by ring
      _ < (s + 1) * (s + 2) * s := Nat.mul_lt_mul_of_pos_left hs (by positivity)
      _ = (s + 1) * ((s + 2) * s) := by ring
  exact absurd (hmono.trans_eq hEq) (not_le.2 hlt)

theorem not_isJ1_of_equiv_statedSL_three {Q : Type} [Group Q] {n : ℕ} (hn : 2 < n)
    (e : Q ≃* CFSG.Open.StatedSL 3 (GaloisField 2 n)) : ¬ IsJ1 Q := by
  intro h
  haveI : Finite Q := Finite.of_equiv _ e.symm.toEquiv
  have hJ : Nat.card Q = 2 ^ 3 * 21945 := by rw [(kJ1_holds Q h).1]; norm_num
  rw [card_eq_of_equiv_statedSL_three (by omega) e] at hJ
  have := CFSG.Timmesfeld.Orders.eq_of_two_pow_mul_odd (odd_card_part (by omega))
    (by decide) hJ
  omega

theorem eq_three_of_s21_16 {Q : Type} [Group Q] {k n : ℕ} (hk : 2 < k) (hk4 : k ≤ 4)
    (hn : 2 < n) (e : Q ≃* CFSG.Open.StatedSL (k - 1) (GaloisField 2 n))
    (h : (∃ a : ℕ, Odd a ∧ IsSp4 Q a) ∨ (∃ a : ℕ, IsSU3 Q a) ∨ (∃ a : ℕ, IsL2 Q a) ∨
      (∃ a : ℕ, IsSz Q a) ∨ (∃ r : ℕ, r.Prime ∧ r ≠ 2 ∧ IsL2Odd Q r) ∨ IsJ1 Q) :
    k = 3 := by
  by_contra h3
  obtain rfl : k = 4 := by omega
  rcases h with ⟨a, -, ha⟩ | ⟨a, ha⟩ | ⟨a, ha⟩ | ⟨a, ha⟩ | ⟨r, -, hr2, hr⟩ | hJ
  · exact not_isSp4_of_equiv_statedSL_three hn e ha
  · exact not_isSU3_of_equiv_statedSL_three hn e ha
  · exact not_isL2_of_equiv_statedSL_three hn e ha
  · exact not_isSz_of_equiv_statedSL_three hn e ha
  · exact not_isL2Odd_of_equiv_statedSL_three hn e hr2 hr
  · exact not_isJ1_of_equiv_statedSL_three hn e hJ

end P22fin3

end CFSG.LocalAnalysis.UniquenessCase.UC22
