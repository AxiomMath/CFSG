module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.K1419ClsDefs
import CFSG.LocalAnalysis.StandardType.GGNbrLSideKitComm
import CFSG.LieType.Universal.Symplectic
import CFSG.LocalAnalysis.ComponentInitial.SymplecticFlagOrder
import CFSG.LocalAnalysis.ComponentInitial.TwoPrimeSolvable
import CFSG.RankThree.PartOne.KC.SymplecticInnerPlaneAlt6
import CFSG.RankThree.Classical.SteinbergBJSymplecticCrossPrimeBlocks
public import CFSG.HardMathSupport.Solomon.Coordinator.I18_3LInput
public import CFSG.HardMathSupport.Solomon.Coordinator.L3C143AltMain
public import CFSG.HardMathSupport.Solomon.Coordinator.YS08.LieQ.Derivation
public import CFSG.HardMathSupport.Solomon.UniquenessMaximal.GenL3.Input252
public import CFSG.HardMathSupport.Solomon.UniquenessMaximal.Sec6D62
public import CFSG.HardMathSupport.Solomon.UniquenessMaximal.Sec6E66
public import CFSG.LocalAnalysis.GLTheoremA.CatA.KD76c
public import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10FBase2
public import CFSG.LocalAnalysis.GLTheoremA.CatA.YS1011U64Types
public import CFSG.LocalAnalysis.GLTheoremA.CatC.ChevQ
public import CFSG.LocalAnalysis.GLTheoremA.PartI.I1132
public import CFSG.LocalAnalysis.GLTheoremA.PartI.KDSU3Holds
public import CFSG.LocalAnalysis.GLTheoremA.PartI.RankTwoDown
public import CFSG.LocalAnalysis.GLTheoremA.S10.Bridge
public import CFSG.LocalAnalysis.GLTheoremA.S10.Inputs105
public import CFSG.LocalAnalysis.GLTheoremA.S10.InputsBeta
public import CFSG.LocalAnalysis.GLTheoremA.S10.InputsSetup
public import CFSG.LocalAnalysis.GLTheoremA.S11.Inputs119
public import CFSG.LocalAnalysis.GLTheoremA.S4.FullCover.MultSporadic
public import CFSG.LocalAnalysis.GLTheoremA.S4.YS02Holds
public import CFSG.LocalAnalysis.GLTheoremA.S6.Lemma62AuxComp
public import CFSG.LocalAnalysis.GLTheoremA.Sec5Setup
public import CFSG.LocalAnalysis.RankThreeTheoremC.InvariantTwoBalanceThree
public import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.Bal3Defs
public import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.Bal3Transitive
public import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.I294Inputs
public import CFSG.LocalAnalysis.RankThreeTheoremC.PlaneTransvection
public import CFSG.Quasithin.Vol2.KGFactC31RuRef
public import CFSG.Quasithin.Vol2.KGFactC31RuRefBase
public import CFSG.RankThree.PartTwo.Sec11.Data
public import CFSG.RankThree.PartTwo.Sec14.Item1411HJ
public import CFSG.RankThree.PartTwo.Sec14.Item143N
public import CFSG.RankThree.PartTwo.Sec15.Item157
public import CFSG.RankThree.PartTwo.Sec16.Item163ProofR
public import CFSG.RankThree.PartTwo.Sec16.Item164Proof
public import CFSG.RankThree.PartTwo.Sec16.Item169HJ
public import CFSG.RankThree.PartTwo.Sec17.Item1724Two
public import CFSG.RankThree.PartTwo.Sec17.Item17TailSteps
public import CFSG.RankThree.PartTwo.Sec17.RouteProvers
public import CFSG.RankThree.PartTwo.Sec17.RouteProvers142
public import CFSG.RankThree.PartTwo.Sec6.Statements
public import CFSG.RankThree.S4Free.SuzukiEight
public import CFSG.Sporadic.HeldB.Common
public import Certificates.Certificate14953
public import Certificates.Certificate7233Base
public import Certificates.Certificate8166

public section

namespace CFSG.StandardType

open CFSG CFSG.Open CFSG.Open.StatedAPI CFSG.LocalAnalysis.ComponentInitial

private theorem kitTame_card_primeFactors_two_three (a b : ℕ) (ha : a ≠ 0) (hb : b ≠ 0) :
    (2 ^ a * 3 ^ b).primeFactors.card ≤ 2 := by
  rw [Nat.primeFactors_mul (by positivity) (by positivity),
    Nat.primeFactors_prime_pow ha Nat.prime_two, Nat.primeFactors_prime_pow hb Nat.prime_three]
  exact (Finset.card_union_le _ _).trans (by simp)

private theorem kitTame_isSolvable_of_card_two_three {G : Type*} [Group G] [Finite G] {a b : ℕ}
    (ha : a ≠ 0) (hb : b ≠ 0) (h : Nat.card G = 2 ^ a * 3 ^ b) : Group.IsSolvable G :=
  CFSG.LocalAnalysis.ComponentInitial.isSolvable_of_card_primeFactors_le_two
    (h ▸ kitTame_card_primeFactors_two_three a b ha hb)

private theorem kitTame_group_statedSp (s : ℕ) (K : Type) [Field K] [Finite K] :
    CFSG.IsQuasisimple ↥(commutator (StatedSp s K)) ∨ Group.IsSolvable (StatedSp s K) := by
  rcases Nat.eq_zero_or_pos s with rfl | hs
  · right
    refine CFSG.LocalAnalysis.ComponentInitial.isSolvable_of_card_primeFactors_le_two ?_
    rw [CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag.card_statedSp]
    simp
  · by_cases hq : (Infinite K ∨ 4 ≤ Nat.card K) ∨ (Nat.card K = 3 ∧ 2 ≤ s) ∨
        (Nat.card K = 2 ∧ 3 ≤ s)
    · left
      have h := CFSG.LieType.Universal.Symplectic.isQuasisimple s K hs hq
      have h1 : commutator (StatedSp s K) = ⊤ := Group.isPerfect_def.mp h.1
      exact CFSG.LocalCores.isQuasisimple_of_mulEquiv
        ((MulEquiv.subgroupCongr h1).trans Subgroup.topEquiv).symm h
    · have hK2 : 2 ≤ Nat.card K := Nat.succ_le_of_lt Finite.one_lt_card
      have hK4 : Nat.card K < 4 := by
        by_contra h
        exact hq (Or.inl (Or.inr (by omega)))
      have h3 : Nat.card K = 3 → s < 2 := fun h => by
        by_contra h'
        exact hq (Or.inr (Or.inl ⟨h, by omega⟩))
      have h2 : Nat.card K = 2 → s < 3 := fun h => by
        by_contra h'
        exact hq (Or.inr (Or.inr ⟨h, by omega⟩))
      have hcard := CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag.card_statedSp (K := K) s
      rcases (show Nat.card K = 2 ∨ Nat.card K = 3 by omega) with hK | hK
      · rcases (show s = 1 ∨ s = 2 by have := h2 hK; omega) with rfl | rfl
        · right
          refine kitTame_isSolvable_of_card_two_three (a := 1) (b := 1) (by norm_num) (by norm_num) ?_
          rw [hcard, hK]
          norm_num [Finset.Icc_self]
        · left
          have hd : Module.finrank K (Fin 2 ⊕ Fin 2 → K) = 4 := by
            rw [Module.finrank_fintype_fun_eq_card, Fintype.card_sum, Fintype.card_fin]
          obtain ⟨E⟩ := CFSG.RankThree.PartOne.nonempty_mulEquiv_sympFour hK
            (CFSG.RankThree.Classical.spForm_isAlt (r := 2) (K := K))
            (CFSG.RankThree.Classical.spForm_nondegenerate (r := 2) (K := K)) hd
          let e₀ : StatedSp 2 K ≃* sesqUnitaryGroup (CFSG.RankThree.Classical.spForm 2 K) :=
            (MonoidHom.ofInjective
              (CFSG.RankThree.Classical.spLin_injective (r := 2) (K := K))).trans
              (MulEquiv.subgroupCongr (CFSG.RankThree.Classical.range_spLin (r := 2) (K := K)))
          exact (CFSG.RankThree.PartOne.derived_of_mulEquiv_sympFour (e₀.trans E)).1
      · have hs1 : s = 1 := by have := h3 hK; omega
        subst hs1
        right
        refine kitTame_isSolvable_of_card_two_three (a := 3) (b := 1) (by norm_num) (by norm_num) ?_
        rw [hcard, hK]
        norm_num [Finset.Icc_self]

theorem ggNbrLSideTame_sp {X : Type} [Group X] {A : Subgroup X} {s : ℕ} {K : Type} [Field K]
    [Finite K] (φ : ↥A ≃* ↥(StatedSp s K)) :
    CFSG.IsQuasisimple ↥⁅A, A⁆ ∨ Group.IsSolvable ↥A := by
  exact CFSG.StandardType.GGNbrLSideKit.tame_of_mulEquiv φ (kitTame_group_statedSp s K)

end CFSG.StandardType
