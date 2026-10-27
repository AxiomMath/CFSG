module


public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.UCOneFourTen.CoreSlices
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.UCOneFourTen.CoreFacts
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.UCOneFourTen.CoreSporRu
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.BorelOvergroupHolds
import CFSG.HardMathSupport.Solomon.Coordinator.SporOrders
import CFSG.LocalAnalysis.AGL81I.Section3.ThreeNineCatThreeSporGenInputs
import CFSG.HardMathSupport.Solomon.Proving.ThreeCoverRank
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.LocalAnalysis.SectionRank.Sporadic.B
public import CFSG.LocalAnalysis.SectionRank.Sporadic.Co1
public import CFSG.LocalAnalysis.SectionRank.Sporadic.Fi22
public import CFSG.LocalAnalysis.SectionRank.Sporadic.Fi23
public import CFSG.LocalAnalysis.SectionRank.Sporadic.Fi24prime
public import CFSG.LocalAnalysis.SectionRank.Sporadic.Suz
public import CFSG.LocalAnalysis.SectionRank.Sporadic.Th
public import CFSG.RankThree.PartTwo.Sec4.Census.Item44TwoCoverList
public import CFSG.Sporadic.Bridge.RuSurj
import CFSG.HardMathSupport.Timmesfeld.Coordinator.SporadicRankData

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.UC410

open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22
open CFSG.Open (orderJ3 orderRu orderON orderHN orderFi23 orderCo1 orderLy orderTh orderJ4
  orderFi24Prime orderBabyMonster orderMonster)

private lemma two_pow_dvd_szOrder (n : ℕ) :
    2 ^ (2 * n) ∣ (2 ^ n) ^ 2 * (2 ^ n - 1) * ((2 ^ n) ^ 2 + 1) := by
  rw [show (2 ^ n) ^ 2 = 2 ^ (2 * n) by rw [← pow_mul, mul_comm]]
  exact dvd_mul_of_dvd_left (dvd_mul_of_dvd_left (dvd_refl _) _) _

private lemma le_of_two_pow_dvd_sporOrd {n : ℕ} {s : TauCeti.SporadicName}
    (h : 2 ^ (2 * n) ∣ CFSG.HardMathSupport.Solomon.Coordinator.sporOrd s) : n ≤ 23 := by
  by_contra hn
  have h48 : 2 ^ 48 ∣ CFSG.HardMathSupport.Solomon.Coordinator.sporOrd s :=
    (pow_dvd_pow 2 (by omega)).trans h
  cases s <;> revert h48 <;>
    norm_num [CFSG.HardMathSupport.Solomon.Coordinator.sporOrd, orderJ3, orderRu, orderON,
      orderHN, orderFi23, orderCo1, orderLy, orderTh, orderJ4, orderFi24Prime,
      orderBabyMonster, orderMonster]

private lemma sporOrderTest {n : ℕ} (hn : Odd n) (hn3 : 3 ≤ n) {s : TauCeti.SporadicName}
    (h : (2 ^ n) ^ 2 * (2 ^ n - 1) * ((2 ^ n) ^ 2 + 1) ∣
      CFSG.HardMathSupport.Solomon.Coordinator.sporOrd s) :
    s = .Suz ∨ s = .Ru ∨ s = .Co1 ∨ s = .Fi22 ∨ s = .Fi23 ∨ s = .Fi24Prime ∨
      s = .Th ∨ s = .B ∨ s = .M := by
  have h2 : 2 ^ (2 * n) ∣ CFSG.HardMathSupport.Solomon.Coordinator.sporOrd s :=
    (two_pow_dvd_szOrder n).trans h
  have hle := le_of_two_pow_dvd_sporOrd h2
  obtain ⟨a, rfl⟩ := hn
  have ha1 : 1 ≤ a := by omega
  have ha : a ≤ 11 := by omega
  interval_cases a <;> cases s <;>
    norm_num [CFSG.HardMathSupport.Solomon.Coordinator.sporOrd, orderJ3, orderRu, orderON,
      orderHN, orderFi23, orderCo1, orderLy, orderTh, orderJ4, orderFi24Prime,
      orderBabyMonster, orderMonster] at h
  all_goals simp

private lemma sporOrderTestRu {n : ℕ} (hn : Odd n) (hn3 : 3 ≤ n)
    (h : (2 ^ n) ^ 2 * (2 ^ n - 1) * ((2 ^ n) ^ 2 + 1) ∣
      CFSG.HardMathSupport.Solomon.Coordinator.sporOrd .Ru) : n = 3 := by
  have h2 : 2 ^ (2 * n) ∣ CFSG.HardMathSupport.Solomon.Coordinator.sporOrd .Ru :=
    (two_pow_dvd_szOrder n).trans h
  have hle := le_of_two_pow_dvd_sporOrd h2
  obtain ⟨a, rfl⟩ := hn
  have ha1 : 1 ≤ a := by omega
  have ha : a ≤ 11 := by omega
  interval_cases a <;>
    norm_num [CFSG.HardMathSupport.Solomon.Coordinator.sporOrd, orderRu] at h
  all_goals omega

private lemma eq_one_of_odd_dvd_multiplier {c : ℕ} {s : TauCeti.SporadicName}
    (h : c ∣ CFSG.RankThree.PartTwo.Sec4.Census.sporadicMultiplierOrder s)
    (hodd : Odd c) (h3 : c ≠ 3) : c = 1 := by
  obtain ⟨k, rfl⟩ := hodd
  cases s <;>
    simp only [CFSG.RankThree.PartTwo.Sec4.Census.sporadicMultiplierOrder] at h
  all_goals
    have hk : k ≤ 5 := by
      have := Nat.le_of_dvd (by norm_num) h
      omega
    interval_cases k <;> simp_all

private noncomputable def spurMulEquiv {X : Type} [Group X] [Finite X] {K : Subgroup X}
    {s : TauCeti.SporadicName}
    (e : ↥K ⧸ center ↥K ≃* (TauCeti.CFSGIndex.sporadic s).Group)
    (hZ : center ↥K = ⊥) : ↥K ≃* (TauCeti.CFSGIndex.sporadic s).Group :=
  ((QuotientGroup.quotientMulEquivOfEq hZ).trans
    (QuotientGroup.quotientBot (G := ↥K))).symm.trans e

private lemma spurFourLePRank {X : Type} [Group X] [Finite X] {K : Subgroup X}
    {s : TauCeti.SporadicName}
    (hbr : Nonempty (CFSG.Blueprint.NativeSporadic.Carrier s ≃*
      (TauCeti.CFSGIndex.sporadic s).Group))
    (hE : ∃ E : Subgroup (CFSG.Blueprint.NativeSporadic.Carrier s),
      CFSG.Open.IsElemAbelian 3 E ∧ Nat.card E = 3 ^ 4)
    (e : ↥K ⧸ center ↥K ≃* (TauCeti.CFSGIndex.sporadic s).Group)
    (hZ : center ↥K = ⊥) : 4 ≤ CFSG.Open.pRank 3 (⊤ : Subgroup ↥K) :=
  CFSG.HardMathSupport.Timmesfeld.Coordinator.sporadicThreeRankGe_of_carrier s 4 hbr hE ↥K
    ⟨spurMulEquiv e hZ⟩

private lemma spurFalseOfRankFour {X : Type} [Group X] [Finite X] {K L T Y : Subgroup X}
    {n : ℕ} (h : CoreSetup X K L T Y n)
    (h4 : 4 ≤ CFSG.Open.pRank 3 (⊤ : Subgroup ↥K)) : False := by
  have h3 : CFSG.Open.pRank 3 (⊤ : Subgroup ↥K) ≤ 3 :=
    h.pRank_K_le (p := 3) Nat.prime_three (by norm_num)
  omega

section SporCoverCerts

variable {X : Type} [Group X] [Finite X] {K L T Y : Subgroup X} {n : ℕ}

private lemma spurCardCenterDvd (h : CoreSetup X K L T Y n) (s : TauCeti.SporadicName)
    (e : ↥K ⧸ center ↥K ≃* (TauCeti.CFSGIndex.sporadic s).Group) :
    Nat.card (center ↥K) ∣
      CFSG.RankThree.PartTwo.Sec4.Census.sporadicMultiplierOrder s :=
  CFSG.LocalAnalysis.AGL81I.Section3.SporGenThree.card_center_dvd_sporadicMultiplierOrder
    s ↥K ⟨⟨h.quasisimple.1⟩, h.quasisimple.2,
      CFSG.ComponentClassification.Helpers.quasisimple_central_quotient_nonabelian ↥K
        h.quasisimple⟩ ⟨e⟩

private lemma spurCenterEqBot (h : CoreSetup X K L T Y n) {s : TauCeti.SporadicName}
    (e : ↥K ⧸ center ↥K ≃* (TauCeti.CFSGIndex.sporadic s).Group)
    (h3 : Nat.card (center ↥K) ≠ 3) : center ↥K = ⊥ := by
  have hdvd := spurCardCenterDvd h s e
  exact Subgroup.eq_bot_of_card_eq _ (eq_one_of_odd_dvd_multiplier hdvd h.odd_card_center h3)

end SporCoverCerts

theorem coreSporSlice :
    CoreSporSlice := by
  intro X _ _ K L T Y n s h ⟨e⟩
  obtain ⟨hoddn, hn3⟩ := h.odd_three_le
  have hcard : Nat.card (Bar2 L) = (2 ^ n) ^ 2 * (2 ^ n - 1) * ((2 ^ n) ^ 2 + 1) :=
    CFSG.LocalAnalysis.UniquenessCase.PartTwo.S19.card_of_isSz_two_pow h.sz
  have hdiv : (2 ^ n) ^ 2 * (2 ^ n - 1) * ((2 ^ n) ^ 2 + 1) ∣
      CFSG.HardMathSupport.Solomon.Coordinator.sporOrd s := by
    rw [← hcard, ← CFSG.HardMathSupport.Solomon.Coordinator.sporadicOrdersTable_holds s,
      ← Nat.card_congr e.toEquiv]
    exact h.card_bar2_dvd_card_quotient_center
  rcases sporOrderTest hoddn hn3 hdiv with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · by_cases hZ3 : Nat.card (center ↥K) = 3
    · exact spurFalseOfRankFour h
        (CFSG.HardMathSupport.Solomon.Proving.threeCover_Suz_rank ↥K h.quasisimple e hZ3)
    · exact spurFalseOfRankFour h
        (spurFourLePRank
          (CFSG.Sporadic.Bridge.nonempty_carrier_mulEquiv_group .Suz)
          CFSG.SectionRank.Suz_elementary_three_rank_four e
          (spurCenterEqBot h e hZ3))
  · have hn : n = 3 := sporOrderTestRu hoddn hn3 hdiv
    subst n
    have hZ : center ↥K = ⊥ := by
      refine spurCenterEqBot h e ?_
      intro hc
      have hdvd := spurCardCenterDvd h .Ru e
      rw [hc] at hdvd
      exact absurd hdvd (by
        norm_num [CFSG.RankThree.PartTwo.Sec4.Census.sporadicMultiplierOrder])
    obtain ⟨b⟩ := CFSG.Sporadic.Bridge.Ru.nonempty_mulEquiv
    exact h.false_of_mulEquiv_ru ((spurMulEquiv e hZ).trans b.symm)
  · have hZ : center ↥K = ⊥ := by
      refine spurCenterEqBot h e ?_
      intro hc
      have hdvd := spurCardCenterDvd h .Co1 e
      rw [hc] at hdvd
      exact absurd hdvd (by
        norm_num [CFSG.RankThree.PartTwo.Sec4.Census.sporadicMultiplierOrder])
    exact spurFalseOfRankFour h
      (spurFourLePRank
        (CFSG.Sporadic.Bridge.nonempty_carrier_mulEquiv_group .Co1)
        CFSG.SectionRank.Co1_elementary_three_rank_four e hZ)
  · by_cases hZ3 : Nat.card (center ↥K) = 3
    · have h6 :=
        CFSG.HardMathSupport.Solomon.Proving.threeCover_Fi22_rank ↥K h.quasisimple e hZ3
      exact spurFalseOfRankFour h (by omega)
    · exact spurFalseOfRankFour h
        (spurFourLePRank
          (CFSG.Sporadic.Bridge.nonempty_carrier_mulEquiv_group .Fi22)
          CFSG.SectionRank.Fi22_elementary_three_rank_four e
          (spurCenterEqBot h e hZ3))
  · have hZ : center ↥K = ⊥ := by
      refine spurCenterEqBot h e ?_
      intro hc
      have hdvd := spurCardCenterDvd h .Fi23 e
      rw [hc] at hdvd
      exact absurd hdvd (by
        norm_num [CFSG.RankThree.PartTwo.Sec4.Census.sporadicMultiplierOrder])
    exact spurFalseOfRankFour h
      (spurFourLePRank
        (CFSG.Sporadic.Bridge.nonempty_carrier_mulEquiv_group .Fi23)
        CFSG.SectionRank.Fi23_elementary_three_rank_four e hZ)
  · by_cases hZ3 : Nat.card (center ↥K) = 3
    · have h8 :=
        CFSG.HardMathSupport.Solomon.Proving.threeCover_Fi24_rank ↥K h.quasisimple e hZ3
      exact spurFalseOfRankFour h (by omega)
    · exact spurFalseOfRankFour h
        (spurFourLePRank
          (CFSG.Sporadic.Bridge.nonempty_carrier_mulEquiv_group .Fi24Prime)
          CFSG.SectionRank.Fi24prime_elementary_three_rank_four e
          (spurCenterEqBot h e hZ3))
  · have hZ : center ↥K = ⊥ := by
      refine spurCenterEqBot h e ?_
      intro hc
      have hdvd := spurCardCenterDvd h .Th e
      rw [hc] at hdvd
      exact absurd hdvd (by
        norm_num [CFSG.RankThree.PartTwo.Sec4.Census.sporadicMultiplierOrder])
    exact spurFalseOfRankFour h
      (spurFourLePRank
        (CFSG.Sporadic.Bridge.nonempty_carrier_mulEquiv_group .Th)
        CFSG.SectionRank.Th_elementary_three_rank_four e hZ)
  · have hZ : center ↥K = ⊥ := by
      refine spurCenterEqBot h e ?_
      intro hc
      have hdvd := spurCardCenterDvd h .B e
      rw [hc] at hdvd
      exact absurd hdvd (by
        norm_num [CFSG.RankThree.PartTwo.Sec4.Census.sporadicMultiplierOrder])
    exact spurFalseOfRankFour h
      (spurFourLePRank
        (CFSG.Sporadic.Bridge.nonempty_carrier_mulEquiv_group .B)
        CFSG.SectionRank.B_elementary_three_rank_four e hZ)
  · have hZ : center ↥K = ⊥ := by
      refine spurCenterEqBot h e ?_
      intro hc
      have hdvd := spurCardCenterDvd h .M e
      rw [hc] at hdvd
      exact absurd hdvd (by
        norm_num [CFSG.RankThree.PartTwo.Sec4.Census.sporadicMultiplierOrder])
    have e' := spurMulEquiv e hZ
    have : Finite (TauCeti.CFSGIndex.sporadic .M).Group := Finite.of_equiv ↥K e'.toEquiv
    exact spurFalseOfRankFour h (by
      rw [CFSG.SectionRank.pRank_top_eq_of_mulEquiv (p := 3) (by norm_num) e']
      exact CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.Bal3.monsterThreeRankFour_holds)

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.UC410
