module

public import CFSG.RankThree.PartTwo.Sec21.Item218ProofU4
public import CFSG.RankThree.PartTwo.Sec21.Item21Early2ProofModels
import CFSG.RankThree.PartTwo.Sec21.Item229Orders
import CFSG.RankThree.GroupTheory.ThetaQuotientTransport
import CFSG.Sporadic.J3
import CFSG.Sporadic.He.Simple
import CFSG.Sporadic.J4
import CFSG.RankThree.PartTwo.KFacts.KS14HJBasic
import CFSG.Timmesfeld.Orders.Classical
import CFSG.Timmesfeld.Orders.Exceptional
import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.X6G2
import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.X6Triality
import CFSG.RankThree.PartTwo.Sec6.Item612Local

public section

namespace CFSG.RankThree.PartTwo.Sec21.Item2113Proof

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open CFSG.Assembly.RankThreeEven (projSU)
open CFSG.Blueprint

variable {G : Type} [Group G]

theorem center_eq_bot_of_mulEquiv {X Y : Type*} [Group X] [Group Y]
    (hY : Subgroup.center Y = ⊥) (e : X ≃* Y) : Subgroup.center X = ⊥ := by
  rw [eq_bot_iff]
  intro z hz
  have hz' : e z ∈ Subgroup.center Y := by
    rw [Subgroup.mem_center_iff]
    intro y
    obtain ⟨x, rfl⟩ := e.surjective y
    rw [← map_mul, ← map_mul, Subgroup.mem_center_iff.mp hz x]
  rw [hY, Subgroup.mem_bot] at hz'
  rw [Subgroup.mem_bot]
  exact e.injective (by rw [hz', map_one])

theorem not_mem_of_center_lBar_eq_bot [Finite G] {L : Subgroup G} {c : G}
    (hLc : L ≤ Subgroup.centralizer ({c} : Set G)) (hc3 : c ^ 3 = 1) (hc1 : c ≠ 1)
    (hZ : Subgroup.center (lBar L) = ⊥) : c ∉ L := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  intro hcL
  set c' : L := ⟨c, hcL⟩ with hc'
  have hcZ : (c' : lBar L) ∈ Subgroup.center (lBar L) := by
    rw [Subgroup.mem_center_iff]
    intro y
    induction y using QuotientGroup.induction_on with
    | H l =>
      rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul]
      congr 1
      exact Subtype.ext (Subgroup.mem_centralizer_singleton_iff.mp (hLc l.2))
  rw [hZ, Subgroup.mem_bot, QuotientGroup.eq_one_iff] at hcZ
  have hord : orderOf (⟨c', hcZ⟩ : aschbacherSolvableCore 3 L) = 3 := by
    rw [Subgroup.orderOf_mk, hc', Subgroup.orderOf_mk]
    exact orderOf_eq_prime hc3 hc1
  exact three_not_dvd_card_aschbacherSolvableCore (hord ▸ orderOf_dvd_natCard _)

theorem card_of_isTripleCover {X Y : Type*} [Group X] [Group Y] (h : Sec4.IsTripleCover X Y) :
    Nat.card X = Nat.card Y * 3 := by
  obtain ⟨h3, ⟨e⟩⟩ := h
  rw [Subgroup.card_eq_card_quotient_mul_card_subgroup (Subgroup.center X), h3,
    Nat.card_congr e.toEquiv]

section List


theorem center_lBar_eq_bot_of_isList218 [Finite G] {L : Subgroup G} (hL : IsList218 L) :
    Subgroup.center (lBar L) = ⊥ := by
  rcases hL with e | e | e | e | e | ⟨m, hm⟩ | ⟨m, hm⟩
  · obtain ⟨e⟩ := e
    exact center_eq_bot_of_mulEquiv Item21Early2Proof.center_nativeM24_eq_bot e
  · obtain ⟨e⟩ := e
    exact center_eq_bot_of_mulEquiv Item21Early2Proof.center_nativeHe_eq_bot e
  · obtain ⟨e⟩ := e
    exact center_eq_bot_of_mulEquiv Item21Early2Proof.center_nativeJ2_eq_bot e
  · obtain ⟨e⟩ := e
    exact center_eq_bot_of_mulEquiv Item21Early2Proof.center_nativeRu_eq_bot e
  · obtain ⟨e⟩ := e
    exact center_eq_bot_of_mulEquiv Item21Early2Proof.center_nativeJ4_eq_bot e
  · exact (CFSG.QuasithinUnique.Setup.X6.even_G2_model_two_extensions hm).1
  · exact (CFSG.QuasithinUnique.Setup.X6.even_triality_model_two_extensions hm).1

theorem not_mem_of_isList218 [Finite G] {A E U L : Subgroup G} {c : G}
    (hpair : Sec21Pair G A E U c L) (hL : IsList218 L) : c ∉ L := by
  have hpairs := mem_lThreeStarPairs_iff.mp hpair.mem_pair
  have hcA : c ∈ A := hpair.mem_E.2 hpairs.1.1
  exact not_mem_of_center_lBar_eq_bot
    (Sec6.le_centralizer_of_mem_thetaComponentsAt ((lZeroStarAt_subset A c) hpairs.2.2.1))
    (hpair.mem_S.1.1.2 c hcA) hpairs.2.1 (center_lBar_eq_bot_of_isList218 hL)

theorem card_lBar_ne_of_isList218 [Finite G] {L : Subgroup G} (hL : IsList218 L) {N : ℕ}
    (hN : N = 50232960 ∨ N = 50232960 * 3 ∨ N = 1451520) : Nat.card (lBar L) ≠ N := by
  intro hc
  have hv7 : padicValNat 2 50232960 = 7 := by
    rw [show (50232960 : ℕ) = 2 ^ 7 * 392445 by norm_num]
    exact padicValNat_two_pow_mul_odd (by decide)
  have hv7' : padicValNat 2 (50232960 * 3) = 7 := by
    rw [show (50232960 * 3 : ℕ) = 2 ^ 7 * 1177335 by norm_num]
    exact padicValNat_two_pow_mul_odd (by decide)
  have hv9 : padicValNat 2 1451520 = 9 := by
    rw [show (1451520 : ℕ) = 2 ^ 9 * 2835 by norm_num]
    exact padicValNat_two_pow_mul_odd (by decide)
  have hv : padicValNat 2 N = 7 ∨ padicValNat 2 N = 9 := by
    rcases hN with rfl | rfl | rfl
    · exact Or.inl hv7
    · exact Or.inl hv7'
    · exact Or.inr hv9
  rcases hL with e | e | e | e | e | ⟨m, hm⟩ | ⟨m, hm⟩
  · rw [Nat.card_congr e.some.toEquiv, Sporadic.Mathieu.card_M24] at hc
    rcases hN with rfl | rfl | rfl <;> norm_num at hc
  · rw [Nat.card_congr e.some.toEquiv, Sporadic.He.card_He] at hc
    rcases hN with rfl | rfl | rfl <;> norm_num at hc
  · rw [Nat.card_congr e.some.toEquiv, KFacts.KS14.card_nativeJ2] at hc
    rcases hN with rfl | rfl | rfl <;> norm_num at hc
  · rw [Nat.card_congr e.some.toEquiv, Sporadic.Ru.card_Ru] at hc
    rcases hN with rfl | rfl | rfl <;> norm_num at hc
  · rw [Nat.card_congr e.some.toEquiv, Sporadic.J4.card_J4] at hc
    rcases hN with rfl | rfl | rfl <;> norm_num at hc
  · have hm1 : 1 ≤ m := hm.1.2.1
    rw [Timmesfeld.card_chevalleyExceptionalModel_two hm] at hc
    have h := Item218Proof.padicValNat_ordG2 hm1
    rw [show CFSG.Open.ordG2 (2 ^ m) = N from hc] at h
    omega
  · have hm1 : 1 ≤ m := hm.1.2.1
    rw [Timmesfeld.card_chevalleyExceptionalModel_two hm] at hc
    have h := Item218Proof.padicValNat_ordTrialityD4 hm1
    rw [show CFSG.Open.ordTrialityD4 (2 ^ m) = N from hc] at h
    omega

theorem card_eq_of_isList218 [Finite G] (h211 : Item211) {A E U L : Subgroup G} {c : G}
    (hpair : Sec21Pair G A E U c L) (hL : IsList218 L) : Nat.card A = 3 ^ 3 := by
  rcases h211 G A E U c L hpair with ⟨-, -, h27, -, -⟩ | ⟨-, h27, -⟩ | ⟨-, h27, -⟩ |
      ⟨-, h27, -⟩ | ⟨-, h27, -⟩ | ⟨-, h27, -⟩ | ⟨-, h27, -⟩ | ⟨-, h27, -⟩ | ⟨-, h27, -⟩ |
      ⟨⟨n, hn1, hno, ⟨e⟩⟩, -, -⟩ | ⟨h11, -, -⟩ | ⟨-, h27, -⟩ | ⟨h13, -, -⟩
  all_goals try exact h27
  · exfalso
    have hn : 1 ≤ n := by omega
    have hU := Item218Proof.padicValNat_card_projSU_four hn
    rw [← Nat.card_congr e.toEquiv] at hU
    rcases Item218Proof.padicValNat_card_lBar_of_isList218 hL with h | h | h | h |
        ⟨m, hm, hG, h⟩ | ⟨m, hm, h⟩
    · omega
    · omega
    · omega
    · omega
    · obtain rfl : m = n := by omega
      exact Item218Proof.ordG2_ne_card_projSU_four hn (hG.symm.trans (Nat.card_congr e.toEquiv))
    · obtain ⟨k, rfl⟩ := hno
      omega
  · exfalso
    rcases h11 with e | h3
    · exact card_lBar_ne_of_isList218 hL (Or.inl rfl)
        ((Nat.card_congr e.some.toEquiv).trans CFSG.Sporadic.J3.card_J3)
    · exact card_lBar_ne_of_isList218 hL (Or.inr (Or.inl rfl))
        ((card_of_isTripleCover h3).trans (by rw [CFSG.Sporadic.J3.card_J3]))
  · exfalso
    have hc := (CFSG.Timmesfeld.card_statedClassicalModel_two h13).2.2.1 rfl
    rw [show CFSG.Open.ordBC 3 (2 ^ 1) = 1451520 by decide] at hc
    exact card_lBar_ne_of_isList218 hL (Or.inr (Or.inr rfl)) hc

end List

end CFSG.RankThree.PartTwo.Sec21.Item2113Proof
