module

public import CFSG.RankThree.PartTwo.Sec21.Item21EarlyProofJ3
import CFSG.RankThree.PartTwo.KFacts.KS14Orders
import CFSG.Timmesfeld.Orders.Exceptional
import CFSG.RankThree.PartTwo.Sec21.Item229Orders
import CFSG.RankThree.PartTwo.Sec19.Step1911Proof
import CFSG.RankThree.PartTwo.Sec4.T444.Item434SmallTwoOtherU54
import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.X6G2
import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.X6Triality
import CFSG.LieType.Simplicity.Classical
import CFSG.Timmesfeld.Orders.Classical
import CFSG.RankThree.PartTwo.Sec6.Item612Local
public import CFSG.RankThree.PartTwo.Sec21.Item21Early2ProofOrder

public section

namespace CFSG.RankThree.PartTwo.Sec21

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open CFSG.Assembly.RankThreeEven (projSL projSU projSp)
open CFSG.Assembly.LowTwoRank (StatedClassicalModel)
open CFSG.Blueprint

@[expose] def Item217InLLocal : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A E U : Subgroup G) (c : G) (L : Subgroup G),
    Sec21Pair G A E U c L → Nonempty (L ⧸ Subgroup.center L ≃* NativeSporadic.J3) → c ∈ L →
      (Nonempty (lBar L ≃* NativeSporadic.J3) ∨ Sec4.IsTripleCover (lBar L) NativeSporadic.J3) →
      Nat.card A = 3 ^ 4 →
      Sec4.IsExtOf ↥(starOf A L) (Multiplicative (ZMod 8)) (Multiplicative (ZMod 3 × ZMod 3)) →
      IsIrreducibleOn (wStar A) ∧ (∃ t ∈ wStar A, IsTransvectionOn t) ∧
      (∃ P : Sylow 3 (wStar A), ∀ x ∈ (P : Subgroup (wStar A)), (x : MulAut A) ∈ starOf A L) ∧
      ∀ x ∈ starOf A L, ¬ IsTransvectionOn x

@[expose] def Item217NotInLLocal : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A E U : Subgroup G) (c : G) (L : Subgroup G),
    Sec21Pair G A E U c L → Nonempty (L ⧸ Subgroup.center L ≃* NativeSporadic.J3) → c ∉ L →
      (Nonempty (lBar L ≃* NativeSporadic.J3) ∨ Sec4.IsTripleCover (lBar L) NativeSporadic.J3) →
      Nat.card A = 3 ^ 4 →
      Sec4.IsExtOf ↥(starOf A L) (Multiplicative (ZMod 8)) (Multiplicative (ZMod 3 × ZMod 3)) →
      False

namespace Item21Early3Proof

open Item21EarlyProof Item21Early2Proof

theorem nonempty_quot_center_lBar {G : Type} [Group G] [Finite G] {L : Subgroup G}
    [Group.IsPerfect L] {S : Type*} [Group S] (hS : IsSimpleGroup S)
    (e : L ⧸ Subgroup.center L ≃* S) :
    Nonempty (lBar L ⧸ Subgroup.center (lBar L) ≃* S) := by
  obtain ⟨hTs, hTch, -⟩ := solvable_prime_complement_core_characterization (H := L)
    Nat.prime_three
  set T := aschbacherSolvableCore 3 L with hT
  have : T.Normal := Subgroup.normal_of_characteristic T
  have : IsSimpleGroup (L ⧸ Subgroup.center L) := @MulEquiv.isSimpleGroup _ _ _ _ hS e
  have hK₀s : Group.IsSolvable (centerPre T) := isSolvable_centerPre T hTs
  have hle : centerPre T ≤ Subgroup.center L :=
    Sec4.Census.le_of_isSolvable_of_normal inferInstance hK₀s
  have hge : Subgroup.center L ≤ centerPre T := by
    intro z hz
    rw [Subgroup.mem_comap, Subgroup.mem_center_iff]
    intro q
    obtain ⟨l, rfl⟩ := QuotientGroup.mk'_surjective T q
    rw [← map_mul, ← map_mul, (Subgroup.mem_center_iff.mp hz l)]
  have heq : centerPre T = Subgroup.center L := le_antisymm hle hge
  exact ⟨((centerPreEquiv T).symm.trans (QuotientGroup.quotientMulEquivOfEq heq)).trans e⟩

theorem card_quot_center_of_mulEquiv {X S : Type*} [Group X] [Group S]
    (hS : Subgroup.center S = ⊥) (e : X ≃* S) : Nat.card (X ⧸ Subgroup.center X) = Nat.card S :=
  Nat.card_congr (nonempty_quot_of_mulEquiv hS e).some.toEquiv

theorem card_quot_center_of_bot {X : Type*} [Group X] (hZ : Subgroup.center X = ⊥) :
    Nat.card (X ⧸ Subgroup.center X) = Nat.card X :=
  Nat.card_congr (quotCenterEquivOfBot hZ).toEquiv

theorem card_projSL_three_ne_j3 {n : ℕ} (hn : 2 ≤ n) (he : Even n) :
    Nat.card (projSL 3 (GaloisField 2 n)) ≠ 50232960 := by
  intro hY
  have hc := KFacts.KS14.card_projSL_three_mul_gcd (GaloisField 2 n)
  rw [GaloisField.card 2 n (by omega), hY] at hc
  have hg : Nat.gcd 3 (2 ^ n - 1) = 3 :=
    Nat.gcd_eq_left (Nat.dvd_of_mod_eq_zero (by
      have := two_pow_mod_three_of_even he
      have h1 : 1 ≤ 2 ^ n := Nat.one_le_two_pow
      omega))
  rw [hg] at hc
  rcases Nat.lt_or_ge n 4 with hn4 | hn4
  · obtain rfl : n = 2 := by
      obtain ⟨k, rfl⟩ := he
      omega
    norm_num at hc
  · have hq : 16 ≤ 2 ^ n := le_trans (by norm_num) (Nat.pow_le_pow_right (by norm_num) hn4)
    have h1 : 4096 ≤ (2 ^ n) ^ 3 := le_trans (by norm_num) (Nat.pow_le_pow_left hq 3)
    have h2 : 256 ≤ (2 ^ n) ^ 2 := le_trans (by norm_num) (Nat.pow_le_pow_left hq 2)
    have h3 : 255 ≤ (2 ^ n) ^ 2 - 1 := by omega
    have h4 : 4095 ≤ (2 ^ n) ^ 3 - 1 := by omega
    have : 4096 * (255 * 4095) ≤ (2 ^ n) ^ 3 * (((2 ^ n) ^ 2 - 1) * ((2 ^ n) ^ 3 - 1)) :=
      Nat.mul_le_mul h1 (Nat.mul_le_mul h3 h4)
    omega

theorem card_projSU_four_ne_j3 {n : ℕ} (hn : 2 ≤ n) :
    Nat.card (projSU 4 2 n) ≠ 50232960 := by
  rw [card_projSU le_rfl (by omega), ordTwistedA_three_eq (by omega)]
  have hq := four_le_two_pow hn
  have h1 : 4096 ≤ (2 ^ n) ^ 6 := le_trans (by norm_num) (Nat.pow_le_pow_left hq 6)
  have h2 : 16 ≤ (2 ^ n) ^ 2 := le_trans (by norm_num) (Nat.pow_le_pow_left hq 2)
  have h3 : 64 ≤ (2 ^ n) ^ 3 := le_trans (by norm_num) (Nat.pow_le_pow_left hq 3)
  have h4 : 256 ≤ (2 ^ n) ^ 4 := le_trans (by norm_num) (Nat.pow_le_pow_left hq 4)
  have : 4096 * (15 * 65 * 255) ≤ (2 ^ n) ^ 6 *
      (((2 ^ n) ^ 2 - 1) * ((2 ^ n) ^ 3 + 1) * ((2 ^ n) ^ 4 - 1)) :=
    Nat.mul_le_mul h1 (Nat.mul_le_mul (Nat.mul_le_mul (by omega) (by omega)) (by omega))
  omega

theorem card_projSp_two_ne_j3 {n : ℕ} (hn : 2 ≤ n) (he : Even n) :
    Nat.card (projSp 2 (GaloisField 2 n)) ≠ 50232960 := by
  rw [Sec19.Step1911Proof.card_projSp_two (by omega)]
  rcases Nat.lt_or_ge n 4 with hn4 | hn4
  · obtain rfl : n = 2 := by
      obtain ⟨k, rfl⟩ := he
      omega
    norm_num
  · have hq : 16 ≤ 2 ^ n := le_trans (by norm_num) (Nat.pow_le_pow_right (by norm_num) hn4)
    have h1 : 2 ^ 16 ≤ 2 ^ (n * 4) := Nat.pow_le_pow_right (by norm_num) (by omega)
    have h2 : 256 ≤ (2 ^ n) ^ 2 := le_trans (by norm_num) (Nat.pow_le_pow_left hq 2)
    have h3 : 65536 ≤ (2 ^ n) ^ 4 := le_trans (by norm_num) (Nat.pow_le_pow_left hq 4)
    have : 2 ^ 16 * (255 * 65535) ≤ 2 ^ (n * 4) * (((2 ^ n) ^ 2 - 1) * ((2 ^ n) ^ 4 - 1)) :=
      Nat.mul_le_mul h1 (Nat.mul_le_mul (by omega) (by omega))
    omega

theorem ordG2_ne_j3 {n : ℕ} (hn : 2 ≤ n) : CFSG.Open.ordG2 (2 ^ n) ≠ 50232960 := by
  have hq : 4 ≤ 2 ^ n := four_le_two_pow hn
  unfold CFSG.Open.ordG2
  have h1 : 4096 ≤ (2 ^ n) ^ 6 := le_trans (by norm_num) (Nat.pow_le_pow_left hq 6)
  have h2 : 16 ≤ (2 ^ n) ^ 2 := le_trans (by norm_num) (Nat.pow_le_pow_left hq 2)
  have h3 : 4095 ≤ (2 ^ n) ^ 6 - 1 := by omega
  have h4 : 15 ≤ (2 ^ n) ^ 2 - 1 := by omega
  have : 4096 * 4095 * 15 ≤ (2 ^ n) ^ 6 * ((2 ^ n) ^ 6 - 1) * ((2 ^ n) ^ 2 - 1) :=
    Nat.mul_le_mul (Nat.mul_le_mul h1 h3) h4
  omega

theorem ordTrialityD4_ne_j3 {n : ℕ} (hn : 2 ≤ n) :
    CFSG.Open.ordTrialityD4 (2 ^ n) ≠ 50232960 := by
  have hq : 4 ≤ 2 ^ n := four_le_two_pow hn
  unfold CFSG.Open.ordTrialityD4
  have h1 : 4 ^ 12 ≤ (2 ^ n) ^ 12 := Nat.pow_le_pow_left hq 12
  have h6 : 4096 ≤ (2 ^ n) ^ 6 := le_trans (by norm_num) (Nat.pow_le_pow_left hq 6)
  have h2 : 16 ≤ (2 ^ n) ^ 2 := le_trans (by norm_num) (Nat.pow_le_pow_left hq 2)
  have h3 : 1 ≤ (2 ^ n) ^ 8 + (2 ^ n) ^ 4 + 1 := by omega
  have h4 : 4095 ≤ (2 ^ n) ^ 6 - 1 := by omega
  have h5 : 15 ≤ (2 ^ n) ^ 2 - 1 := by omega
  have : 4 ^ 12 * 1 * 4095 * 15 ≤ (2 ^ n) ^ 12 * ((2 ^ n) ^ 8 + (2 ^ n) ^ 4 + 1) *
      ((2 ^ n) ^ 6 - 1) * ((2 ^ n) ^ 2 - 1) :=
    Nat.mul_le_mul (Nat.mul_le_mul (Nat.mul_le_mul h1 h3) h4) h5
  omega

variable {G : Type} [Group G] [Finite G]

theorem case211_eleven_of_card
    {A L : Subgroup G} {c : G} (h : Case211 A c L)
    (hcard : Nat.card (lBar L ⧸ Subgroup.center (lBar L)) = 50232960) :
    (Nonempty (lBar L ≃* NativeSporadic.J3) ∨ Sec4.IsTripleCover (lBar L) NativeSporadic.J3) ∧
      Nat.card A = 3 ^ 4 ∧
      Sec4.IsExtOf ↥(starOf A L) (Multiplicative (ZMod 8)) (Multiplicative (ZMod 3 × ZMod 3)) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  rcases h with ⟨-, hT, -⟩ | ⟨h, -⟩ | ⟨h | h, -⟩ | ⟨h | h, -⟩ | ⟨h, -⟩ |
      ⟨h | h, -⟩ | ⟨⟨n, hn, he, ⟨h, -⟩ | ⟨h, -⟩⟩, -⟩ |
      ⟨⟨n, hn, he, hG | hD⟩, -⟩ | ⟨⟨n, hn, he, h | h⟩ | h, -⟩ |
      ⟨⟨n, hn, hno, h⟩, -⟩ | h11 | ⟨h | h, -⟩ | ⟨h, -⟩
  ·
    obtain ⟨f⟩ := hT.2
    rw [Nat.card_congr f.toEquiv, KFacts.KS14.card_nativeM22] at hcard
    norm_num at hcard
  · obtain ⟨e⟩ := h
    rw [card_quot_center_of_mulEquiv center_nativeM22_eq_bot e,
      KFacts.KS14.card_nativeM22] at hcard
    norm_num at hcard
  · obtain ⟨e⟩ := h
    rw [card_quot_center_of_mulEquiv center_nativeM23_eq_bot e,
      CFSG.Sporadic.Schreier.m23_card] at hcard
    norm_num at hcard
  · obtain ⟨e⟩ := h
    rw [card_quot_center_of_mulEquiv center_nativeHS_eq_bot e, CFSG.Sporadic.HS.card_HS] at hcard
    norm_num at hcard
  · obtain ⟨e⟩ := h
    rw [card_quot_center_of_mulEquiv center_nativeM24_eq_bot e,
      CFSG.Sporadic.Mathieu.card_M24] at hcard
    norm_num at hcard
  · obtain ⟨e⟩ := h
    rw [card_quot_center_of_mulEquiv center_nativeHe_eq_bot e, CFSG.Sporadic.He.card_He] at hcard
    norm_num at hcard
  · obtain ⟨e⟩ := h
    rw [card_quot_center_of_mulEquiv center_nativeJ2_eq_bot e,
      KFacts.KS14.card_nativeJ2] at hcard
    norm_num at hcard
  · obtain ⟨e⟩ := h
    rw [card_quot_center_of_mulEquiv center_nativeRu_eq_bot e, CFSG.Sporadic.Ru.card_Ru] at hcard
    norm_num at hcard
  · obtain ⟨e⟩ := h
    rw [card_quot_center_of_mulEquiv center_nativeJ4_eq_bot e, CFSG.Sporadic.J4.card_J4] at hcard
    norm_num at hcard
  ·
    obtain ⟨e⟩ := h
    have hn2 : 2 ≤ n := by obtain ⟨k, rfl⟩ := he; omega
    rw [card_quot_center_of_mulEquiv (center_projSL_three_eq_bot hn he) e] at hcard
    exact absurd hcard (card_projSL_three_ne_j3 hn2 he)
  ·
    obtain ⟨e⟩ := h
    have hn2 : 2 ≤ n := by obtain ⟨k, rfl⟩ := he; omega
    obtain ⟨f⟩ := nonempty_quot_SL3 n
    rw [Nat.card_congr ((quotCenterCongr e).trans f).toEquiv] at hcard
    exact absurd hcard (card_projSL_three_ne_j3 hn2 he)
  ·
    have hn2 : 2 ≤ n := by obtain ⟨k, rfl⟩ := he; omega
    rw [card_quot_center_of_bot (CFSG.QuasithinUnique.Setup.X6.even_G2_model_two_extensions hG).1,
      CFSG.Timmesfeld.card_chevalleyExceptionalModel_two hG] at hcard
    exact absurd hcard (ordG2_ne_j3 hn2)
  ·
    have hn2 : 2 ≤ n := by obtain ⟨k, rfl⟩ := he; omega
    rw [card_quot_center_of_bot
        (CFSG.QuasithinUnique.Setup.X6.even_triality_model_two_extensions hD).1,
      CFSG.Timmesfeld.card_chevalleyExceptionalModel_two hD] at hcard
    exact absurd hcard (ordTrialityD4_ne_j3 hn2)
  ·
    obtain ⟨e⟩ := h
    have hn2 : 2 ≤ n := by obtain ⟨k, rfl⟩ := he; omega
    rw [card_quot_center_of_mulEquiv (center_projSp_two_eq_bot hn2) e] at hcard
    exact absurd hcard (card_projSp_two_ne_j3 hn2 he)
  ·
    obtain ⟨e⟩ := h
    have hn2 : 2 ≤ n := by obtain ⟨k, rfl⟩ := he; omega
    rw [card_quot_center_of_mulEquiv (center_projSU_four_eq_bot (by omega)) e] at hcard
    exact absurd hcard (card_projSU_four_ne_j3 hn2)
  ·
    obtain ⟨e⟩ := h
    rw [card_quot_center_of_mulEquiv Sec4.Item434SmallTwoOther.U54.center_U54 e,
      Sec4.Item434SmallTwoOther.U54.card_U54] at hcard
    norm_num at hcard
  ·
    obtain ⟨e⟩ := h
    rw [card_quot_center_of_mulEquiv (center_projSU_four_eq_bot (by omega)) e] at hcard
    exact absurd hcard (card_projSU_four_ne_j3 (by omega))
  ·
    exact h11
  ·
    have : IsSimpleGroup (lBar L) :=
      (CFSG.LieType.Simplicity.fam_PSL_simplicity (lBar L) 4 2 1 h).2
    have hc := (CFSG.Timmesfeld.card_statedClassicalModel_two h).1 rfl
    have hZ : Subgroup.center (lBar L) = ⊥ := by
      refine center_eq_bot_of_isSimpleGroup_of_not_prime ?_
      rw [hc, show CFSG.Open.ordA (4 - 1) (2 ^ 1) = 20160 by decide]
      norm_num
    rw [card_quot_center_of_bot hZ, hc,
      show CFSG.Open.ordA (4 - 1) (2 ^ 1) = 20160 by decide] at hcard
    norm_num at hcard
  ·
    have : IsSimpleGroup (lBar L) :=
      (CFSG.LieType.Simplicity.fam_PSL_simplicity (lBar L) 5 2 1 h).2
    have hc := (CFSG.Timmesfeld.card_statedClassicalModel_two h).1 rfl
    have hZ : Subgroup.center (lBar L) = ⊥ := by
      refine center_eq_bot_of_isSimpleGroup_of_not_prime ?_
      rw [hc, show CFSG.Open.ordA (5 - 1) (2 ^ 1) = 9999360 by decide]
      norm_num
    rw [card_quot_center_of_bot hZ, hc,
      show CFSG.Open.ordA (5 - 1) (2 ^ 1) = 9999360 by decide] at hcard
    norm_num at hcard
  ·
    have : IsSimpleGroup (lBar L) :=
      CFSG.ClassicalGroups.Symplectic.isSimpleGroup_of_statedClassicalModel_PSp (lBar L) 3 2 1 h
    have hc := (CFSG.Timmesfeld.card_statedClassicalModel_two h).2.2.1 rfl
    have hZ : Subgroup.center (lBar L) = ⊥ := by
      refine center_eq_bot_of_isSimpleGroup_of_not_prime ?_
      rw [hc, show CFSG.Open.ordBC 3 (2 ^ 1) = 2 ^ 9 * 2835 by decide]
      norm_num
    rw [card_quot_center_of_bot hZ, hc,
      show CFSG.Open.ordBC 3 (2 ^ 1) = 2 ^ 9 * 2835 by decide] at hcard
    norm_num at hcard

theorem case211_eleven_of_j3
    (h211 : Item211) {A E U L : Subgroup G} {c : G}
    (hpair : Sec21Pair G A E U c L) (hJ : Nonempty (L ⧸ Subgroup.center L ≃* NativeSporadic.J3)) :
    (Nonempty (lBar L ≃* NativeSporadic.J3) ∨ Sec4.IsTripleCover (lBar L) NativeSporadic.J3) ∧
      Nat.card A = 3 ^ 4 ∧
      Sec4.IsExtOf ↥(starOf A L) (Multiplicative (ZMod 8)) (Multiplicative (ZMod 3 × ZMod 3)) := by
  obtain ⟨e⟩ := hJ
  have hpairs := mem_lThreeStarPairs_iff.mp hpair.mem_pair
  have hLc : L ∈ thetaComponentsAt 3 c := (lZeroStarAt_subset A c) hpairs.2.2.1
  have hLp : Group.IsPerfect L := Sec6.isPerfect_of_mem_thetaComponentsAt hLc
  obtain ⟨f⟩ := nonempty_quot_center_lBar (L := L) CFSG.Sporadic.J3.isSimpleGroup_J3 e
  refine case211_eleven_of_card (h211 G A E U c L hpair) ?_
  rw [Nat.card_congr f.toEquiv, CFSG.Sporadic.J3.card_J3]

end Item21Early3Proof

open Item21Early3Proof

theorem item217InL_of
    (h211 : Item211) (hloc : Item217InLLocal) : Item217InL := by
  intro G _ _ A E U c L hpair hJ hcL
  obtain ⟨h1, h2, h3⟩ := case211_eleven_of_j3 h211 hpair hJ
  exact ⟨h2, hloc G A E U c L hpair hJ hcL h1 h2 h3⟩

theorem item217NotInL_of
    (h211 : Item211) (hloc : Item217NotInLLocal) :
    Item217NotInL := by
  intro G _ _ A E U c L hpair hJ hcL
  obtain ⟨h1, h2, h3⟩ := case211_eleven_of_j3 h211 hpair hJ
  exact hloc G A E U c L hpair hJ hcL h1 h2 h3

theorem item217_of_items
    (hMcL : KFacts.KP14.SylowTransvectionGL43) (h211 : Item211)
    (hIn : Item217InLLocal) (hOut : Item217NotInLLocal) : Item217 :=
  item217_of hMcL (item217InL_of h211 hIn) (item217NotInL_of h211 hOut)

end CFSG.RankThree.PartTwo.Sec21
