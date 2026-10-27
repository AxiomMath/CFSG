module

public import CFSG.RankThree.PartTwo.Sec21.Item21LateProofOrders
import CFSG.RankThree.PartTwo.Sec21.Item222ProofCases
import CFSG.Timmesfeld.Orders.Exceptional
import CFSG.Timmesfeld.Orders.Classical
import CFSG.RankThree.PartTwo.Sec19.Step1911Proof
import CFSG.RankThree.PartTwo.Sec21.Item211ResProofLStar
public import CFSG.RankThree.PartTwo.Sec21.Item211
public import CFSG.RankThree.PartTwo.Sec21.Item21Statements

public section

namespace CFSG.RankThree.PartTwo.Sec21.Item21LateProof

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo
open CFSG.Assembly.RankThreeEven (projSL projSU projSp)
open CFSG.Blueprint

variable {G : Type} [Group G]

theorem case7_of_lBar_SL3
    (h211 : Item211) [Finite G] {A E U L : Subgroup G} {c : G}
    (hpair : Sec21Pair G A E U c L) {n : ℕ} (eL : lBar L ≃* SL3 n) :
    0 < n ∧ Even n ∧ IsTypeCOnBarSL A L ∧ Nat.card A = 3 ^ 3 ∧
      Nonempty (starOf A L ≃* Equiv.Perm (Fin 3)) := by
  obtain ⟨r, hr, hcard⟩ := card_SL3_eq n
  have hX : Nat.card (lBar L) = 2 ^ (3 * max n 1) * r := by
    rw [Nat.card_congr eL.toEquiv, hcard]
  have two : ∀ {a s : ℕ}, Odd s → Nat.card (lBar L) = 2 ^ a * s → 3 * max n 1 = a :=
    fun hs h => Timmesfeld.Orders.eq_of_two_pow_mul_odd hr hs (hX.symm.trans h)
  have hns : ∀ {Y : Type} [Group Y] [IsSimpleGroup Y], (lBar L ≃* Y) → 0 < n → Even n →
      False := fun e hn he => Item222Proof.false_of_isSimpleGroup_of_mulEquiv_SL3 hn he
    (e.symm.trans eL)
  have hpar : 0 < n ∧ Even n ∨ n = 0 ∨ n % 2 = 1 := by
    rcases Nat.even_or_odd n with he | ho
    · rcases Nat.eq_zero_or_pos n with h0 | hn
      · exact Or.inr (Or.inl h0)
      · exact Or.inl ⟨hn, he⟩
    · exact Or.inr (Or.inr (Nat.odd_iff.mp ho))
  have h3 : n = 3 → Nat.card (lBar L) = 2 ^ 9 * 32193 := fun h => by
    subst h
    rw [Nat.card_congr eL.toEquiv, card_SL3_three]
  have h7 : n = 7 → Nat.card (lBar L) = 2 ^ 21 * 34357624833 := fun h => by
    subst h
    rw [Nat.card_congr eL.toEquiv, card_SL3_seven]
  rcases h211 G A E U c L hpair with ⟨-, hT, -⟩ | ⟨hM, -⟩ | ⟨hM, -⟩ | ⟨hM, -⟩ | ⟨hM, -⟩ |
      ⟨hM, -⟩ | ⟨⟨m, hm, hme, h7c⟩, h27, hS3⟩ | ⟨⟨m, hm, hme, h8⟩, -⟩ | ⟨h9, -⟩ |
      ⟨⟨m, hm, hmo, hM⟩, -⟩ | ⟨hJ, -⟩ | ⟨h12, -⟩ | ⟨hP, -⟩
  ·
    exfalso
    have := two (a := 7) (s := 10395) (by decide)
      (by rw [card_of_isTripleCover hT, card_M22_eq]; norm_num)
    omega
  ·
    exfalso
    obtain ⟨e⟩ := hM
    have := two (a := 7) (s := 3465) (by decide) (by rw [Nat.card_congr e.toEquiv, card_M22_eq])
    omega
  ·
    exfalso
    rcases hM with he | he
    · obtain ⟨e⟩ := he
      have := two (a := 7) (s := 79695) (by decide)
        (by rw [Nat.card_congr e.toEquiv, card_M23_eq])
      omega
    · obtain ⟨e⟩ := he
      have h := two (a := 9) (s := 86625) (by decide)
        (by rw [Nat.card_congr e.toEquiv, card_HS_eq])
      have := (h3 (by omega)).symm.trans (by rw [Nat.card_congr e.toEquiv, card_HS_eq])
      omega
  ·
    exfalso
    rcases hM with he | he
    · obtain ⟨e⟩ := he
      have := two (a := 10) (s := 239085) (by decide)
        (by rw [Nat.card_congr e.toEquiv, card_M24_eq])
      omega
    · obtain ⟨e⟩ := he
      have := two (a := 10) (s := 3935925) (by decide)
        (by rw [Nat.card_congr e.toEquiv, card_He_eq])
      omega
  ·
    exfalso
    obtain ⟨e⟩ := hM
    have := two (a := 7) (s := 4725) (by decide) (by rw [Nat.card_congr e.toEquiv, card_J2_eq])
    omega
  ·
    exfalso
    rcases hM with he | he
    · obtain ⟨e⟩ := he
      have := two (a := 14) (s := 8906625) (by decide)
        (by rw [Nat.card_congr e.toEquiv, card_Ru_eq])
      omega
    · obtain ⟨e⟩ := he
      have h := two (a := 21) (s := 41377816699065) (by decide)
        (by rw [Nat.card_congr e.toEquiv, card_J4_eq])
      have := (h7 (by omega)).symm.trans (by rw [Nat.card_congr e.toEquiv, card_J4_eq])
      omega
  ·
    rcases h7c with ⟨⟨e⟩, -⟩ | ⟨⟨e⟩, hC⟩
    ·
      exfalso
      obtain ⟨r', hr', hc'⟩ := card_projSL3_eq m
      have h := two hr' (by rw [Nat.card_congr e.toEquiv, hc'])
      have hnm : n = m := by obtain ⟨k, hk⟩ := hme; omega
      have := Item222Proof.isSimpleGroup_projSL_three (GaloisField 2 m)
      exact hns e (by omega) (hnm ▸ hme)
    ·
      obtain ⟨r', hr', hc'⟩ := card_SL3_eq m
      have h := two hr' (by rw [Nat.card_congr e.toEquiv, hc'])
      have hnm : n = m := by obtain ⟨k, hk⟩ := hme; omega
      exact ⟨by omega, hnm ▸ hme, hC, h27, hS3⟩
  ·
    exfalso
    rcases h8 with hG | hD
    · obtain ⟨r', hr', hc'⟩ := (Timmesfeld.Orders.profile_ordG2 (f := m) hm).two
      have hcG : Nat.card (lBar L) = CFSG.Open.ordG2 (2 ^ m) :=
        CFSG.Timmesfeld.card_chevalleyExceptionalModel_two hG
      have h := two hr' (by rw [hcG, hc'])
      have hn2 : n = 2 * m := by omega
      apply card_SL3_ne_ordG2 hm
      rw [← hcG, Nat.card_congr eL.toEquiv, hn2, SL3, Sec19.Step1911Proof.card_SL3 (by omega)]
    · obtain ⟨r', hr', hc'⟩ := (Timmesfeld.Orders.profile_ordTrialityD4 (f := m) hm).two
      have hcD : Nat.card (lBar L) = CFSG.Open.ordTrialityD4 (2 ^ m) :=
        CFSG.Timmesfeld.card_chevalleyExceptionalModel_two hD
      have h := two hr' (by rw [hcD, hc'])
      have hn1 : 1 ≤ n := by omega
      refine Sec19.Step1911Proof.false_of_SL3 hn1 (one_dvd 3) ?_ Nat.prime_two hm hcD
      rw [mul_one, Nat.card_congr eL.toEquiv, SL3, Sec19.Step1911Proof.card_SL3 hn1]
  ·
    exfalso
    rcases h9 with ⟨m, hm, hme, he | he⟩ | he
    · obtain ⟨e⟩ := he
      obtain ⟨r', hr', hc'⟩ := card_projSp2_eq hm
      have h := two hr' (by rw [Nat.card_congr e.toEquiv, hc'])
      have hm2 : 2 ≤ m := by obtain ⟨k, hk⟩ := hme; omega
      have := isSimpleGroup_projSp_two hm2
      rcases hpar with ⟨hn, he⟩ | hp
      · exact hns e hn he
      · omega
    · obtain ⟨e⟩ := he
      obtain ⟨r', hr', hc'⟩ := card_projSU4_eq hm
      have h := two hr' (by rw [Nat.card_congr e.toEquiv, hc'])
      have := isSimpleGroup_projSU (m := 4) (n := m) le_rfl hm
      rcases hpar with ⟨hn, he⟩ | hp
      · exact hns e hn he
      · omega
    · obtain ⟨e⟩ := he
      have := two (a := 20) (s := 50968125) (by decide)
        (by rw [Nat.card_congr e.toEquiv, card_U54_eq])
      omega
  ·
    exfalso
    obtain ⟨e⟩ := hM
    obtain ⟨r', hr', hc'⟩ := card_projSU4_eq (by omega : 1 ≤ m)
    have h := two hr' (by rw [Nat.card_congr e.toEquiv, hc'])
    have := isSimpleGroup_projSU (m := 4) (n := m) le_rfl (by omega)
    rcases hpar with ⟨hn, he⟩ | hp
    · exact hns e hn he
    · omega
  ·
    exfalso
    rcases hJ with he | hT
    · obtain ⟨e⟩ := he
      have := two (a := 7) (s := 392445) (by decide)
        (by rw [Nat.card_congr e.toEquiv, card_J3_eq])
      omega
    · have := two (a := 7) (s := 1177335) (by decide)
        (by rw [card_of_isTripleCover hT, card_J3_eq]; norm_num)
      omega
  ·
    exfalso
    rcases h12 with hP | hP
    · have h := two (a := 6) (s := 315) (by decide) ((card_PSL_two_eq hP).1 rfl)
      have hn2 : n = 2 := by omega
      subst hn2
      exact Item222Proof.false_of_statedClassicalModel_PSL_of_mulEquiv_SL3 hP (by norm_num)
        even_two eL
    · have := two (a := 10) (s := 9765) (by decide) ((card_PSL_two_eq hP).2 rfl)
      omega
  ·
    exfalso
    have h := two (a := 9) (s := 2835) (by decide) (card_PSp_three_two_eq hP)
    have := (h3 (by omega)).symm.trans (card_PSp_three_two_eq hP)
    omega

theorem case7_of_lBar_L3
    (h211 : Item211) (h2116 : Item2116) [Finite G]
    {A E U L : Subgroup G} {c : G} (hpair : Sec21Pair G A E U c L) {n : ℕ}
    (eL : lBar L ≃* projSL 3 (GaloisField 2 n)) :
    0 < n ∧ Even n ∧ Sec4.IsTypeCOn A L ∧ Nat.card A = 3 ^ 3 ∧
      Nonempty (starOf A L ≃* Equiv.Perm (Fin 3)) := by
  obtain ⟨r, hr, hcard⟩ := card_projSL3_eq n
  have hX : Nat.card (lBar L) = 2 ^ (3 * max n 1) * r := by
    rw [Nat.card_congr eL.toEquiv, hcard]
  have two : ∀ {a s : ℕ}, Odd s → Nat.card (lBar L) = 2 ^ a * s → 3 * max n 1 = a :=
    fun hs h => Timmesfeld.Orders.eq_of_two_pow_mul_odd hr hs (hX.symm.trans h)
  have := Item222Proof.isSimpleGroup_projSL_three (GaloisField 2 n)
  have hsimp : IsSimpleGroup (lBar L) := eL.isSimpleGroup
  have h3 : n = 3 → Nat.card (lBar L) = 2 ^ 9 * 32193 := fun h => by
    subst h
    rw [Nat.card_congr eL.toEquiv, card_projSL3_eq_card_SL3 (by norm_num) (by decide),
      card_SL3_three]
  have h7 : n = 7 → Nat.card (lBar L) = 2 ^ 21 * 34357624833 := fun h => by
    subst h
    rw [Nat.card_congr eL.toEquiv, card_projSL3_eq_card_SL3 (by norm_num) (by decide),
      card_SL3_seven]
  have hA : 1 ≤ n → Nat.card (lBar L) = CFSG.Open.ordA 2 (2 ^ n) := fun hn => by
    rw [Nat.card_congr eL.toEquiv, Sec19.Step1911Proof.card_projSL (by norm_num) hn]
  rcases h211 G A E U c L hpair with ⟨-, hT, -⟩ | ⟨hM, -⟩ | ⟨hM, -⟩ | ⟨hM, -⟩ | ⟨hM, -⟩ |
      ⟨hM, -⟩ | ⟨⟨m, hm, hme, h7c⟩, h27, hS3⟩ | ⟨⟨m, hm, hme, h8⟩, -⟩ | ⟨h9, -⟩ |
      ⟨⟨m, hm, hmo, hM⟩, -⟩ | ⟨hJ, -⟩ | ⟨h12, -⟩ | ⟨hP, -⟩
  ·
    exfalso
    have := two (a := 7) (s := 10395) (by decide)
      (by rw [card_of_isTripleCover hT, card_M22_eq]; norm_num)
    omega
  ·
    exfalso
    obtain ⟨e⟩ := hM
    have := two (a := 7) (s := 3465) (by decide) (by rw [Nat.card_congr e.toEquiv, card_M22_eq])
    omega
  ·
    exfalso
    rcases hM with he | he
    · obtain ⟨e⟩ := he
      have := two (a := 7) (s := 79695) (by decide)
        (by rw [Nat.card_congr e.toEquiv, card_M23_eq])
      omega
    · obtain ⟨e⟩ := he
      have h := two (a := 9) (s := 86625) (by decide)
        (by rw [Nat.card_congr e.toEquiv, card_HS_eq])
      have := (h3 (by omega)).symm.trans (by rw [Nat.card_congr e.toEquiv, card_HS_eq])
      omega
  ·
    exfalso
    rcases hM with he | he
    · obtain ⟨e⟩ := he
      have := two (a := 10) (s := 239085) (by decide)
        (by rw [Nat.card_congr e.toEquiv, card_M24_eq])
      omega
    · obtain ⟨e⟩ := he
      have := two (a := 10) (s := 3935925) (by decide)
        (by rw [Nat.card_congr e.toEquiv, card_He_eq])
      omega
  ·
    exfalso
    obtain ⟨e⟩ := hM
    have := two (a := 7) (s := 4725) (by decide) (by rw [Nat.card_congr e.toEquiv, card_J2_eq])
    omega
  ·
    exfalso
    rcases hM with he | he
    · obtain ⟨e⟩ := he
      have := two (a := 14) (s := 8906625) (by decide)
        (by rw [Nat.card_congr e.toEquiv, card_Ru_eq])
      omega
    · obtain ⟨e⟩ := he
      have h := two (a := 21) (s := 41377816699065) (by decide)
        (by rw [Nat.card_congr e.toEquiv, card_J4_eq])
      have := (h7 (by omega)).symm.trans (by rw [Nat.card_congr e.toEquiv, card_J4_eq])
      omega
  ·
    rcases h7c with ⟨⟨e⟩, hC⟩ | ⟨⟨e⟩, -⟩
    ·
      obtain ⟨r', hr', hc'⟩ := card_projSL3_eq m
      have h := two hr' (by rw [Nat.card_congr e.toEquiv, hc'])
      have hnm : n = m := by obtain ⟨k, hk⟩ := hme; omega
      exact ⟨by omega, hnm ▸ hme, hC, h27, hS3⟩
    ·
      exact (Item222Proof.false_of_isSimpleGroup_of_mulEquiv_SL3 hm hme e).elim
  ·
    exfalso
    rcases h8 with hG | hD
    · obtain ⟨r', hr', hc'⟩ := (Timmesfeld.Orders.profile_ordG2 (f := m) hm).two
      have hcG : Nat.card (lBar L) = CFSG.Open.ordG2 (2 ^ m) :=
        CFSG.Timmesfeld.card_chevalleyExceptionalModel_two hG
      have h := two hr' (by rw [hcG, hc'])
      have hn2 : n = 2 * m := by omega
      have hlt := three_mul_ordG2_lt hm
      have hg := Sec19.Step1911Proof.ordA_two_mul_gcd n
      have hg3 : Nat.gcd 3 (2 ^ n - 1) = 3 :=
        Nat.gcd_eq_left (three_dvd_two_pow_sub_one ⟨m, by omega⟩)
      rw [hg3, ← hA (by omega), hcG, hn2] at hg
      omega
    · obtain ⟨r', hr', hc'⟩ := (Timmesfeld.Orders.profile_ordTrialityD4 (f := m) hm).two
      have hcD : Nat.card (lBar L) = CFSG.Open.ordTrialityD4 (2 ^ m) :=
        CFSG.Timmesfeld.card_chevalleyExceptionalModel_two hD
      have h := two hr' (by rw [hcD, hc'])
      have hn1 : 1 ≤ n := by omega
      refine Sec19.Step1911Proof.false_of_SL3 hn1 (Nat.gcd_dvd_left 3 (2 ^ n - 1)) ?_
        Nat.prime_two hm hcD
      rw [hA hn1, Sec19.Step1911Proof.ordA_two_mul_gcd]
  ·
    exfalso
    rcases h9 with ⟨m, hm, hme, he | he⟩ | he
    · obtain ⟨e⟩ := he
      obtain ⟨r', hr', hc'⟩ := card_projSp2_eq hm
      have h := two hr' (by rw [Nat.card_congr e.toEquiv, hc'])
      have hn1 : 1 ≤ n := by omega
      refine Timmesfeld.Orders.ordA_ne_ordBC_two (n := 2) (f := n) (g := m) (by norm_num) hn1 hm ?_
      rw [← hA hn1, Nat.card_congr e.toEquiv, Sec19.Step1911Proof.card_projSp_two hm,
        ordBC_two_eq hm, ← pow_mul 2 m 4]
    · obtain ⟨e⟩ := he
      obtain ⟨r', hr', hc'⟩ := card_projSU4_eq hm
      have h := two hr' (by rw [Nat.card_congr e.toEquiv, hc'])
      have hn1 : 1 ≤ n := by omega
      refine Timmesfeld.Orders.ordA_ne_ordTwistedA (n := 2) (f := n) (u := 3) (g := m)
        (by norm_num) hn1 (by norm_num) hm ?_
      rw [← hA hn1, Nat.card_congr e.toEquiv, card_projSU le_rfl hm]
    · obtain ⟨e⟩ := he
      have h := two (a := 20) (s := 50968125) (by decide)
        (by rw [Nat.card_congr e.toEquiv, card_U54_eq])
      omega
  ·
    exfalso
    obtain ⟨e⟩ := hM
    obtain ⟨r', hr', hc'⟩ := card_projSU4_eq (by omega : 1 ≤ m)
    have h := two hr' (by rw [Nat.card_congr e.toEquiv, hc'])
    have hn1 : 1 ≤ n := by omega
    refine Timmesfeld.Orders.ordA_ne_ordTwistedA (n := 2) (f := n) (u := 3) (g := m)
      (by norm_num) hn1 (by norm_num) (by omega) ?_
    rw [← hA hn1, Nat.card_congr e.toEquiv, card_projSU le_rfl (by omega)]
  ·
    exfalso
    rcases hJ with he | hT
    · obtain ⟨e⟩ := he
      have := two (a := 7) (s := 392445) (by decide)
        (by rw [Nat.card_congr e.toEquiv, card_J3_eq])
      omega
    · have := two (a := 7) (s := 1177335) (by decide)
        (by rw [card_of_isTripleCover hT, card_J3_eq]; norm_num)
      omega
  ·
    exact (h2116 G A E U c L hpair (h12.elim Or.inl fun h => Or.inr (Or.inl h))).elim
  ·
    exact (h2116 G A E U c L hpair (Or.inr (Or.inr hP))).elim

theorem false_of_projSU4_odd
    (h211 : Item211) [Finite G] {A E U L : Subgroup G} {c : G}
    (hpair : Sec21Pair G A E U c L) (h27 : Nat.card A = 3 ^ 3) {n : ℕ} (hno : Odd n)
    (eL : L ≃* projSU 4 2 n) : False := by
  have hn1 : 1 ≤ n := hno.pos
  have hn2 : n % 2 = 1 := Nat.odd_iff.mp hno
  have hpairs := mem_lThreeStarPairs_iff.mp hpair.mem_pair
  have hLc : L ∈ thetaComponentsAt 3 c := (lZeroStarAt_subset A c) hpairs.2.2.1
  have hLp : Group.IsPerfect L := Sec6.isPerfect_of_mem_thetaComponentsAt hLc
  have := isSimpleGroup_projSU (m := 4) (n := n) le_rfl hn1
  have eθ := mulEquiv_lBar_of_theta_eq_bot (inSubgroup_theta_eq_bot_of_mulEquiv hLp eL)
  set eX : lBar L ≃* projSU 4 2 n := eθ.symm.trans eL with heX
  have hsimp : IsSimpleGroup (lBar L) := eX.isSimpleGroup
  obtain ⟨r, hr, hcard⟩ := card_projSU4_eq hn1
  have hX : Nat.card (lBar L) = 2 ^ (6 * n) * r := by rw [Nat.card_congr eX.toEquiv, hcard]
  have two : ∀ {a s : ℕ}, Odd s → Nat.card (lBar L) = 2 ^ a * s → 6 * n = a :=
    fun hs h => Timmesfeld.Orders.eq_of_two_pow_mul_odd hr hs (hX.symm.trans h)
  have hU : Nat.card (lBar L) = CFSG.Open.ordTwistedA 3 (2 ^ n) := by
    rw [Nat.card_congr eX.toEquiv, card_projSU le_rfl hn1]
  rcases h211 G A E U c L hpair with ⟨-, hT, -⟩ | ⟨hM, -⟩ | ⟨hM, -⟩ | ⟨hM, -⟩ | ⟨hM, -⟩ |
      ⟨hM, -⟩ | ⟨⟨m, hm, hme, h7c⟩, -, -⟩ | ⟨⟨m, hm, hme, h8⟩, -⟩ | ⟨h9, -⟩ |
      ⟨-, h81, -⟩ | ⟨-, h81, -⟩ | ⟨h12, -⟩ | ⟨-, h81, -⟩
  ·
    have := two (a := 7) (s := 10395) (by decide)
      (by rw [card_of_isTripleCover hT, card_M22_eq]; norm_num)
    omega
  ·
    obtain ⟨e⟩ := hM
    have := two (a := 7) (s := 3465) (by decide) (by rw [Nat.card_congr e.toEquiv, card_M22_eq])
    omega
  ·
    rcases hM with he | he
    · obtain ⟨e⟩ := he
      have := two (a := 7) (s := 79695) (by decide)
        (by rw [Nat.card_congr e.toEquiv, card_M23_eq])
      omega
    · obtain ⟨e⟩ := he
      have := two (a := 9) (s := 86625) (by decide)
        (by rw [Nat.card_congr e.toEquiv, card_HS_eq])
      omega
  ·
    rcases hM with he | he
    · obtain ⟨e⟩ := he
      have := two (a := 10) (s := 239085) (by decide)
        (by rw [Nat.card_congr e.toEquiv, card_M24_eq])
      omega
    · obtain ⟨e⟩ := he
      have := two (a := 10) (s := 3935925) (by decide)
        (by rw [Nat.card_congr e.toEquiv, card_He_eq])
      omega
  ·
    obtain ⟨e⟩ := hM
    have := two (a := 7) (s := 4725) (by decide) (by rw [Nat.card_congr e.toEquiv, card_J2_eq])
    omega
  ·
    rcases hM with he | he
    · obtain ⟨e⟩ := he
      have := two (a := 14) (s := 8906625) (by decide)
        (by rw [Nat.card_congr e.toEquiv, card_Ru_eq])
      omega
    · obtain ⟨e⟩ := he
      have := two (a := 21) (s := 41377816699065) (by decide)
        (by rw [Nat.card_congr e.toEquiv, card_J4_eq])
      omega
  ·
    rcases h7c with ⟨⟨e⟩, -⟩ | ⟨⟨e⟩, -⟩
    · refine Timmesfeld.Orders.ordA_ne_ordTwistedA (n := 2) (f := m) (u := 3) (g := n)
        (by norm_num) hm (by norm_num) hn1 ?_
      rw [← hU, Nat.card_congr e.toEquiv, Sec19.Step1911Proof.card_projSL (by norm_num) hm]
    · exact Item222Proof.false_of_isSimpleGroup_of_mulEquiv_SL3 hm hme e
  ·
    have hm2 : 2 ≤ m := by obtain ⟨k, hk⟩ := hme; omega
    rcases h8 with hG | hD
    · refine Timmesfeld.Orders.ordG2_ne_ordTwistedA (f := m) (u := 3) (g := n) hm2
        (by norm_num) hn1 ?_
      rw [← hU, CFSG.Timmesfeld.card_chevalleyExceptionalModel_two hG]
    · refine Timmesfeld.Orders.ordTrialityD4_ne_ordTwistedA (f := m) (u := 3) (g := n) hm
        (by norm_num) hn1 ?_
      rw [← hU, CFSG.Timmesfeld.card_chevalleyExceptionalModel_two hD]
  ·
    rcases h9 with ⟨m, hm, hme, he | he⟩ | he
    · obtain ⟨e⟩ := he
      have hm2 : 2 ≤ m := by obtain ⟨k, hk⟩ := hme; omega
      exact (not_mulEquiv_projSp_two_projSU_four hm2 hn1).false (e.symm.trans eX)
    · obtain ⟨e⟩ := he
      have hnm := eq_of_mulEquiv_projSU_four hn1 hm (eX.symm.trans e)
      obtain ⟨k, hk⟩ := hme
      omega
    · obtain ⟨e⟩ := he
      have := two (a := 20) (s := 50968125) (by decide)
        (by rw [Nat.card_congr e.toEquiv, card_U54_eq])
      omega
  ·
    rw [h27] at h81
    norm_num at h81
  ·
    rw [h27] at h81
    norm_num at h81
  ·
    rcases h12 with hP | hP
    · refine Timmesfeld.Orders.ordA_ne_ordTwistedA (n := 3) (f := 1) (u := 3) (g := n)
        (by norm_num) le_rfl (by norm_num) hn1 ?_
      rw [← hU, (CFSG.Timmesfeld.card_statedClassicalModel_two hP).1 rfl]
    · refine Timmesfeld.Orders.ordA_ne_ordTwistedA (n := 4) (f := 1) (u := 3) (g := n)
        (by norm_num) le_rfl (by norm_num) hn1 ?_
      rw [← hU, (CFSG.Timmesfeld.card_statedClassicalModel_two hP).1 rfl]
  ·
    rw [h27] at h81
    norm_num at h81

theorem case10_of_lt_card (h211 : Item211) (h213 : Item213)
    (h217 : Item217) (h2116 : Item2116) [Finite G] {A E U L : Subgroup G} {c : G}
    (hpair : Sec21Pair G A E U c L) (hA : 27 < Nat.card A) :
    (∃ n : ℕ, 1 < n ∧ Odd n ∧ Nonempty (lBar L ≃* projSU 4 2 n)) ∧ Nat.card A = 3 ^ 4 ∧
      Nonempty (starOf A L ≃* Equiv.Perm (Fin 4)) := by
  rcases h211 G A E U c L hpair with ⟨-, -, h27, -⟩ | ⟨-, h27, -⟩ | ⟨-, h27, -⟩ |
      ⟨-, h27, -⟩ | ⟨-, h27, -⟩ | ⟨-, h27, -⟩ | ⟨-, h27, -⟩ | ⟨-, h27, -⟩ | ⟨-, h27, -⟩ |
      h10 | ⟨hJ, -⟩ | ⟨-, h27, -⟩ | ⟨hP, -⟩
  all_goals first
    | (exfalso; rw [h27] at hA; norm_num at hA)
    | skip
  · exact h10
  · exact (false_of_J3 (h213 G A E U c L hpair) (h217 G A E U c L hpair) hJ).elim
  · exact (h2116 G A E U c L hpair (Or.inr (Or.inr hP))).elim

end CFSG.RankThree.PartTwo.Sec21.Item21LateProof
