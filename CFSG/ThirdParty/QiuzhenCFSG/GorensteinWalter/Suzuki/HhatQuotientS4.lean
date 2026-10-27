module

public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.MinimalCounterexample
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section2.Theorem26
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section3.FirstCaseCountData
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section3.FirstCaseOrderInfra
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.PGL2Cardinality
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.LinearThreeEquiv
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Classification
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Suzuki.SylowThreeCount
import Mathlib.Tactic

namespace CFSG
end CFSG
open CFSG

noncomputable section

namespace CFSG.GorensteinWalter

universe u

open scoped Pointwise

private lemma hhat_card_72
    {G : Type u} [Group G] [Finite G]
    (hmin : IsMinimalCounterexample G)
    (c : CentralizerSetup G)
    (hfirst : FirstCase c)
    (hklein : IsKleinFour (pCore 2 c.Hhat))
    (hU3 : Nat.card c.U = 3) :
    Nat.card (↥c.Hhat) = 72 := by
  have hHcard : Nat.card c.H = 8 * Nat.card c.U :=
    firstCase_H_card_eq_eight_mul_U hmin c hfirst hklein
  have hidx : c.H.index = 3 * c.Hhat.index :=
    firstCase_H_index_eq_three_mul_Hhat_index hmin c hfirst hklein
  have hm := c.H.card_mul_index
  have hmhat := c.Hhat.card_mul_index
  have hpos : 0 < c.Hhat.index := by
    rw [Subgroup.index_eq_card]
    exact Nat.card_pos
  have hhat_eq : Nat.card c.Hhat = 3 * Nat.card c.H := by
    apply Nat.eq_of_mul_eq_mul_right hpos
    calc
      Nat.card c.Hhat * c.Hhat.index = Nat.card G := hmhat
      _ = Nat.card c.H * c.H.index := hm.symm
      _ = Nat.card c.H * (3 * c.Hhat.index) := by rw [hidx]
      _ = (3 * Nat.card c.H) * c.Hhat.index := by ring
  rw [hhat_eq, hHcard, hU3]

private lemma two_dvd_q_sq_sub_one (q : ℕ) (hqodd : Odd q) : 2 ∣ q ^ 2 - 1 := by
  rw [← even_iff_two_dvd]
  exact Nat.Odd.sub_odd (Odd.pow hqodd) (by norm_num)

private lemma odd_prime_power_ge_three
    (q : ℕ) (hq : IsOddPrimePower q) : 3 ≤ q := by
  rcases hq with ⟨p, n, hp, hpOdd, hn1, hqcard⟩
  have hp3 : 3 ≤ p := by
    have hp2 : 2 ≤ p := hp.two_le
    rcases hpOdd with ⟨k, hk⟩
    omega
  have hple : p ≤ p ^ n := by
    have hpos : 0 < p := hp.pos
    have hd : p ∣ p ^ n := ⟨p ^ (n - 1), by
      rw [← pow_succ', Nat.sub_add_cancel hn1]⟩
    exact Nat.le_of_dvd (pow_pos hp.pos n) hd
  omega

private lemma odd_prime_power_three_or_ge_five
    (q : ℕ) (hq : IsOddPrimePower q) (hq3 : q ≠ 3) : 5 ≤ q := by
  have hge3 : 3 ≤ q := odd_prime_power_ge_three q hq
  have hodd : Odd q := by
    rcases hq with ⟨p, n, hp, hpOdd, hn1, hqcard⟩
    rw [hqcard]
    exact hpOdd.pow
  rcases hodd with ⟨k, hk⟩
  omega

private lemma odd_dvd_of_two_pow_mul
    {q : ℕ} (hqodd : Odd q) (n m : ℕ) (h : q ∣ 2 ^ n * m) : q ∣ m := by
  have hcop : q.Coprime 2 := (Nat.coprime_two_right).mpr hqodd
  induction n with
  | zero => simpa using h
  | succ n ih =>
      have h2 : q ∣ 2 * (2 ^ n * m) := by
        convert h using 1
        rw [pow_succ]
        ring
      exact ih (hcop.dvd_of_dvd_mul_left h2)

/-- `Ĥ / O₂'(Ĥ)` is the symmetric group on four letters: `Ĥ` is a proper
subgroup of the minimal counterexample, hence a D-group; with
`O₂'(Ĥ) = U` and `|Ĥ| = 72` the D-group cases force the linear case
`PGL₂(3) ≅ S₄`. -/
private theorem firstCase_hhat_quotient_U_s4_of_U3
    {G : Type u} [Group G] [Finite G]
    (hmin : IsMinimalCounterexample G)
    (c : CentralizerSetup G) (hfirst : FirstCase c)
    (hklein : IsKleinFour (pCore 2 c.Hhat))
    (hU3 : Nat.card c.U = 3) :
    Nonempty ((c.Hhat ⧸ pPrimeCore 2 c.Hhat) ≃* Equiv.Perm (Fin 4)) := by
  classical
  let Q : Type u := c.Hhat ⧸ pPrimeCore 2 c.Hhat
  have hDG : IsDGroup (↥c.Hhat) :=
    properSubgroups_areDGroups hmin c.Hhat c.Hhat_maximal.ne_top
  have hUeq : c.U = oddCoreOf c.Hhat := (theorem_2_6 hmin c).1
  have hP2card : Nat.card (pPrimeCore 2 c.Hhat) = 3 := by
    have hmap : Nat.card ((pPrimeCore 2 c.Hhat).map c.Hhat.subtype) =
        Nat.card (pPrimeCore 2 c.Hhat) := by
      exact (Nat.card_congr (Subgroup.equivMapOfInjective (pPrimeCore 2 c.Hhat)
        c.Hhat.subtype c.Hhat.subtype_injective).toEquiv).symm
    have hmapU : (pPrimeCore 2 c.Hhat).map c.Hhat.subtype = c.U := by
      rw [hUeq]
      rfl
    rw [hmapU] at hmap
    exact hmap.symm.trans hU3
  have hQcard : Nat.card Q = 24 := by
    have hm := (pPrimeCore 2 c.Hhat).index_mul_card
    change (pPrimeCore 2 c.Hhat).index * Nat.card (pPrimeCore 2 c.Hhat) =
      Nat.card (↥c.Hhat) at hm
    rw [hP2card, hhat_card_72 hmin c hfirst hklein hU3] at hm
    have hindex : (pPrimeCore 2 c.Hhat).index = 24 := by
      rw [mul_comm] at hm
      exact Nat.eq_of_mul_eq_mul_left (by norm_num : 0 < 3) (by simpa using hm)
    change Nat.card Q = 24
    rw [← Subgroup.index_eq_card]
    exact hindex
  rcases hDG with ⟨_hSylow2, h2⟩ | ⟨_hSylow7, e⟩ |
    ⟨_hSylowL, K, hKpp, L, _hLnormal, hLindex, hLmodel⟩
  · have h3dvd : 3 ∣ Nat.card Q := by
      rw [hQcard]
      norm_num
    have h2pow : ∃ n : ℕ, Nat.card Q = 2 ^ n := by
      let : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
      exact (IsPGroup.iff_card.mp h2)
    rcases h2pow with ⟨n, hn⟩
    have h3dvd2 : 3 ∣ 2 ^ n := by
      rw [hn] at h3dvd
      exact h3dvd
    have h32 : 3 ∣ 2 := (Nat.Prime.dvd_of_dvd_pow Nat.prime_three h3dvd2)
    norm_num at h32
  · have h7 : Nat.card Q = 2520 := by
      change Nat.card (↥c.Hhat ⧸ pPrimeCore 2 c.Hhat) = 2520
      exact (Nat.card_congr e.some.toEquiv).trans (by
        rw [nat_card_alternatingGroup, Nat.card_eq_fintype_card]
        decide)
    omega
  · have hLidxmul : L.index * Nat.card ↥L = Nat.card Q := L.index_mul_card
    rw [hQcard] at hLidxmul
    have hLdvd : L.index ∣ 24 := ⟨Nat.card ↥L, hLidxmul.symm⟩
    have hLidx_cases : L.index = 1 ∨ L.index = 3 := by
      have hodd : Odd L.index := hLindex
      have hcop : L.index.Coprime 2 := (Nat.coprime_two_right).mpr hodd
      have hLdvd3 : L.index ∣ 3 := by
        have hd24 : L.index ∣ 2 * (2 * (2 * 3)) := by
          simpa using hLdvd
        have hLdvd12 : L.index ∣ 2 * (2 * 3) := hcop.dvd_of_dvd_mul_left hd24
        have hLdvd6 : L.index ∣ 2 * 3 := hcop.dvd_of_dvd_mul_left hLdvd12
        exact hcop.dvd_of_dvd_mul_left hLdvd6
      have hlt : L.index ≤ 3 := Nat.le_of_dvd (by norm_num : 0 < 3) hLdvd3
      have hne0 : L.index ≠ 0 := by
        intro h0
        rw [h0] at hLidxmul
        norm_num at hLidxmul
      interval_cases L.index
      · norm_num at hLdvd3
      · norm_num
      · norm_num at hLdvd3
      · norm_num
    rcases hLidx_cases with hL1 | hL3
    · have hLtop : L = ⊤ := Subgroup.index_eq_one.mp hL1
      have hLcard : Nat.card ↥L = 24 := by
        rw [hLtop]
        change Nat.card (⊤ : Subgroup Q) = 24
        exact (Nat.card_congr (Subgroup.topEquiv (G := Q)).toEquiv).trans hQcard
      rcases hLmodel with hPSL | hPGL
      · rcases hPSL with ⟨eL⟩
        have hcardL' : Nat.card (PSL2 K) = 24 :=
          (Nat.card_congr eL.toEquiv).symm.trans hLcard
        have hq : Nat.card K * (Nat.card K ^ 2 - 1) = 48 := by
          rw [psl2_card_formula K hKpp] at hcardL'
          have h2dvd : 2 ∣ Nat.card K * (Nat.card K ^ 2 - 1) := by
            exact dvd_mul_of_dvd_right (two_dvd_q_sq_sub_one (Nat.card K) (by
              rcases hKpp with ⟨p, n, hp, hpOdd, hn1, hqcard⟩
              rw [hqcard]
              exact hpOdd.pow)) (Nat.card K)
          exact Nat.eq_mul_of_div_eq_right h2dvd hcardL'
        have hqodd : Odd (Nat.card K) := by
          rcases hKpp with ⟨p, n, hp, hpOdd, hn1, hqcard⟩
          rw [hqcard]
          exact hpOdd.pow
        have hq3 : Nat.card K ≠ 3 := by
          intro h3
          rw [h3] at hq
          norm_num at hq
        have hq5 : 5 ≤ Nat.card K :=
          odd_prime_power_three_or_ge_five (Nat.card K) hKpp hq3
        have hqdiv : Nat.card K ∣ 48 := ⟨Nat.card K ^ 2 - 1, hq.symm⟩
        have hq3dvd : Nat.card K ∣ 3 :=
          odd_dvd_of_two_pow_mul hqodd 4 3 (by simpa using hqdiv)
        have hqle3 : Nat.card K ≤ 3 :=
          Nat.le_of_dvd (by norm_num : 0 < 3) hq3dvd
        omega
      · rcases hPGL with ⟨eL⟩
        have hcardL' : Nat.card (PGL2 K) = 24 :=
          (Nat.card_congr eL.toEquiv).symm.trans hLcard
        have hq : Nat.card K * (Nat.card K ^ 2 - 1) = 24 := by
          rw [pgl2_card_formula K] at hcardL'
          exact hcardL'
        have hqdiv : Nat.card K ∣ 24 := ⟨Nat.card K ^ 2 - 1, hq.symm⟩
        have hqodd : Odd (Nat.card K) := by
          rcases hKpp with ⟨p, n, hp, hpOdd, hn1, hqcard⟩
          rw [hqcard]
          exact hpOdd.pow
        have hq3 : Nat.card K = 3 := by
          have hq3dvd : Nat.card K ∣ 3 :=
            odd_dvd_of_two_pow_mul hqodd 3 3 (by simpa using hqdiv)
          have hqle3 : Nat.card K ≤ 3 :=
            Nat.le_of_dvd (by norm_num : 0 < 3) hq3dvd
          have hge3 : 3 ≤ Nat.card K := odd_prime_power_ge_three (Nat.card K) hKpp
          omega
        let : Fintype K := Fintype.ofFinite K
        have hf : Fintype.card K = 3 := by
          rw [← Nat.card_eq_fintype_card]
          exact hq3
        have eK : K ≃+* ZMod 3 := (ZMod.ringEquivOfPrime K Nat.prime_three hf).symm
        have eTop : (⊤ : Subgroup Q) ≃* Q := Subgroup.topEquiv (G := Q)
        have eLtop : (⊤ : Subgroup Q) ≃* PGL2 K := by
          rw [← hLtop]
          exact eL
        exact ⟨(eTop.symm.trans eLtop).trans
          ((pgl2RingEquiv eK).trans pgl2_three_equiv_perm)⟩
    · have hLcard : Nat.card ↥L = 8 := by
        have hm := hLidxmul
        rw [hL3] at hm
        exact Nat.eq_of_mul_eq_mul_left (by norm_num : 0 < 3) hm
      rcases hLmodel with hPSL | hPGL
      · rcases hPSL with ⟨eL⟩
        have hcardL' : Nat.card (PSL2 K) = 8 :=
          (Nat.card_congr eL.toEquiv).symm.trans hLcard
        have hq : Nat.card K * (Nat.card K ^ 2 - 1) = 16 := by
          rw [psl2_card_formula K hKpp] at hcardL'
          have h2dvd : 2 ∣ Nat.card K * (Nat.card K ^ 2 - 1) := by
            exact dvd_mul_of_dvd_right (two_dvd_q_sq_sub_one (Nat.card K) (by
              rcases hKpp with ⟨p, n, hp, hpOdd, hn1, hqcard⟩
              rw [hqcard]
              exact hpOdd.pow)) (Nat.card K)
          exact Nat.eq_mul_of_div_eq_right h2dvd hcardL'
        have hqdiv : Nat.card K ∣ 16 := ⟨Nat.card K ^ 2 - 1, hq.symm⟩
        have hqodd : Odd (Nat.card K) := by
          rcases hKpp with ⟨p, n, hp, hpOdd, hn1, hqcard⟩
          rw [hqcard]
          exact hpOdd.pow
        have hge3 : 3 ≤ Nat.card K := odd_prime_power_ge_three (Nat.card K) hKpp
        have hq1dvd : Nat.card K ∣ 1 :=
          odd_dvd_of_two_pow_mul hqodd 4 1 (by simpa using hqdiv)
        have hq1 : Nat.card K = 1 := Nat.dvd_one.mp hq1dvd
        omega
      · rcases hPGL with ⟨eL⟩
        have hcardL' : Nat.card (PGL2 K) = 8 :=
          (Nat.card_congr eL.toEquiv).symm.trans hLcard
        have hq : Nat.card K * (Nat.card K ^ 2 - 1) = 8 := by
          rw [pgl2_card_formula K] at hcardL'
          exact hcardL'
        have hqdiv : Nat.card K ∣ 8 := ⟨Nat.card K ^ 2 - 1, hq.symm⟩
        have hqodd : Odd (Nat.card K) := by
          rcases hKpp with ⟨p, n, hp, hpOdd, hn1, hqcard⟩
          rw [hqcard]
          exact hpOdd.pow
        have hge3 : 3 ≤ Nat.card K := odd_prime_power_ge_three (Nat.card K) hKpp
        have hq1dvd : Nat.card K ∣ 1 :=
          odd_dvd_of_two_pow_mul hqodd 3 1 (by simpa using hqdiv)
        have hq1 : Nat.card K = 1 := Nat.dvd_one.mp hq1dvd
        omega

public theorem firstCase_hhat_quotient_U_s4_of_U_card_three
    {G : Type u} [Group G] [Finite G]
    (hmin : IsMinimalCounterexample G)
    (c : CentralizerSetup G) (hfirst : FirstCase c)
    (hklein : IsKleinFour (pCore 2 c.Hhat))
    (hU3 : Nat.card c.U = 3) :
    Nonempty ((c.Hhat ⧸ pPrimeCore 2 c.Hhat) ≃* Equiv.Perm (Fin 4)) :=
  firstCase_hhat_quotient_U_s4_of_U3 hmin c hfirst hklein hU3

public theorem firstCase_hhat_quotient_U_s4
    {G : Type u} [Group G] [Finite G]
    (hmin : IsMinimalCounterexample G)
    (c : CentralizerSetup G) (hfirst : FirstCase c)
    (d : FirstCaseCountData c) :
    Nonempty ((c.Hhat ⧸ pPrimeCore 2 c.Hhat) ≃* Equiv.Perm (Fin 4)) := by
  exact firstCase_hhat_quotient_U_s4_of_U_card_three hmin c hfirst
    (by exact firstCase_twoCore_isKleinFour hmin c hfirst)
    (firstCase_U_card_three hmin c hfirst d)

end CFSG.GorensteinWalter
