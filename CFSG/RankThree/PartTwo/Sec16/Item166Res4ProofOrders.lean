module

public import CFSG.RankThree.PartTwo.Sec14.Item148RankProofChar
import CFSG.RankThree.PartTwo.KFacts.KS14Orders

public section

namespace CFSG.RankThree.PartTwo.Sec16.Proof166Res4

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec14
  CFSG.RankThree.PartTwo.Sec14.Item148Rank

theorem false_of_card_eq_two_pow_odd {k N Q g : ℕ} (hk : 1 ≤ k) (hg : g ∣ 3)
    (hq : N * g = (2 ^ k) ^ 3 * (((2 ^ k) ^ 2 - 1) * ((2 ^ k) ^ 3 - 1)) ∨
      N * g = (2 ^ k) ^ 3 * (((2 ^ k) ^ 2 - 1) * ((2 ^ k) ^ 3 + 1)))
    (hQ : Odd Q) (hQ3 : 3 ≤ Q)
    (hN : 3 * N = Q ^ 3 * ((Q ^ 2 - 1) * (Q ^ 3 - 1)) ∨
      3 * N = Q ^ 3 * ((Q ^ 2 - 1) * (Q ^ 3 + 1))) : False := by
  set q := 2 ^ k with hqdef
  have hq2 : 2 ≤ q := le_trans (by norm_num) (Nat.pow_le_pow_right (by norm_num) hk)
  have hgpos : 0 < g := Nat.pos_of_dvd_of_pos hg (by norm_num)
  have hg13 : g = 1 ∨ g = 3 := (Nat.dvd_prime Nat.prime_three).mp hg
  have hNq : N ≤ q ^ 8 := by
    obtain ⟨h1, h2⟩ := mul_le_pow_five148 q
    have hNg : N ≤ N * g := Nat.le_mul_of_pos_right N hgpos
    have hq8 : q ^ 8 = q ^ 3 * q ^ 5 := by ring
    rcases hq with h | h
    · rw [h] at hNg
      exact hNg.trans ((Nat.mul_le_mul_left _ h1).trans hq8.ge)
    · rw [h] at hNg
      exact hNg.trans ((Nat.mul_le_mul_left _ h2).trans hq8.ge)
  have hQ8 : Q ^ 8 ≤ 2 * (3 * N) := by
    have h5 := pow_five_le148 (show 2 ≤ Q by omega)
    have hR : Q ^ 3 * ((Q ^ 2 - 1) * (Q ^ 3 - 1)) ≤ 3 * N := by
      rcases hN with h | h
      · exact h.ge
      · rw [h]
        exact Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _ (by omega))
    calc Q ^ 8 = Q ^ 3 * Q ^ 5 := by ring
      _ ≤ Q ^ 3 * (2 * ((Q ^ 2 - 1) * (Q ^ 3 - 1))) := Nat.mul_le_mul_left _ h5
      _ = 2 * (Q ^ 3 * ((Q ^ 2 - 1) * (Q ^ 3 - 1))) := by ring
      _ ≤ 2 * (3 * N) := by omega
  have hlt : 7 * Q < 9 * q := by
    by_contra hge
    have hge' : 9 * q ≤ 7 * Q := not_lt.mp hge
    have h1 : (9 * q) ^ 8 ≤ (7 * Q) ^ 8 := Nat.pow_le_pow_left hge' 8
    rw [mul_pow, mul_pow] at h1
    have hq8 : 0 < q ^ 8 := by positivity
    nlinarith
  have hcop3 : Nat.Coprime (q ^ 3) g := by
    rw [hqdef, ← pow_mul]
    exact coprime_two_pow_of_odd148 _ (by rcases hg13 with rfl | rfl <;> decide)
  have hqN : q ^ 3 ∣ N := by
    refine hcop3.dvd_of_dvd_mul_right ?_
    rcases hq with h | h <;> rw [h] <;> exact Dvd.intro _ rfl
  have hcopQ : Nat.Coprime (q ^ 3) (Q ^ 3) := by
    rw [hqdef, ← pow_mul]
    exact coprime_two_pow_of_odd148 _ hQ.pow
  obtain ⟨u, rfl⟩ : ∃ u, Q = u + 1 := ⟨Q - 1, by omega⟩
  have hu : Even u := by
    obtain ⟨j, hj⟩ := hQ
    exact ⟨j, by omega⟩
  have hu0 : 0 < u := by omega
  have hdiv : 2 ^ (k * 3) ∣ u ^ 2 * (u + 2) ∨ 2 ^ (k * 3) ∣ u * (u + 2) ^ 2 := by
    rw [pow_mul, ← hqdef]
    have h3N : q ^ 3 ∣ 3 * N := Dvd.dvd.mul_left hqN 3
    rcases hN with h | h
    · left
      rw [h] at h3N
      have h2 : q ^ 3 ∣ (u ^ 2 * (u + 2)) * (u ^ 2 + 3 * u + 3) := by
        have h1' := hcopQ.dvd_of_dvd_mul_left h3N
        rwa [succ_sq_sub_one148, succ_cube_sub_one148,
          show u * (u + 2) * (u * (u ^ 2 + 3 * u + 3)) =
            u ^ 2 * (u + 2) * (u ^ 2 + 3 * u + 3) by ring] at h1'
      have hodd : Odd (u ^ 2 + 3 * u + 3) := by
        obtain ⟨j, rfl⟩ := hu
        exact ⟨2 * j ^ 2 + 3 * j + 1, by ring⟩
      rw [hqdef, ← pow_mul] at h2 ⊢
      exact (coprime_two_pow_of_odd148 _ hodd).dvd_of_dvd_mul_right h2
    · right
      rw [h] at h3N
      have h2 : q ^ 3 ∣ (u * (u + 2) ^ 2) * (u ^ 2 + u + 1) := by
        have h1' := hcopQ.dvd_of_dvd_mul_left h3N
        rwa [succ_sq_sub_one148, show (u + 1) ^ 3 + 1 = (u + 2) * (u ^ 2 + u + 1) by ring,
          show u * (u + 2) * ((u + 2) * (u ^ 2 + u + 1)) =
            u * (u + 2) ^ 2 * (u ^ 2 + u + 1) by ring] at h1'
      have hodd : Odd (u ^ 2 + u + 1) := by
        obtain ⟨j, rfl⟩ := hu
        exact ⟨2 * j ^ 2 + j, by ring⟩
      rw [hqdef, ← pow_mul] at h2 ⊢
      exact (coprime_two_pow_of_odd148 _ hodd).dvd_of_dvd_mul_right h2
  have hbound := two_pow_le_of_dvd148 (by omega) hu hu0 hdiv
  rw [pow_mul, ← hqdef] at hbound
  have hq4 : q ≤ 4 := by
    by_contra h5
    have h5' : 5 ≤ q := by omega
    have h1 : 7 * (u + 2) < 11 * q := by omega
    have h2 : 49 * (u + 2) ^ 2 < 121 * q ^ 2 := by nlinarith
    have h3 : 49 * q * q ^ 2 < 242 * q ^ 2 := by nlinarith
    have h4 : 49 * q < 242 := lt_of_mul_lt_mul_right h3 (Nat.zero_le _)
    omega
  have h2q : 2 ∣ q := by
    rw [hqdef]
    exact dvd_pow_self 2 (by omega)
  have hq24 : q = 2 ∨ q = 4 := by omega
  rcases hq24 with h2 | h4
  · rw [h2] at hlt
    omega
  · rw [h4] at hlt hq
    have hu4 : u = 2 ∨ u = 4 := by
      obtain ⟨j, hj⟩ := hu
      omega
    rcases hg13 with rfl | rfl <;> rcases hu4 with rfl | rfl <;> norm_num at hq hN <;> omega

theorem three_mul_card_of_isoLThreePi {X : Type} [Group X] {p e : ℕ} [Fact p.Prime] (he : 1 ≤ e)
    (h : Sec4.IsoLThreePi X p e) :
    3 * Nat.card X = (p ^ e) ^ 3 * (((p ^ e) ^ 2 - 1) * ((p ^ e) ^ 3 - 1)) ∨
      3 * Nat.card X = (p ^ e) ^ 3 * (((p ^ e) ^ 2 - 1) * ((p ^ e) ^ 3 + 1)) := by
  rcases h with ⟨h1, ⟨φ⟩⟩ | ⟨h2, ⟨φ⟩⟩
  · left
    have hc := KFacts.KS14.card_projSL_three_mul_gcd (GaloisField p e)
    rw [GaloisField.card p e (by omega), ← Nat.card_congr φ.toEquiv,
      Nat.gcd_eq_left (show 3 ∣ p ^ e - 1 by omega)] at hc
    rw [← hc, mul_comm]
  · right
    have hc := KFacts.KS14.card_projSU_three_mul_gcd p e he
    rw [← Nat.card_congr φ.toEquiv, Nat.gcd_eq_left (show 3 ∣ p ^ e + 1 by omega)] at hc
    rw [← hc, mul_comm]

theorem not_isLThreeEpsAt_two_of_isoLThreePi {X : Type} [Group X] {p e : ℕ} [Fact p.Prime]
    (hp2 : p ≠ 2) (he : 1 ≤ e) (h : Sec4.IsoLThreePi X p e) {k : ℕ} (hk : 1 ≤ k)
    (hL : IsLThreeEpsAt X 2 k) : False := by
  have hp : p.Prime := Fact.out
  have hQ : Odd (p ^ e) := (hp.eq_two_or_odd'.resolve_left hp2).pow
  have hp3 : 3 ≤ p := by
    have := hp.two_le
    omega
  have hQ3 : 3 ≤ p ^ e := le_trans hp3 (Nat.le_self_pow (by omega) p)
  obtain ⟨g, hg, hq⟩ : ∃ g, g ∣ 3 ∧
      (Nat.card X * g = (2 ^ k) ^ 3 * (((2 ^ k) ^ 2 - 1) * ((2 ^ k) ^ 3 - 1)) ∨
        Nat.card X * g = (2 ^ k) ^ 3 * (((2 ^ k) ^ 2 - 1) * ((2 ^ k) ^ 3 + 1))) := by
    rcases hL with ⟨⟨φ⟩⟩ | ⟨-, ⟨φ⟩⟩
    · refine ⟨Nat.gcd 3 (2 ^ k - 1), Nat.gcd_dvd_left _ _, Or.inl ?_⟩
      have hc := KFacts.KS14.card_projSL_three_mul_gcd (GaloisField 2 k)
      rw [GaloisField.card 2 k (by omega), ← Nat.card_congr φ.toEquiv] at hc
      exact hc
    · refine ⟨Nat.gcd 3 (2 ^ k + 1), Nat.gcd_dvd_left _ _, Or.inr ?_⟩
      have hc := KFacts.KS14.card_projSU_three_mul_gcd 2 k hk
      rw [← Nat.card_congr φ.toEquiv] at hc
      exact hc
  exact false_of_card_eq_two_pow_odd hk hg hq hQ hQ3 (three_mul_card_of_isoLThreePi he h)

theorem eq_of_card_eq_two_pow_mul_odd {X : Type} [Group X] {n : ℕ} (hn : 1 ≤ n)
    (h : Sec4.IsoLThreePi X 2 n) {a s : ℕ} (hs : Odd s) (hX : Nat.card X = 2 ^ a * s) :
    a = 3 * n := by
  have hodd : ∀ b : ℕ, 0 < b → Odd ((2 ^ n) ^ b - 1) ∧ Odd ((2 ^ n) ^ b + 1) := by
    intro b hb
    have he : Even ((2 ^ n) ^ b) := by
      rw [← pow_mul]
      exact Nat.even_pow.mpr ⟨even_two, by positivity⟩
    have h1 : 1 ≤ (2 ^ n) ^ b := Nat.one_le_pow _ _ (by positivity)
    exact ⟨Nat.Even.sub_odd h1 he odd_one, he.add_one⟩
  have hg : ∀ x : ℕ, Odd (Nat.gcd 3 x) := fun x => by
    rcases (Nat.dvd_prime Nat.prime_three).mp (Nat.gcd_dvd_left 3 x) with h1 | h3
    · rw [h1]
      exact odd_one
    · rw [h3]
      decide
  obtain ⟨g, R, hgo, hR, hc⟩ : ∃ g R, Odd g ∧ Odd R ∧ Nat.card X * g = 2 ^ (n * 3) * R := by
    rw [pow_mul]
    rcases card_mul_gcd_of_isoLThreePi_two hn h with hc | hc
    · exact ⟨_, _, hg _, (hodd 2 (by norm_num)).1.mul (hodd 3 (by norm_num)).1, hc⟩
    · exact ⟨_, _, hg _, (hodd 2 (by norm_num)).1.mul (hodd 3 (by norm_num)).2, hc⟩
  have heq : 2 ^ a * (s * g) = 2 ^ (n * 3) * R := by
    rw [← hc, hX]
    ring
  have := eq_of_two_pow_mul_odd148 (hs.mul hgo) hR heq
  omega

theorem isEmpty_mulEquiv_a10_of_isoLThreePi_two {X : Type} [Group X] {n : ℕ} (hn : 1 ≤ n)
    (h : Sec4.IsoLThreePi X 2 n) : IsEmpty (X ≃* alternatingGroup (Fin 10)) := by
  refine ⟨fun φ => ?_⟩
  have hX : Nat.card X = 2 ^ 7 * 14175 := by
    rw [Nat.card_congr φ.toEquiv, KFacts.KS14.card_alternatingGroup_five_seven_ten.2.2]
    norm_num
  have := eq_of_card_eq_two_pow_mul_odd hn h (by decide) hX
  omega

end CFSG.RankThree.PartTwo.Sec16.Proof166Res4
