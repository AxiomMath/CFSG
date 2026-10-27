module

public import CFSG.Quasithin.Vol2.Ch1EightFourOdd
public import CFSG.Quasithin.Vol2.Ch1EightFourFixed

public section

namespace CFSG.Quasithin.Ch1Four

@[expose] def ListNum (m : ℕ) (NS : ℕ → Prop) : Prop :=
  (FixShapeC m ∧ ∀ n, NS n → n ≤ 3) ∨ FixShape m ∨
    ((∃ r, r.Prime ∧ 5 ≤ r ∧ 2 * m = r ^ 2 * (r ^ 4 - 1)) ∧ ∀ n, NS n → n ≤ 3) ∨
    (OddL3Shape m ∧ ∀ n, NS n → n ≤ 3) ∨ C2Shape m

@[expose] def InitNum (m : ℕ) (NS : ℕ → Prop) : Prop :=
  (∃ c ∈ finOrders, ∃ k, m * 2 ^ k = c) ∨ (∃ n, 2 ≤ n ∧ m = 2 ^ n * (4 ^ n - 1)) ∨ ¬ 3 ∣ m ∨
    (∃ p k n : ℕ, p.Prime ∧ 5 ≤ p ∧ Odd n ∧ NS n ∧ m * 2 ^ k = n * (p * (p ^ 2 - 1))) ∨
    ∃ p k : ℕ, p.Prime ∧ 5 ≤ p ∧ NS (p ^ 2) ∧ m * 2 ^ k = p ^ 3 * (p ^ 2 - 1)

theorem eq_one_or_three_of_le {n : ℕ} (hn : Odd n) (h : n ≤ 3) : n = 1 ∨ n = 3 := by
  obtain ⟨k, rfl⟩ := hn
  omega

theorem not_sq_le_three {p : ℕ} (hp : 5 ≤ p) : ¬ p ^ 2 ≤ 3 := by
  have : 25 ≤ p ^ 2 := by nlinarith
  omega

theorem core {m : ℕ} {NS : ℕ → Prop} (hL : ListNum m NS) (hI : InitNum m NS) : False := by
  rcases hL with ⟨hF, hNS⟩ | hF | ⟨⟨r, hr, hr5, hm⟩, hNS⟩ | ⟨hO, hNS⟩ | hC <;>
    rcases hI with ⟨c, hc, k, hk⟩ | ⟨n, hn, hm2⟩ | h3 | ⟨p, k, n, hp, hp5, hn, hNSn, hk⟩ |
      ⟨p, k, hp, hp5, hNSp, hk⟩
  · exact hF.fin c hc k hk
  · exact hF.two n hm2
  · exact h3 hF.three
  · exact hF.odd p n k hp hp5 (eq_one_or_three_of_le hn (hNS n hNSn)) hk
  · exact not_sq_le_three hp5 (hNS _ hNSp)
  · exact hF.fin c hc k hk
  · exact hF.two n hm2
  · exact h3 hF.three
  · exact hF.odd p (n * p) k hp hp5 (hn.mul (hp.odd_of_ne_two (by omega)))
      (dvd_mul_left p n) (by rw [hk]; ring)
  · exact hF.odd p (p ^ 3) k hp hp5 ((hp.odd_of_ne_two (by omega)).pow)
      (dvd_pow_self p (by norm_num)) hk
  · exact r2_false_fix hr hr5 hm (k := k) (hk ▸ (finOrders_spec hc).2)
  · exact r2_false_two hr hr5 hm hn hm2
  · exact h3 (r2_three hr hr5 hm)
  · exact r2_false_p hr hr5 hm hp hp5 (eq_one_or_three_of_le hn (hNS n hNSn)) hk
  · exact not_sq_le_three hp5 (hNS _ hNSp)
  · rcases hO.small_of_fix (finOrders_spec hc).2 hk with rfl | rfl | rfl
    · exact not_fin_of_odd (a := 4) (o := 351) (by norm_num) (by decide) (by decide) c hc k hk
    · exact not_fin_of_odd (a := 3) (o := 729) (by norm_num) (by decide) (by decide) c hc k hk
    · exact not_fin_of_odd (a := 5) (o := 189) (by norm_num) (by decide) (by decide) c hc k hk
  · exact hO.false_of_two hn hm2
  · exact h3 hO.three
  · exact hO.false_of_p hp hp5 (eq_one_or_three_of_le hn (hNS n hNSn)) hk
  · exact not_sq_le_three hp5 (hNS _ hNSp)
  · exact hC.fin c hc k hk
  · exact hC.false_of_two (by omega) hm2
  · exact h3 hC.three
  · exact hC.false_of_odd hp hp5 (hn.mul (hp.odd_of_ne_two (by omega))) (dvd_mul_left p n)
      (by rw [hk]; ring)
  · exact hC.false_of_odd hp hp5 ((hp.odd_of_ne_two (by omega)).pow)
      (dvd_pow_self p (by norm_num)) hk

end CFSG.Quasithin.Ch1Four
