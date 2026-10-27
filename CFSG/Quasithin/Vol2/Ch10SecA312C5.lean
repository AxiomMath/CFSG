module

public import CFSG.Quasithin.Vol2.Ch10SecA312C4

public section

namespace CFSG.Quasithin.Vol2.Ch10.A312C

variable {L : Type} [Group L] [Finite L]

omit [Finite L] in
theorem psl2_not_dvd {p r : ℕ} (hp : p.Prime) (hr : r.Prime) (hrp : r ≠ p)
    (h : ¬ r ^ 2 ∣ p ^ 2 - 1) (hL : IsPSL 2 p 1 L) : ¬ r ^ (1 + 1) ∣ Nat.card L := fun hd =>
  h (Nat.Coprime.dvd_of_dvd_mul_left (Nat.Coprime.pow_left 2
    ((Nat.coprime_primes hr hp).mpr hrp)) (hd.trans (card_dvd_of_isPSL2 hL)))

theorem not_dvd_of_dvd_succ {p r : ℕ} (hr : r.Prime) (hr2 : r ≠ 2) (hrd : r ∣ p + 1)
    (hp : 2 ≤ p) : ¬ r ∣ p - 1 ∧ ¬ r ∣ p ∧ ¬ r ∣ p ^ 2 + p + 1 := by
  refine ⟨fun h => ?_, fun h => ?_, fun h => ?_⟩
  · have h2 : r ∣ 2 := by
      have := Nat.dvd_sub hrd h
      rwa [show p + 1 - (p - 1) = 2 by omega] at this
    exact hr2 ((Nat.prime_dvd_prime_iff_eq hr Nat.prime_two).mp h2)
  · exact hr.one_lt.ne' (Nat.dvd_one.mp ((Nat.dvd_add_right h).mp hrd))
  · have h1 : r ∣ p * (p + 1) := hrd.mul_left p
    have h2 : p ^ 2 + p + 1 = p * (p + 1) + 1 := by ring
    rw [h2] at h
    exact hr.one_lt.ne' (Nat.dvd_one.mp ((Nat.dvd_add_right h1).mp h))

theorem not_dvd_of_dvd_pred {p r : ℕ} (hr : r.Prime) (hr2 : r ≠ 2) (hrd : r ∣ p - 1)
    (hp : 2 ≤ p) : ¬ r ∣ p + 1 ∧ ¬ r ∣ p ∧ ¬ r ∣ p ^ 2 - p + 1 := by
  refine ⟨fun h => ?_, fun h => ?_, fun h => ?_⟩
  · exact (not_dvd_of_dvd_succ hr hr2 h hp).1 hrd
  · have h1 : r ∣ p - (p - 1) := Nat.dvd_sub h hrd
    rw [show p - (p - 1) = 1 by omega] at h1
    exact hr.one_lt.ne' (Nat.dvd_one.mp h1)
  · have h1 : r ∣ p * (p - 1) := hrd.mul_left p
    have h2 : p ^ 2 - p + 1 = p * (p - 1) + 1 := by
      have : p ≤ p ^ 2 := by nlinarith
      zify [this, (by omega : 1 ≤ p)]
      ring
    rw [h2] at h
    exact hr.one_lt.ne' (Nat.dvd_one.mp ((Nat.dvd_add_right h1).mp h))

theorem l3_not_dvd {p r : ℕ} (hp : p.Prime) (hr : r.Prime) (hr2 : r ≠ 2) (hrd : r ∣ p + 1)
    (hL : IsPSL 3 p 1 L ∨ IsSL3 p L) : ¬ r ^ ((p + 1).factorization r + 1) ∣ Nat.card L := by
  have hp2 := hp.two_le
  obtain ⟨h1, h2, h3⟩ := not_dvd_of_dvd_succ hr hr2 hrd hp2
  have hdvd : Nat.card L ∣ p ^ 3 * ((p ^ 2 - 1) * (p ^ 3 - 1)) := by
    rcases hL with hL | hL
    · exact card_dvd_of_isPSL3 hL
    · exact (card_of_isSL3 hL).dvd
  have hp1 : p - 1 ≠ 0 := by omega
  refine not_pow_succ_dvd hr Nat.card_pos.ne' ((factorization_le_of_dvd hdvd
    (by rw [sq_sub_one_eq, cube_sub_one_eq]; positivity) r).trans ?_)
  rw [sq_sub_one_eq, cube_sub_one_eq, factorization_mul_apply (by positivity) (by positivity),
    factorization_mul_apply (by positivity) (by positivity),
    factorization_mul_apply hp1 (by positivity), factorization_mul_apply hp1 (by positivity),
    factorization_eq_zero_of_not_dvd' (fun h => h2 (hr.dvd_of_dvd_pow h)),
    factorization_eq_zero_of_not_dvd' h1, factorization_eq_zero_of_not_dvd' h3]
  omega

theorem u3_not_dvd {p r : ℕ} [Fact p.Prime] (hr : r.Prime) (hr2 : r ≠ 2) (hrd : r ∣ p - 1)
    (hL : IsPSU 3 p 1 L ∨ IsSU3 p L) : ¬ r ^ ((p - 1).factorization r + 1) ∣ Nat.card L := by
  have hp2 := (Fact.out : p.Prime).two_le
  obtain ⟨h1, h2, h3⟩ := not_dvd_of_dvd_pred hr hr2 hrd hp2
  have hp1 : p - 1 ≠ 0 := by omega
  have hq : p ^ 2 - p + 1 ≠ 0 := by omega
  have hdvd : Nat.card L ∣ p ^ 3 * ((p + 1) * (p - 1)) * ((p + 1) * (p ^ 2 - p + 1)) := by
    rcases hL with hL | hL
    · have e : p ^ 3 * ((p ^ 2 - 1) * (p ^ 3 + 1)) =
          p ^ 3 * ((p + 1) * (p - 1)) * ((p + 1) * (p ^ 2 - p + 1)) := by
        rw [sq_sub_one_eq, cube_add_one_eq]
        ring
      rw [← e]
      exact Dvd.intro _ (card_of_isPSU3 hL)
    · exact (card_of_isSU3 hL).dvd
  refine not_pow_succ_dvd hr Nat.card_pos.ne' ((factorization_le_of_dvd hdvd
    (by positivity) r).trans ?_)
  rw [factorization_mul_apply (by positivity) (by positivity),
    factorization_mul_apply (by positivity) (by positivity),
    factorization_mul_apply (by positivity) hp1, factorization_mul_apply (by positivity) hq,
    factorization_eq_zero_of_not_dvd' (fun h => h2 (hr.dvd_of_dvd_pow h)),
    factorization_eq_zero_of_not_dvd' h1, factorization_eq_zero_of_not_dvd' h3]
  omega

theorem l3_not_dvd_p {p : ℕ} (hp : p.Prime) (hL : IsPSL 3 p 1 L ∨ IsSL3 p L) :
    ¬ p ^ (3 + 1) ∣ Nat.card L := by
  have hp2 := hp.two_le
  have hdvd : Nat.card L ∣ p ^ 3 * ((p ^ 2 - 1) * (p ^ 3 - 1)) := by
    rcases hL with hL | hL
    · exact card_dvd_of_isPSL3 hL
    · exact (card_of_isSL3 hL).dvd
  have h4 : 4 ≤ p ^ 2 := by nlinarith
  have h8 : 8 ≤ p ^ 3 := by nlinarith
  have hs : p ^ 2 - 1 ≠ 0 := by omega
  have hc : p ^ 3 - 1 ≠ 0 := by omega
  have hnd : ∀ m, 1 ≤ m → ¬ p ∣ p ^ m - 1 := fun m hm h => by
    have h1 : p ∣ p ^ m := dvd_pow_self p (by omega)
    have h2 := Nat.dvd_sub h1 h
    rw [show p ^ m - (p ^ m - 1) = 1 by have := Nat.one_le_pow m p hp.pos; omega] at h2
    exact hp.one_lt.ne' (Nat.dvd_one.mp h2)
  refine not_pow_succ_dvd hp Nat.card_pos.ne' ((factorization_le_of_dvd hdvd
    (by positivity) p).trans ?_)
  rw [factorization_mul_apply (by positivity) (by positivity), factorization_mul_apply hs hc,
    Nat.Prime.factorization_pow hp, Finsupp.single_eq_same,
    factorization_eq_zero_of_not_dvd' (hnd 2 (by norm_num)),
    factorization_eq_zero_of_not_dvd' (hnd 3 (by norm_num))]

end CFSG.Quasithin.Vol2.Ch10.A312C
