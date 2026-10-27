module

public import CFSG.Walter.W67.RouteRee

public section

namespace CFSG.Walter.W67

namespace RCyc

section Sylow

variable {L : Type*} [Group L] [Finite L] {p : ℕ} [Fact p.Prime]

theorem isCyclic_sylow_of_factorization_eq (C : Subgroup L) (hC : IsCyclic C)
    (hfac : (Nat.card L).factorization p = (Nat.card C).factorization p) (P : Sylow p L) :
    IsCyclic (P : Subgroup L) := by
  obtain ⟨Q⟩ : Nonempty (Sylow p C) := inferInstance
  have hQ : Nat.card ((Q : Subgroup C).map C.subtype) = p ^ (Nat.card L).factorization p := by
    rw [Subgroup.card_map_of_injective C.subtype_injective, Sylow.card_eq_multiplicity, hfac]
  have hQc : IsCyclic ((Q : Subgroup C).map C.subtype) :=
    (MulEquiv.isCyclic ((Q : Subgroup C).equivMapOfInjective _ C.subtype_injective)).mp
      inferInstance
  exact (MulEquiv.isCyclic (Sylow.equiv (Sylow.ofCard _ hQ) P)).mp hQc

theorem isCyclic_sylow_of_card_eq_mul (C : Subgroup L) (hC : IsCyclic C) {m : ℕ}
    (hm : Nat.card L = Nat.card C * m) (hpm : ¬ p ∣ m) (P : Sylow p L) :
    IsCyclic (P : Subgroup L) := by
  refine isCyclic_sylow_of_factorization_eq C hC ?_ P
  have hm0 : m ≠ 0 := by
    rintro rfl
    exact hpm (dvd_zero p)
  rw [hm, Nat.factorization_mul Nat.card_pos.ne' hm0, Finsupp.add_apply,
    Nat.factorization_eq_zero_of_not_dvd hpm, add_zero]

theorem isCyclic_sylow_of_not_sq_dvd (h : ¬ p ^ 2 ∣ Nat.card L) (P : Sylow p L) :
    IsCyclic (P : Subgroup L) := by
  have hle : (Nat.card L).factorization p ≤ 1 := by
    by_contra hlt
    exact h ((Nat.Prime.pow_dvd_iff_le_factorization Fact.out Nat.card_pos.ne').mpr (by omega))
  have hc := P.card_eq_multiplicity
  rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hle with h0 | h1
  · rw [h0, pow_zero, Subgroup.card_eq_one] at hc
    rw [hc]
    infer_instance
  · rw [h1, pow_one] at hc
    exact isCyclic_of_prime_card hc

end Sylow

theorem not_sq_dvd_1512 {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hp3 : p ≠ 3) : ¬ p ^ 2 ∣ 1512 := by
  intro h
  have hcop : Nat.Coprime (p ^ 2) 216 := by
    refine Nat.Coprime.pow_left 2 ?_
    rw [show (216 : ℕ) = 2 ^ 3 * 3 ^ 3 by norm_num]
    exact Nat.Coprime.mul_right
      (Nat.Coprime.pow_right 3 ((Nat.coprime_primes hp Nat.prime_two).mpr hp2))
      (Nat.Coprime.pow_right 3 ((Nat.coprime_primes hp Nat.prime_three).mpr hp3))
  rw [show (1512 : ℕ) = 216 * 7 by norm_num] at h
  have h7 := Nat.le_of_dvd (by norm_num) (hcop.dvd_of_dvd_mul_left h)
  have h3 : 3 ≤ p := by
    have := hp.two_le
    omega
  have : 3 ^ 2 ≤ p ^ 2 := Nat.pow_le_pow_left h3 2
  omega

end RCyc

open RCyc in
theorem rCyclicSylow_of_hall
    (hH : ∀ (L : Type) [Group L] [Finite L] (hL : JRGroup L), hL.q ≠ 5 → 3 < hL.q →
      ∀ (p : ℕ) [Fact p.Prime], p ∣ hL.q ^ 2 - hL.q + 1 →
        ∀ P : Sylow p L, IsCyclic (P : Subgroup L)) :
    RCyclicSylow := by
  intro L _ _ hL hq5 p _ hp2 hp3 P
  have hp : p.Prime := Fact.out
  obtain ⟨⟨⟨n, hn, hqn⟩, hcard, -, hsolv⟩, -, hR3, hR4, -⟩ := rFacts L hL hq5
  have hq3 : 3 ≤ hL.q := by
    rw [hqn]
    exact Nat.le_self_pow hn.pos.ne' 3
  rcases hq3.lt_or_eq with hq3 | hq3
  ·
    have hns : ¬ Group.IsSolvable L := fun hs => by
      have := (hsolv hs).1
      omega
    have hLc := hcard hns
    have hqq : hL.q ≤ hL.q ^ 2 := Nat.le_self_pow two_ne_zero _
    have h3 : hL.q ^ 3 + 1 = (hL.q + 1) * (hL.q ^ 2 - hL.q + 1) := by
      zify [hqq]
      ring
    have hpq : ¬ p ∣ hL.q ^ 3 := fun h => by
      rw [hqn] at h
      exact hp3 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_three).mp
        (hp.dvd_of_dvd_pow (hp.dvd_of_dvd_pow h)))
    by_cases hd : p ∣ hL.q ^ 2 - hL.q + 1
    · exact hH L hL hq5 hq3 p hd P
    by_cases hb : p ∣ hL.q - 1
    ·
      have hc : ¬ p ∣ hL.q + 1 := fun hc => hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp
        ((Nat.dvd_add_right hb).mp (by rwa [show hL.q - 1 + 2 = hL.q + 1 by omega])))
      obtain ⟨S⟩ : Nonempty (Sylow 3 L) := inferInstance
      obtain ⟨-, -, -, -, -, -, -, -, W, hWc, hWcard, -⟩ := hR3 hq3 S
      refine isCyclic_sylow_of_card_eq_mul W hWc
        (m := hL.q ^ 3 * (hL.q + 1) * (hL.q ^ 2 - hL.q + 1)) ?_
        (hp.not_dvd_mul (hp.not_dvd_mul hpq hc) hd) P
      rw [hLc, hWcard, h3]
      ring
    by_cases hc : p ∣ hL.q + 1
    ·
      have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
      obtain ⟨fr⟩ := Frame.nonempty L hL.toHyp
      obtain ⟨⟨t, ht⟩, hot⟩ := exists_prime_orderOf_dvd_card'
        (G := ↥((fr.S : Subgroup L) ⊓ hL.toHyp.K)) 2 (by rw [fr.card_T]; norm_num)
      rw [Subgroup.orderOf_mk] at hot
      obtain ⟨hAc, hAcard, -⟩ := hR4 hq3 t (Subgroup.mem_inf.mp ht).2 hot
      have h4 : ¬ p ∣ 4 := fun h4 => hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp
        (hp.dvd_of_dvd_pow (show p ∣ 2 ^ 2 by norm_num; exact h4)))
      refine isCyclic_sylow_of_card_eq_mul _ hAc
        (m := 4 * hL.q ^ 3 * (hL.q - 1) * (hL.q ^ 2 - hL.q + 1)) ?_
        (hp.not_dvd_mul (hp.not_dvd_mul (hp.not_dvd_mul h4 hpq) hb) hd) P
      rw [hLc, h3, ← hAcard]
      ring
    ·
      refine isCyclic_sylow_of_not_sq_dvd (fun h => ?_) P
      have h1 := (dvd_pow_self p two_ne_zero).trans h
      rw [hLc, h3] at h1
      exact hp.not_dvd_mul (hp.not_dvd_mul (hp.not_dvd_mul hc hd) hpq) hb h1
  ·
    refine isCyclic_sylow_of_not_sq_dvd (fun h => not_sq_dvd_1512 hp hp2 hp3 (h.trans ?_)) P
    by_cases hs : Group.IsSolvable L
    · rw [(hsolv hs).2.1]
      norm_num
    · rw [hcard hs, ← hq3]
      norm_num

end CFSG.Walter.W67
