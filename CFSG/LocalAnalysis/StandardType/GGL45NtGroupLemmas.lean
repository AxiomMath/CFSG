module

public import Mathlib.GroupTheory.PGroup
public import Mathlib.NumberTheory.Multiplicity

public section

namespace CFSG.HardMathSupport.C14Group

open Finset

theorem exists_fixed_of_order_p {H : Type*} [Group H] [Finite H] {p : ℕ} (hp : p.Prime)
    (α : MulAut H) (hα : α ^ p = 1) (hH : p ∣ Nat.card H) :
    ∃ x : H, orderOf x = p ∧ α x = x := by
  haveI := Fact.mk hp
  have hP : IsPGroup p (Subgroup.zpowers α) := by
    refine IsPGroup.of_card (n := (orderOf α).factorization p) ?_
    rw [Nat.card_zpowers]
    have hd : orderOf α ∣ p := orderOf_dvd_of_pow_eq_one hα
    rcases (Nat.dvd_prime hp).1 hd with h | h <;> simp [h, hp.factorization_self]
  have hmod := hP.card_modEq_card_fixedPoints H
  have hfix : p ∣ Nat.card (MulAction.fixedPoints (Subgroup.zpowers α) H) :=
    (Nat.modEq_zero_iff_dvd.1 (hmod.symm.trans (Nat.modEq_zero_iff_dvd.2 hH)))
  let C : Subgroup H := FixedPoints.subgroup (Subgroup.zpowers α) H
  have hC : p ∣ Nat.card C := hfix
  haveI : Fintype C := Fintype.ofFinite _
  obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card p (by rwa [Nat.card_eq_fintype_card] at hC)
  refine ⟨x, by rw [Subgroup.orderOf_coe]; exact hx, ?_⟩
  exact x.2 ⟨α, Subgroup.mem_zpowers α⟩

theorem geom_sum_eq_prime_mul {p N : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hN : N ≡ 1 [MOD p]) :
    ∃ u, ∑ i ∈ range p, N ^ i = p * u ∧ ¬ p ∣ u := by
  haveI := Fact.mk hp
  have hodd : Odd p := hp.odd_of_ne_two hp2
  rcases lt_trichotomy N 1 with h0 | rfl | h1
  · obtain rfl : N = 0 := by omega
    have h := hN
    unfold Nat.ModEq at h
    rw [Nat.zero_mod, Nat.mod_eq_of_lt hp.one_lt] at h
    exact absurd h (by norm_num)
  · exact ⟨1, by simp, hp.not_dvd_one⟩
  · set S := ∑ i ∈ range p, N ^ i with hS
    have hmul : S * (N - 1) = N ^ p - 1 := geom_sum_mul_of_one_le h1.le p
    have hdvd : p ∣ N - 1 := (Nat.modEq_iff_dvd' h1.le).1 hN.symm
    have hNp : ¬ p ∣ N := fun h => by
      have := Nat.dvd_sub h hdvd
      rw [show N - (N - 1) = 1 by omega] at this
      exact hp.not_dvd_one this
    have hlte := padicValNat.pow_sub_pow (p := p) (x := N) (y := 1) hodd h1 (by simpa using hdvd)
      hNp hp.ne_zero
    rw [one_pow, padicValNat_self] at hlte
    have hS0 : S ≠ 0 := by
      intro h; rw [h, zero_mul] at hmul
      have : N ^ p ≤ 1 := by omega
      exact absurd this (by
        have := Nat.one_lt_pow hp.ne_zero h1; omega)
    have hN10 : N - 1 ≠ 0 := by omega
    have hv : padicValNat p S = 1 := by
      have := padicValNat.mul (p := p) hS0 hN10
      rw [hmul, hlte] at this; omega
    have hpS : p ∣ S := by
      have := pow_padicValNat_dvd (p := p) (n := S); rwa [hv, pow_one] at this
    obtain ⟨u, hu⟩ := hpS
    refine ⟨u, hu, fun hpu => ?_⟩
    have : p ^ 2 ∣ S := by rw [hu, pow_two]; exact Nat.mul_dvd_mul_left p hpu
    have := (padicValNat_dvd_iff_le hS0).1 this
    omega

theorem pow_eq_one_and_omega_one_le_agemo {A : Type*} [Monoid A] {p v : ℕ} (hv : 1 ≤ v)
    (h : ∀ a : A, a ^ p ^ v = 1 ↔ ∃ b, a = b ^ p) :
    (∀ a : A, a ^ p ^ (v + 1) = 1) ∧ ∀ a : A, a ^ p = 1 → ∃ b, a = b ^ p ^ v := by
  refine ⟨fun a => ?_, fun a ha => ?_⟩
  · rw [pow_succ', pow_mul]
    exact (h _).2 ⟨a, rfl⟩
  · have key : ∀ i ≤ v, ∃ b : A, a = b ^ p ^ i ∧ b ^ p ^ (i + 1) = 1 := by
      intro i hi
      induction i with
      | zero => exact ⟨a, by simp, by simpa using ha⟩
      | succ i ih =>
        obtain ⟨b, rfl, hb⟩ := ih (by omega)
        have hbv : b ^ p ^ v = 1 := by
          obtain ⟨k, hk⟩ := Nat.exists_eq_add_of_le (show i + 1 ≤ v by omega)
          rw [hk, pow_add, pow_mul, hb, one_pow]
        obtain ⟨c, rfl⟩ := (h b).1 hbv
        refine ⟨c, by rw [← pow_mul, ← pow_succ'], ?_⟩
        rw [← pow_mul, ← pow_succ'] at hb
        exact hb
    obtain ⟨b, hb, -⟩ := key v le_rfl
    exact ⟨b, hb⟩

theorem homocyclic_of_norm_surjective {A : Type*} [CommGroup A] [Finite A] {p N : ℕ}
    (hp : p.Prime) (hp2 : p ≠ 2) (hA : IsPGroup p A) (hN : N ≡ 1 [MOD p]) (hN1 : N ≠ 1)
    (hF : ∀ a : A, a ^ N ^ p = a)
    (hnorm : ∀ a : A, a ^ N = a → ∃ b : A, a = ∏ i ∈ range p, b ^ N ^ i) :
    ∃ s, 2 ≤ s ∧ (∃ k : ℕ, ¬ p ∣ k ∧ N ≡ 1 + p ^ (s - 1) * k [MOD p ^ s]) ∧
      (∀ a : A, a ^ p ^ s = 1) ∧ ∀ a : A, a ^ p = 1 → ∃ b, a = b ^ p ^ (s - 1) := by
  haveI := Fact.mk hp
  have hN2 : 2 ≤ N := by
    rcases Nat.lt_or_ge N 2 with h | h
    · interval_cases N
      · have h' := hN
        unfold Nat.ModEq at h'
        rw [Nat.zero_mod, Nat.mod_eq_of_lt hp.one_lt] at h'
        exact absurd h' (by norm_num)
      · exact absurd rfl hN1
    · exact h
  have hdvd : p ∣ N - 1 := (Nat.modEq_iff_dvd' (by omega)).1 hN.symm
  obtain ⟨v, w, hw, hvw⟩ := Nat.exists_eq_pow_mul_and_not_dvd (n := N - 1) (by omega) p
    hp.one_lt.ne'
  have hv : 1 ≤ v := by
    rcases Nat.eq_zero_or_pos v with h | h
    · subst h; rw [pow_zero, one_mul] at hvw; exact absurd (hvw ▸ hdvd) hw
    · exact h
  have hG3 : ∀ a : A, a ^ N = a ↔ a ^ p ^ v = 1 := by
    intro a
    have hsplit : a ^ N = a ^ (N - 1) * a := by
      rw [← pow_succ]; congr 1; omega
    rw [hsplit, mul_eq_right, hvw, pow_mul]
    constructor
    · intro h
      obtain ⟨j, hj⟩ := hA a
      have h1 : orderOf a ∣ p ^ v * w := by
        rw [← pow_mul] at h; exact orderOf_dvd_of_pow_eq_one h
      have h2 : orderOf a ∣ p ^ j := orderOf_dvd_of_pow_eq_one hj
      obtain ⟨i, -, hi⟩ := (Nat.dvd_prime_pow hp).1 h2
      have hcop : Nat.Coprime (orderOf a) w := by
        rw [hi]; exact Nat.Coprime.pow_left _ ((Nat.Prime.coprime_iff_not_dvd hp).2 hw)
      exact orderOf_dvd_iff_pow_eq_one.1 (hcop.dvd_of_dvd_mul_right h1)
    · intro h; rw [h, one_pow]
  obtain ⟨u, hSu, hu⟩ := geom_sum_eq_prime_mul hp hp2 hN
  have hnormpow : ∀ b : A, ∏ i ∈ range p, b ^ N ^ i = b ^ (p * u) := by
    intro b; rw [Finset.prod_pow_eq_pow_sum, hSu]
  obtain ⟨n, hn⟩ := (IsPGroup.iff_card (p := p) (G := A)).1 hA
  have hcopu : Nat.Coprime (Nat.card A) u := by
    rw [hn]; exact Nat.Coprime.pow_left _ ((Nat.Prime.coprime_iff_not_dvd hp).2 hu)
  have hroot : ∀ b : A, ∃ c : A, b = c ^ u := fun b =>
    ⟨(powCoprime hcopu).symm b, by
      have := (powCoprime hcopu).apply_symm_apply b; rw [powCoprime_apply] at this
      exact this.symm⟩
  have hfixnorm : ∀ c : A, (c ^ (p * u)) ^ N = c ^ (p * u) := by
    intro c
    have hsum : (∑ i ∈ range p, N ^ i) * N + 1 = (∑ i ∈ range p, N ^ i) + N ^ p := by
      have h1 := Finset.sum_range_succ (fun i => N ^ i) p
      have h2 := Finset.sum_range_succ' (fun i => N ^ i) p
      simp only [pow_succ, pow_zero] at h2
      rw [Finset.sum_mul]
      omega
    have key : (c ^ (p * u)) ^ N * c = c ^ (p * u) * c := by
      rw [← hSu, ← pow_mul, ← pow_succ, hsum, pow_add, hF]
    exact mul_right_cancel key
  have hΩ : ∀ a : A, a ^ p ^ v = 1 ↔ ∃ b, a = b ^ p := by
    intro a
    constructor
    · intro h
      obtain ⟨b, hb⟩ := hnorm a ((hG3 a).2 h)
      rw [hnormpow, mul_comm, pow_mul] at hb
      exact ⟨b ^ u, hb⟩
    · rintro ⟨b, rfl⟩
      obtain ⟨c, rfl⟩ := hroot b
      have := (hG3 _).1 (hfixnorm c)
      rwa [mul_comm, pow_mul] at this
  obtain ⟨hexp, hom⟩ := pow_eq_one_and_omega_one_le_agemo hv hΩ
  refine ⟨v + 1, by omega, ⟨w, hw, ?_⟩, hexp, ?_⟩
  · rw [Nat.add_sub_cancel, ← hvw]
    exact Nat.ModEq.refl _ |>.trans (by rw [show 1 + (N - 1) = N by omega])
  · simpa using hom

end CFSG.HardMathSupport.C14Group
