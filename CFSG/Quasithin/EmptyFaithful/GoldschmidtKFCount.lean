module

public import Mathlib.GroupTheory.Perm.Cycle.Type

public section

namespace CFSG.Quasithin.SBd19F

open Subgroup

variable {P : Type*} [Group P] {E : Subgroup P}

@[expose] def conjSelf (E : Subgroup P) (q : P) (hq : q ∈ normalizer (E : Set P)) :
    Function.End E :=
  fun e => ⟨q * e * q⁻¹, (mem_normalizer_iff.mp hq (e : P)).mp e.2⟩

theorem conjSelf_pow {q : P} (hq : q ∈ normalizer (E : Set P)) (k : ℕ) (e : E) :
    (((conjSelf E q hq) ^ k) e : P) = q ^ k * e * (q ^ k)⁻¹ := by
  induction k generalizing e with
  | zero =>
    change (e : P) = _
    simp
  | succ k ih =>
    rw [pow_succ]
    change ((((conjSelf E q hq) ^ k) (conjSelf E q hq e) : E) : P) = _
    rw [ih]
    simp only [conjSelf]
    group

theorem card_inf_centralizer_modEq [Finite E] {p n : ℕ} [Fact p.Prime] {q : P}
    (hq : q ∈ normalizer (E : Set P)) (hqn : q ^ (p ^ n) = 1) :
    Nat.card E ≡ Nat.card ↥(E ⊓ centralizer ({q} : Set P)) [MOD p] := by
  classical
  have : Fintype E := Fintype.ofFinite E
  have hf : (conjSelf E q hq) ^ (p ^ n) = 1 := by
    funext e
    apply Subtype.ext
    rw [conjSelf_pow hq (p ^ n) e, hqn]
    change _ = (e : P)
    simp
  have hmod := Equiv.Perm.card_fixedPoints_modEq (f := conjSelf E q hq) (p := p) (n := n) hf
  have hequiv : ↥(Function.fixedPoints (show E → E from conjSelf E q hq)) ≃
      ↥(E ⊓ centralizer ({q} : Set P)) :=
    { toFun := fun e => ⟨(e.1 : P), Subgroup.mem_inf.mpr ⟨e.1.2, by
        rw [mem_centralizer_singleton_iff]
        have h := congrArg Subtype.val e.2
        change q * (e.1 : P) * q⁻¹ = (e.1 : P) at h
        calc (e.1 : P) * q = (q * (e.1 : P) * q⁻¹) * q := by rw [h]
          _ = q * (e.1 : P) := by group⟩⟩
      invFun := fun x => ⟨⟨(x : P), (Subgroup.mem_inf.mp x.2).1⟩, by
        apply Subtype.ext
        change q * (x : P) * q⁻¹ = (x : P)
        have h := mem_centralizer_singleton_iff.mp (Subgroup.mem_inf.mp x.2).2
        calc q * (x : P) * q⁻¹ = ((x : P) * q) * q⁻¹ := by rw [← h]
          _ = (x : P) := by group⟩
      left_inv := fun e => Subtype.ext (Subtype.ext rfl)
      right_inv := fun x => Subtype.ext rfl }
  have h1 : Nat.card E = Fintype.card E := Nat.card_eq_fintype_card
  have h2 : Nat.card ↥(E ⊓ centralizer ({q} : Set P)) =
      Fintype.card ↥(Function.fixedPoints (show E → E from conjSelf E q hq)) := by
    rw [← Nat.card_congr hequiv, Nat.card_eq_fintype_card]
  rw [h1, h2]
  exact hmod

theorem card_inf_centralizer_dvd (hE : Nat.card E = 9) (q : P) :
    Nat.card ↥(E ⊓ centralizer ({q} : Set P)) ∣ 9 := by
  have h := card_dvd_of_le (inf_le_left : E ⊓ centralizer ({q} : Set P) ≤ E)
  rwa [hE] at h

theorem le_centralizer_of_prime_ge_five (hE : Nat.card E = 9) {q : P}
    (hq : q ∈ normalizer (E : Set P)) {r : ℕ} (hr : r.Prime) (hr5 : 5 ≤ r) (hqr : q ^ r = 1) :
    E ≤ centralizer ({q} : Set P) := by
  have : Fact r.Prime := ⟨hr⟩
  have hfin : Finite E := Nat.finite_of_card_ne_zero (by omega)
  have hmod := card_inf_centralizer_modEq (n := 1) hq (by simpa using hqr)
  rw [hE] at hmod
  have hdvd := card_inf_centralizer_dvd hE q
  have hle : Nat.card ↥(E ⊓ centralizer ({q} : Set P)) ≤ 9 := Nat.le_of_dvd (by norm_num) hdvd
  have hc : Nat.card ↥(E ⊓ centralizer ({q} : Set P)) = 9 := by
    have h9 := (Nat.modEq_iff_dvd' hle).mp hmod.symm
    have hdiv9 : Nat.card ↥(E ⊓ centralizer ({q} : Set P)) ∈ Nat.divisors 9 :=
      Nat.mem_divisors.mpr ⟨hdvd, by norm_num⟩
    have hdiv : Nat.divisors 9 = {1, 3, 9} := by decide
    rw [hdiv] at hdiv9
    simp only [Finset.mem_insert, Finset.mem_singleton] at hdiv9
    rcases hdiv9 with h1 | h3 | h9'
    · rw [h1] at h9
      have h8 : r ∣ 2 ^ 3 := by simpa using h9
      have := Nat.le_of_dvd (by norm_num) (hr.dvd_of_dvd_pow h8)
      omega
    · rw [h3] at h9
      have h6 : r ∣ 2 * 3 := by simpa using h9
      rcases (Nat.Prime.dvd_mul hr).mp h6 with h | h <;>
        · have := Nat.le_of_dvd (by norm_num) h
          omega
    · exact h9'
  have heq : E ⊓ centralizer ({q} : Set P) = E :=
    Subgroup.eq_of_le_of_card_ge inf_le_left (by rw [hc, hE])
  exact inf_eq_left.mp heq

theorem exists_ne_one_commute_of_threePow (hE : Nat.card E = 9) {q : P}
    (hq : q ∈ normalizer (E : Set P)) {n : ℕ} (hqn : q ^ (3 ^ n) = 1) :
    ∃ x ∈ E, x ≠ 1 ∧ x * q = q * x := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hfin : Finite E := Nat.finite_of_card_ne_zero (by omega)
  have hmod := card_inf_centralizer_modEq (p := 3) (n := n) hq hqn
  rw [hE] at hmod
  have hdvd := card_inf_centralizer_dvd hE q
  have hne : E ⊓ centralizer ({q} : Set P) ≠ ⊥ := by
    intro hbot
    rw [hbot, Subgroup.card_bot] at hmod
    exact absurd hmod (by decide)
  obtain ⟨a, ha⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hne
  refine ⟨(a : P), a.2.1, fun h => ha (Subtype.ext h), ?_⟩
  exact mem_centralizer_singleton_iff.mp a.2.2

theorem mem_of_odd_orderOf_of_mem_normalizer (hE : Nat.card E = 9)
    (hC : ∀ x ∈ E, x ≠ 1 → centralizer ({x} : Set P) = E) {q : P}
    (hq : q ∈ normalizer (E : Set P)) (hodd : Odd (orderOf q)) : q ∈ E := by
  have hn0 : orderOf q ≠ 0 := by
    intro h
    rw [h] at hodd
    exact absurd hodd (by decide)
  have hE1 : ∃ x ∈ E, x ≠ 1 := by
    by_contra hcon
    push Not at hcon
    have : E = ⊥ := (Subgroup.eq_bot_iff_forall _).mpr hcon
    rw [this, Subgroup.card_bot] at hE
    omega
  obtain ⟨x₀, hx₀E, hx₀1⟩ := hE1
  have hprime : ∀ {r : ℕ}, r.Prime → r ∣ orderOf q → r = 3 := by
    intro r hr hrd
    by_contra hr3
    have hr2 : r ≠ 2 := by
      rintro rfl
      exact (Nat.not_even_iff_odd.mpr hodd) (even_iff_two_dvd.mpr hrd)
    have hr5 : 5 ≤ r := by
      have h2 := hr.two_le
      by_contra hlt
      have h234 : r = 2 ∨ r = 3 ∨ r = 4 := by omega
      rcases h234 with h | h | h
      · exact hr2 h
      · exact hr3 h
      · rw [h] at hr
        exact absurd hr (by decide)
    set z : P := q ^ (orderOf q / r) with hz
    have hzo : orderOf z = r := orderOf_pow_orderOf_div hn0 hrd
    have hzN : z ∈ normalizer (E : Set P) := pow_mem hq _
    have hzr : z ^ r = 1 := by rw [← hzo]; exact pow_orderOf_eq_one z
    have hcomm := le_centralizer_of_prime_ge_five hE hzN hr hr5 hzr
    have hzx : z ∈ centralizer ({x₀} : Set P) := by
      rw [mem_centralizer_singleton_iff]
      exact (mem_centralizer_singleton_iff.mp (hcomm hx₀E)).symm
    rw [hC x₀ hx₀E hx₀1] at hzx
    have : r ∣ 9 := by
      rw [← hE, ← hzo]
      exact orderOf_dvd_natCard E hzx
    have hr9 : r ∣ 3 ^ 2 := by norm_num; exact this
    exact hr3 ((Nat.prime_dvd_prime_iff_eq hr Nat.prime_three).mp (hr.dvd_of_dvd_pow hr9))
  have hpow := Nat.eq_prime_pow_of_unique_prime_dvd hn0 (fun {d} hd hdd => hprime hd hdd)
  have hqn : q ^ (3 ^ (orderOf q).primeFactorsList.length) = 1 := by
    rw [← hpow]
    exact pow_orderOf_eq_one q
  obtain ⟨x, hxE, hx1, hxq⟩ := exists_ne_one_commute_of_threePow hE hq hqn
  have hqx : q ∈ centralizer ({x} : Set P) := by
    rw [mem_centralizer_singleton_iff]
    exact hxq.symm
  rwa [hC x hxE hx1] at hqx

end CFSG.Quasithin.SBd19F
