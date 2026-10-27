module

public import Mathlib.GroupTheory.PGroup

public section

namespace CFSG.Quasithin.SzN31

section FactRA

variable {p : ℕ}

theorem eq_one_of_sq_eq_one_of_pow_eq_one (hp : p.Prime) (hp2 : p ≠ 2) {G : Type*} [Group G]
    {z : G} (h2 : z * z = 1) (hpz : z ^ p = 1) : z = 1 := by
  have hcop : Nat.Coprime 2 p := (Nat.coprime_primes Nat.prime_two hp).2 (Ne.symm hp2)
  have h1 : orderOf z ∣ 2 := orderOf_dvd_of_pow_eq_one (by rw [pow_two]; exact h2)
  have h2' : orderOf z ∣ p := orderOf_dvd_of_pow_eq_one hpz
  have h3 : orderOf z ∣ 1 := by
    have := Nat.dvd_gcd h1 h2'
    rwa [hcop.gcd_eq_one] at this
  exact orderOf_eq_one_iff.1 (Nat.dvd_one.1 h3)

theorem eq_one_of_sq_eq_one_of_mem (hp : p.Prime) (hp2 : p ≠ 2) {Q : Type*} [Group Q]
    {N : Subgroup Q} (hN : IsPGroup p N) {y : Q} (hy : y ∈ N) (h2 : y * y = 1) : y = 1 := by
  obtain ⟨k, hk⟩ := hN ⟨y, hy⟩
  have hyk : y ^ p ^ k = 1 := by simpa using congrArg Subtype.val hk
  have hcop : Nat.Coprime 2 (p ^ k) :=
    Nat.Coprime.pow_right _ ((Nat.coprime_primes Nat.prime_two hp).2 (Ne.symm hp2))
  have h1 : orderOf y ∣ 2 := orderOf_dvd_of_pow_eq_one (by rw [pow_two]; exact h2)
  have h2' : orderOf y ∣ p ^ k := orderOf_dvd_of_pow_eq_one hyk
  have h3 : orderOf y ∣ 1 := by
    have := Nat.dvd_gcd h1 h2'
    rwa [hcop.gcd_eq_one] at this
  exact orderOf_eq_one_iff.1 (Nat.dvd_one.1 h3)

theorem invol_fixed_of_fixed_order_p (hp : p.Prime) (hp2 : p ≠ 2) {Q : Type*} [Group Q]
    (σ : MulAut Q) (hσ : σ * σ = 1) (N : Subgroup Q) (hN : IsPGroup p N)
    (hinv : ∀ x ∈ N, σ x ∈ N) (hfix : ∀ z ∈ N, z ^ p = 1 → σ z = z) : ∀ x ∈ N, σ x = x := by
  have hσσ : ∀ x : Q, σ (σ x) = x := fun x => by
    have := congrArg (fun f : MulAut Q => f x) hσ
    simpa using this
  intro x hx
  set w : Q := x⁻¹ * σ x with hw
  have hwN : w ∈ N := N.mul_mem (N.inv_mem hx) (hinv x hx)
  have hσw : σ w = w⁻¹ := by
    rw [hw, map_mul, map_inv, hσσ, mul_inv_rev, inv_inv]
  by_contra hne
  have hw1 : w ≠ 1 := fun h => hne (inv_mul_eq_one.1 h).symm
  obtain ⟨k, hk⟩ := hN ⟨w, hwN⟩
  have hwk : w ^ p ^ k = 1 := by simpa using congrArg Subtype.val hk
  obtain ⟨e, he⟩ : ∃ e, orderOf w = p ^ e := by
    have hdvd : orderOf w ∣ p ^ k := orderOf_dvd_of_pow_eq_one hwk
    obtain ⟨e, -, he⟩ := (Nat.dvd_prime_pow hp).1 hdvd
    exact ⟨e, he⟩
  have he0 : e ≠ 0 := by
    rintro rfl
    exact hw1 (orderOf_eq_one_iff.1 (by simpa using he))
  obtain ⟨f, rfl⟩ : ∃ f, e = f + 1 := ⟨e - 1, by omega⟩
  set z : Q := w ^ p ^ f with hz
  have hzp : z ^ p = 1 := by
    rw [hz, ← pow_mul, ← pow_succ]
    exact he ▸ pow_orderOf_eq_one w
  have hz1 : z ≠ 1 := by
    intro h
    have := orderOf_dvd_of_pow_eq_one h
    rw [he] at this
    have := Nat.le_of_dvd (pow_pos hp.pos f) this
    have hlt : p ^ f < p ^ (f + 1) := Nat.pow_lt_pow_right hp.one_lt (by omega)
    omega
  have hzN : z ∈ N := N.pow_mem hwN _
  have hσz : σ z = z⁻¹ := by
    rw [hz, map_pow, hσw, inv_pow]
  have hfz := hfix z hzN hzp
  rw [hσz] at hfz
  have hz2 : z * z = 1 := by
    have : z⁻¹ = z := hfz
    calc z * z = z * z⁻¹ := by rw [this]
      _ = 1 := mul_inv_cancel z
  exact hz1 (eq_one_of_sq_eq_one_of_pow_eq_one hp hp2 hz2 hzp)

theorem invol_eq_one_of_fixed_selfCentralizing (hp : p.Prime) (hp2 : p ≠ 2) {Q : Type*} [Group Q]
    (σ : MulAut Q) (hσ : σ * σ = 1) (N : Subgroup Q) [N.Normal] (hN : IsPGroup p N)
    (hC : ∀ y : Q, (∀ n ∈ N, y * n = n * y) → y ∈ N) (hfix : ∀ n ∈ N, σ n = n) :
    σ = 1 := by
  have hσσ : ∀ x : Q, σ (σ x) = x := fun x => by
    have := congrArg (fun f : MulAut Q => f x) hσ
    simpa using this
  ext x
  show σ x = x
  obtain ⟨y, hy⟩ : ∃ y : Q, y = σ x * x⁻¹ := ⟨_, rfl⟩
  have hyc : ∀ n ∈ N, y * n = n * y := by
    intro n hn
    have h1 : x⁻¹ * n * x ∈ N := by
      have := (inferInstance : N.Normal).conj_mem n hn x⁻¹
      simpa [mul_assoc] using this
    have h2 : σ (x⁻¹ * n * x) = x⁻¹ * n * x := hfix _ h1
    rw [map_mul, map_mul, map_inv, hfix n hn] at h2
    calc y * n = σ x * (x⁻¹ * n * x) * x⁻¹ := by rw [hy]; group
      _ = σ x * ((σ x)⁻¹ * n * σ x) * x⁻¹ := by rw [h2]
      _ = n * y := by rw [hy]; group
  have hyN : y ∈ N := hC y hyc
  have hσy : σ y = y⁻¹ := by
    rw [hy, map_mul, map_inv, hσσ]
    group
  have hfy : σ y = y := hfix y hyN
  have h : y⁻¹ = y := hσy.symm.trans hfy
  have hy2 : y * y = 1 := by
    calc y * y = y⁻¹ * y := by rw [h]
      _ = 1 := inv_mul_cancel y
  have hy1 : y = 1 := eq_one_of_sq_eq_one_of_mem hp hp2 hN hyN hy2
  rw [hy] at hy1
  exact mul_inv_eq_one.1 hy1

end FactRA

end CFSG.Quasithin.SzN31
