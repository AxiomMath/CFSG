module

public import Mathlib.GroupTheory.PGroup

public section

namespace CFSG.Quasithin.EmptyFaithfulMultiple.L3213

open scoped commutatorElement

variable {Γ : Type*} [Group Γ]

theorem mem_of_pow_mem_of_pow_mem {Q : Subgroup Γ} {x : Γ} {m n : ℕ} (hmn : Nat.Coprime m n)
    (hm : x ^ m ∈ Q) (hn : x ^ n ∈ Q) : x ∈ Q := by
  have h1 : x ^ ((m : ℤ) * m.gcdA n + (n : ℤ) * m.gcdB n) =
      (x ^ m) ^ m.gcdA n * (x ^ n) ^ m.gcdB n := by
    rw [zpow_add, zpow_mul, zpow_mul, zpow_natCast, zpow_natCast]
  have h2 : (m : ℤ) * m.gcdA n + (n : ℤ) * m.gcdB n = 1 := by
    rw [← Nat.gcd_eq_gcd_ab, Nat.Coprime.gcd_eq_one hmn, Nat.cast_one]
  rw [h2, zpow_one] at h1
  rw [h1]
  exact Q.mul_mem (Q.zpow_mem hm _) (Q.zpow_mem hn _)

theorem eq_one_of_conj_coprime {a d β : Γ} {m n : ℕ} (hmn : Nat.Coprime m n)
    (ham : a ^ m * d * (a ^ m)⁻¹ = d) (had : a * d * a⁻¹ = β * d) (haβ : a * β * a⁻¹ = β)
    (hβ : β ^ n = 1) : β = 1 := by
  have hk : ∀ k : ℕ, a ^ k * d * (a ^ k)⁻¹ = β ^ k * d := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
      have h1 : a ^ (k + 1) * d * (a ^ (k + 1))⁻¹ = a * (a ^ k * d * (a ^ k)⁻¹) * a⁻¹ := by
        group
      have h2 : a * β ^ k * a⁻¹ = β ^ k := by
        rw [← conj_pow, haβ]
      calc a ^ (k + 1) * d * (a ^ (k + 1))⁻¹ = a * (β ^ k * d) * a⁻¹ := by rw [h1, ih]
        _ = (a * β ^ k * a⁻¹) * (a * d * a⁻¹) := by group
        _ = β ^ (k + 1) * d := by rw [h2, had, pow_succ]; group
  have h3 : β ^ m = 1 := by
    have := hk m
    rw [ham] at this
    simpa using this.symm
  have h4 : orderOf β = 1 :=
    Nat.eq_one_of_dvd_coprimes hmn (orderOf_dvd_of_pow_eq_one h3) (orderOf_dvd_of_pow_eq_one hβ)
  exact orderOf_eq_one_iff.mp h4

theorem commutator_mem_of_series_coprime {N B D : Subgroup Γ} {a : Γ} {m n : ℕ}
    (hmn : Nat.Coprime m n) (ham : a ^ m = 1) (haN : a ∈ Subgroup.normalizer (N : Set Γ))
    (hDN : D ≤ Subgroup.normalizer (N : Set Γ)) (hBD : B ≤ D) (hB : ∀ b ∈ B, b ^ n ∈ N)
    (h5 : ∀ d ∈ D, a * d * a⁻¹ * d⁻¹ ∈ B) (h6 : ∀ b ∈ B, a * b * a⁻¹ * b⁻¹ ∈ N) :
    ∀ d ∈ D, a * d * a⁻¹ * d⁻¹ ∈ N := by
  intro d hd
  set β := a * d * a⁻¹ * d⁻¹ with hβdef
  have hβB : β ∈ B := h5 d hd
  have hβD : β ∈ D := hBD hβB
  have hnormN : (N.subgroupOf (Subgroup.normalizer (N : Set Γ))).Normal :=
    Subgroup.normal_subgroupOf_of_le_normalizer le_rfl
  let π := QuotientGroup.mk' (N.subgroupOf (Subgroup.normalizer (N : Set Γ)))
  let α : Subgroup.normalizer (N : Set Γ) := ⟨a, haN⟩
  let δ : Subgroup.normalizer (N : Set Γ) := ⟨d, hDN hd⟩
  let γ : Subgroup.normalizer (N : Set Γ) := ⟨β, hDN hβD⟩
  have hker : ∀ x : Subgroup.normalizer (N : Set Γ), π x = 1 ↔ (x : Γ) ∈ N := fun x => by
    rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
    rfl
  have h1 : α * δ * α⁻¹ = γ * δ := by
    apply Subtype.ext
    simp only [Subgroup.coe_mul, Subgroup.coe_inv, α, δ, γ, hβdef]
    group
  have h1' : π α * π δ * (π α)⁻¹ = π γ * π δ := by
    rw [← map_inv, ← map_mul, ← map_mul, h1, map_mul]
  have h2 : π α * π γ * (π α)⁻¹ = π γ := by
    have : π (α * γ * α⁻¹ * γ⁻¹) = 1 := by
      rw [hker]
      exact h6 β hβB
    rwa [map_mul, map_mul, map_mul, map_inv, map_inv, mul_inv_eq_one] at this
  have h3 : (π γ) ^ n = 1 := by
    rw [← map_pow, hker]
    exact hB β hβB
  have h4 : (π α) ^ m * π δ * ((π α) ^ m)⁻¹ = π δ := by
    have : α ^ m = 1 := Subtype.ext (by simp [α, ham])
    rw [← map_pow, this, map_one]
    group
  have h5 := eq_one_of_conj_coprime hmn h4 h1' h2 h3
  exact (hker γ).mp h5

theorem commutatorElement_mul_mul_of_commute {x y z₁ z₂ : Γ} (h1x : Commute z₁ x)
    (h1y : Commute z₁ y) (h12 : Commute z₁ z₂) (h2x : Commute z₂ x) (h2y : Commute z₂ y) :
    ⁅z₁ * x, z₂ * y⁆ = ⁅x, y⁆ := by
  have c1 : Commute z₁ (x * z₂ * y * x⁻¹) :=
    ((h1x.mul_right h12).mul_right h1y).mul_right h1x.inv_right
  have c2 : Commute z₂ (y * x⁻¹) := h2y.mul_right h2x.inv_right
  rw [commutatorElement_def, commutatorElement_def]
  calc z₁ * x * (z₂ * y) * (z₁ * x)⁻¹ * (z₂ * y)⁻¹
      = (z₁ * (x * z₂ * y * x⁻¹) * z₁⁻¹) * y⁻¹ * z₂⁻¹ := by group
    _ = x * (z₂ * (y * x⁻¹)) * y⁻¹ * z₂⁻¹ := by rw [c1.eq, mul_inv_cancel_right]; group
    _ = x * (y * x⁻¹ * z₂) * y⁻¹ * z₂⁻¹ := by rw [c2.eq]
    _ = x * y * x⁻¹ * (z₂ * y⁻¹ * z₂⁻¹) := by group
    _ = x * y * x⁻¹ * y⁻¹ := by
        rw [(h2y.inv_right).eq, mul_inv_cancel_right]

theorem commutator_le_self (D : Subgroup Γ) : ⁅D, D⁆ ≤ D :=
  Subgroup.commutator_le.mpr fun x hx y hy => by
    rw [commutatorElement_def]
    exact D.mul_mem (D.mul_mem (D.mul_mem hx hy) (D.inv_mem hx)) (D.inv_mem hy)

theorem conj_commutator_mem_of_central {N D : Subgroup Γ} {a : Γ} (hND : N ≤ D)
    (hDN : D ≤ Subgroup.normalizer (N : Set Γ)) (haN : a ∈ Subgroup.normalizer (N : Set Γ))
    (hcen : ∀ d ∈ D, ∀ b ∈ ⁅D, D⁆ ⊔ N, d * b * d⁻¹ * b⁻¹ ∈ N)
    (h5 : ∀ d ∈ D, a * d * a⁻¹ * d⁻¹ ∈ ⁅D, D⁆ ⊔ N) :
    ∀ b ∈ ⁅D, D⁆ ⊔ N, a * b * a⁻¹ * b⁻¹ ∈ N := by
  have hconjN : ∀ y ∈ D, ∀ c ∈ N, y * c * y⁻¹ ∈ N := fun y hy c hc =>
    (Subgroup.mem_normalizer_iff.mp (hDN hy) c).mp hc
  have hΦD : ⁅D, D⁆ ⊔ N ≤ D := sup_le (commutator_le_self D) hND
  let S : Subgroup Γ :=
    { carrier := {y | y ∈ D ∧ a * y * a⁻¹ * y⁻¹ ∈ N}
      one_mem' := ⟨D.one_mem, by simp [N.one_mem]⟩
      mul_mem' := by
        rintro y z ⟨hy, hy'⟩ ⟨hz, hz'⟩
        refine ⟨D.mul_mem hy hz, ?_⟩
        have e : a * (y * z) * a⁻¹ * (y * z)⁻¹ =
            (a * y * a⁻¹ * y⁻¹) * (y * (a * z * a⁻¹ * z⁻¹) * y⁻¹) := by group
        rw [e]
        exact N.mul_mem hy' (hconjN y hy _ hz')
      inv_mem' := by
        rintro y ⟨hy, hy'⟩
        refine ⟨D.inv_mem hy, ?_⟩
        have e : a * y⁻¹ * a⁻¹ * y⁻¹⁻¹ = y⁻¹ * (a * y * a⁻¹ * y⁻¹)⁻¹ * y⁻¹⁻¹ := by group
        rw [e]
        exact hconjN y⁻¹ (D.inv_mem hy) _ (N.inv_mem hy') }
  have hNS : N ≤ S := fun c hc =>
    ⟨hND hc, N.mul_mem ((Subgroup.mem_normalizer_iff.mp haN c).mp hc) (N.inv_mem hc)⟩
  have hnorm : (N.subgroupOf D).Normal := Subgroup.normal_subgroupOf_of_le_normalizer hDN
  let π := QuotientGroup.mk' (N.subgroupOf D)
  have hker : ∀ x : D, π x = 1 ↔ (x : Γ) ∈ N := fun x => by
    rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
    rfl
  have hcomm : ∀ (d b : D), (b : Γ) ∈ ⁅D, D⁆ ⊔ N → Commute (π b) (π d) := by
    intro d b hb
    have h := (hker (d * b * d⁻¹ * b⁻¹)).mpr (hcen d d.2 b hb)
    rw [map_mul, map_mul, map_mul, map_inv, map_inv, mul_inv_eq_one] at h
    exact (mul_inv_eq_iff_eq_mul.mp h).symm
  have hcommS : ⁅D, D⁆ ≤ S := by
    refine Subgroup.commutator_le.mpr fun d₁ hd₁ d₂ hd₂ => ⟨commutator_le_self D
      (Subgroup.commutator_mem_commutator hd₁ hd₂), ?_⟩
    set β₁ := a * d₁ * a⁻¹ * d₁⁻¹ with hβ₁
    set β₂ := a * d₂ * a⁻¹ * d₂⁻¹ with hβ₂
    have hb₁ : β₁ ∈ ⁅D, D⁆ ⊔ N := h5 d₁ hd₁
    have hb₂ : β₂ ∈ ⁅D, D⁆ ⊔ N := h5 d₂ hd₂
    have e : a * ⁅d₁, d₂⁆ * a⁻¹ * ⁅d₁, d₂⁆⁻¹ = ⁅β₁ * d₁, β₂ * d₂⁆ * ⁅d₁, d₂⁆⁻¹ := by
      simp only [hβ₁, hβ₂, commutatorElement_def]
      group
    rw [e]
    let x₁ : D := ⟨d₁, hd₁⟩
    let x₂ : D := ⟨d₂, hd₂⟩
    let y₁ : D := ⟨β₁, hΦD hb₁⟩
    let y₂ : D := ⟨β₂, hΦD hb₂⟩
    have hmem : (⁅y₁ * x₁, y₂ * x₂⁆ * ⁅x₁, x₂⁆⁻¹ : D) = (⟨⁅β₁ * d₁, β₂ * d₂⁆ * ⁅d₁, d₂⁆⁻¹,
        D.mul_mem (commutator_le_self D (Subgroup.commutator_mem_commutator
          (D.mul_mem (hΦD hb₁) hd₁) (D.mul_mem (hΦD hb₂) hd₂)))
          (D.inv_mem (commutator_le_self D (Subgroup.commutator_mem_commutator hd₁ hd₂)))⟩ : D) :=
      rfl
    have key := (hker (⁅y₁ * x₁, y₂ * x₂⁆ * ⁅x₁, x₂⁆⁻¹)).mp (by
      rw [map_mul, map_inv, map_commutatorElement, map_commutatorElement, map_mul, map_mul,
        commutatorElement_mul_mul_of_commute (hcomm x₁ y₁ hb₁) (hcomm x₂ y₁ hb₁)
          (hcomm y₂ y₁ hb₁) (hcomm x₁ y₂ hb₂) (hcomm x₂ y₂ hb₂), mul_inv_cancel])
    rw [hmem] at key
    exact key
  intro b hb
  exact (sup_le hcommS hNS hb).2

theorem commutator_mem_of_frattini_coprime {N D : Subgroup Γ} {a : Γ} {m n : ℕ}
    (hmn : Nat.Coprime m n) (ham : a ^ m = 1) (hND : N ≤ D)
    (hDN : D ≤ Subgroup.normalizer (N : Set Γ)) (haN : a ∈ Subgroup.normalizer (N : Set Γ))
    (hexp : ∀ d ∈ D, d ^ n ∈ N)
    (hcen : ∀ d ∈ D, ∀ b ∈ ⁅D, D⁆ ⊔ N, d * b * d⁻¹ * b⁻¹ ∈ N)
    (h5 : ∀ d ∈ D, a * d * a⁻¹ * d⁻¹ ∈ ⁅D, D⁆ ⊔ N) :
    ∀ d ∈ D, a * d * a⁻¹ * d⁻¹ ∈ N :=
  commutator_mem_of_series_coprime hmn ham haN hDN (sup_le (commutator_le_self D) hND)
    (fun b hb => hexp b (sup_le (commutator_le_self D) hND hb)) h5
    (conj_commutator_mem_of_central hND hDN haN hcen h5)

theorem commutator_le_centralizer_of_card_dvd {p : ℕ} [hp : Fact p.Prime] {P : Subgroup Γ}
    [Finite P] (hP : Nat.card P ∣ p ^ 3) : ⁅P, P⁆ ≤ Subgroup.centralizer (P : Set Γ) := by
  obtain ⟨k, hk3, hk⟩ := (Nat.dvd_prime_pow hp.out).mp hP
  have hPp : IsPGroup p P := IsPGroup.of_card hk
  have hcommQ : ∀ a b : P ⧸ Subgroup.center P, a * b = b * a := by
    rcases subsingleton_or_nontrivial P with hs | hn
    · intro a b
      have : Subsingleton (P ⧸ Subgroup.center P) := by
        refine ⟨fun x y => ?_⟩
        obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective x
        obtain ⟨y, rfl⟩ := QuotientGroup.mk_surjective y
        rw [Subsingleton.elim x y]
      exact Subsingleton.elim _ _
    · have hZ : Nontrivial (Subgroup.center P) := hPp.center_nontrivial
      obtain ⟨j, hj⟩ := (IsPGroup.iff_card).mp (hPp.to_subgroup (Subgroup.center P))
      have hj0 : j ≠ 0 := by
        rintro rfl
        rw [pow_zero] at hj
        exact (Finite.one_lt_card_iff_nontrivial.mpr hZ).ne' hj
      have hcard := Subgroup.card_eq_card_quotient_mul_card_subgroup (Subgroup.center P)
      have hQp : IsPGroup p (P ⧸ Subgroup.center P) := hPp.to_quotient _
      obtain ⟨i, hi⟩ := (IsPGroup.iff_card).mp hQp
      rw [hk, hi, hj, ← pow_add] at hcard
      have hik : k = i + j := Nat.pow_right_injective hp.out.two_le hcard
      have hi2 : i ≤ 2 := by omega
      interval_cases i
      · intro a b
        have : Subsingleton (P ⧸ Subgroup.center P) := by
          rw [pow_zero] at hi
          exact (Nat.card_eq_one_iff_unique.mp hi).1
        exact Subsingleton.elim _ _
      · rw [pow_one] at hi
        have := isCyclic_of_prime_card hi
        exact fun a b => (IsCyclic.isMulCommutative (α := P ⧸ Subgroup.center P)).is_comm.comm a b
      · exact fun a b => (IsPGroup.isMulCommutative_of_card_eq_prime_sq hi).is_comm.comm a b
  refine Subgroup.commutator_le.mpr fun a ha b hb => ?_
  have h1 : (⁅(⟨a, ha⟩ : P), ⟨b, hb⟩⁆ : P) ∈ Subgroup.center P := by
    rw [← QuotientGroup.eq_one_iff]
    have := map_commutatorElement (QuotientGroup.mk' (Subgroup.center P)) ⟨a, ha⟩ ⟨b, hb⟩
    simp only [QuotientGroup.mk'_apply] at this
    rw [this, commutatorElement_eq_one_iff_mul_comm]
    exact hcommQ _ _
  rw [Subgroup.mem_centralizer_iff]
  intro c hc
  have h2 := congrArg Subtype.val (Subgroup.mem_center_iff.mp h1 ⟨c, hc⟩)
  simpa [commutatorElement_def] using h2

theorem mul_card_le_card_of_lt {p : ℕ} [hp : Fact p.Prime] {A B : Subgroup Γ} [Finite B]
    (hB : IsPGroup p B) (hAB : A < B) : p * Nat.card A ≤ Nat.card B := by
  have h1 := Subgroup.relIndex_mul_card (H := A) (K := B)
  rw [inf_eq_left.mpr hAB.le] at h1
  obtain ⟨k, hk⟩ := hB.index (A.subgroupOf B)
  have hne : A.relIndex B ≠ 1 := fun h => hAB.not_ge (Subgroup.relIndex_eq_one.mp h)
  have hk0 : k ≠ 0 := by
    rintro rfl
    exact hne (by rw [Subgroup.relIndex, hk, pow_zero])
  have hle : p ≤ A.relIndex B := by
    rw [Subgroup.relIndex, hk]
    exact Nat.le_self_pow hk0 p
  calc p * Nat.card A ≤ A.relIndex B * Nat.card A := Nat.mul_le_mul_right _ hle
    _ = Nat.card B := h1

theorem commute_of_normalizes_of_coprime {p : ℕ} [hp : Fact p.Prime] {A : Subgroup Γ}
    (hA : Nat.card A = p) {y : Γ} (hy : Nat.Coprime (orderOf y) (p - 1))
    (hn : y ∈ Subgroup.normalizer (A : Set Γ)) : ∀ a ∈ A, y * a = a * y := by
  have : Finite A := Nat.finite_of_card_ne_zero (by rw [hA]; exact hp.out.ne_zero)
  have hcyc : IsCyclic A := isCyclic_of_prime_card hA
  set ψ := A.normalizerMonoidHom ⟨y, hn⟩ with hψ
  have h1 : orderOf ψ ∣ orderOf y := by
    have := orderOf_map_dvd A.normalizerMonoidHom (⟨y, hn⟩ : Subgroup.normalizer (A : Set Γ))
    rwa [Subgroup.orderOf_mk] at this
  have h2 : orderOf ψ ∣ p - 1 := by
    have := orderOf_dvd_natCard ψ
    rwa [IsCyclic.card_mulAut, hA, Nat.totient_prime hp.out] at this
  have hψ1 : ψ = 1 := orderOf_eq_one_iff.mp (Nat.eq_one_of_dvd_coprimes hy h1 h2)
  intro a ha
  have := congrArg (fun φ : MulAut A => ((φ ⟨a, ha⟩ : A) : Γ)) hψ1
  simp only [hψ, MulAut.one_apply] at this
  have h4 : y * a * y⁻¹ = a := this
  rw [mul_inv_eq_iff_eq_mul] at h4
  exact h4

end CFSG.Quasithin.EmptyFaithfulMultiple.L3213
