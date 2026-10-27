module

public import Mathlib.GroupTheory.PGroup

public section

namespace CFSG.Quasithin.Stellmacher.CD.L3YC.Row9

section Lift

variable {X Y : Type*} [Group X] [Group Y]

structure CentralExp3 (φ : X →* Y) : Prop where
  surj : Function.Surjective φ
  central : ∀ x, φ x = 1 → ∀ y : X, x * y = y * x
  exp3 : ∀ x, φ x = 1 → x ^ 3 = 1

variable {φ : X →* Y}

theorem CentralExp3.commute (h : CentralExp3 φ) {a b : X} {k : ℕ} (hk : Nat.Coprime k 3)
    (hbk : b ^ k = 1) (hab : φ a * φ b = φ b * φ a) : a * b = b * a := by
  set ζ : X := a * b * a⁻¹ * b⁻¹ with hζ
  have hζ1 : φ ζ = 1 := by
    rw [hζ]
    calc φ (a * b * a⁻¹ * b⁻¹) = φ a * φ b * (φ a)⁻¹ * (φ b)⁻¹ := by
          simp only [map_mul, map_inv]
      _ = φ b * φ a * (φ a)⁻¹ * (φ b)⁻¹ := by rw [hab]
      _ = 1 := by group
  have hc := h.central ζ hζ1
  have h3 := h.exp3 ζ hζ1
  have hcomm : ζ * b = b * ζ := hc b
  have habk : (a * b * a⁻¹) ^ k = 1 := by
    rw [conj_pow, hbk]; simp
  have hfac : a * b * a⁻¹ = ζ * b := by
    simp only [hζ]; group
  have hzk : ζ ^ k = 1 := by
    have : (ζ * b) ^ k = ζ ^ k * b ^ k := (Commute.mul_pow (show Commute ζ b from hcomm) k)
    rw [hfac, this, hbk, mul_one] at habk
    exact habk
  have : ζ ^ Nat.gcd k 3 = 1 := pow_gcd_eq_one.mpr ⟨hzk, h3⟩
  rw [hk] at this
  have hζ' : ζ = 1 := by simpa using this
  have : a * b * a⁻¹ * b⁻¹ = 1 := hζ'
  calc a * b = (a * b * a⁻¹ * b⁻¹) * (b * a) := by group
    _ = b * a := by rw [this, one_mul]

theorem CentralExp3.lift_two_pow (h : CentralExp3 φ) {y : Y} {n : ℕ} (hy : y ^ (2 ^ n) = 1) :
    ∃ x : X, φ x = y ∧ x ^ (2 ^ n) = 1 := by
  obtain ⟨x0, rfl⟩ := h.surj y
  have hu : φ (x0 ^ (2 ^ n)) = 1 := by rw [map_pow, hy]
  have h3 := h.exp3 _ hu
  have hcop : Nat.Coprime 3 (orderOf (φ x0)) :=
    Nat.Coprime.coprime_dvd_right (orderOf_dvd_of_pow_eq_one hy)
      (Nat.Coprime.pow_right n (by decide : Nat.Coprime 3 2))
  obtain ⟨t, ht⟩ := exists_pow_eq_self_of_coprime hcop
  refine ⟨x0 ^ (3 * t), ?_, ?_⟩
  · rw [map_pow, pow_mul]; exact ht
  · calc (x0 ^ (3 * t)) ^ (2 ^ n) = ((x0 ^ (2 ^ n)) ^ 3) ^ t := by
          rw [← pow_mul, ← pow_mul, ← pow_mul]; congr 1; ring
      _ = 1 := by rw [h3, one_pow]

theorem CentralExp3.lift_seven (h : CentralExp3 φ) {y : Y} (hy : y ^ 7 = 1) :
    ∃ x : X, φ x = y ∧ x ^ 7 = 1 := by
  obtain ⟨x0, rfl⟩ := h.surj y
  have hu : φ (x0 ^ 7) = 1 := by rw [map_pow, hy]
  have h3 := h.exp3 _ hu
  have hcop : Nat.Coprime 3 (orderOf (φ x0)) :=
    Nat.Coprime.coprime_dvd_right (orderOf_dvd_of_pow_eq_one hy) (by decide)
  obtain ⟨t, ht⟩ := exists_pow_eq_self_of_coprime hcop
  refine ⟨x0 ^ (3 * t), ?_, ?_⟩
  · rw [map_pow, pow_mul]; exact ht
  · calc (x0 ^ (3 * t)) ^ 7 = ((x0 ^ 7) ^ 3) ^ t := by
          rw [← pow_mul, ← pow_mul, ← pow_mul]; congr 1; ring
      _ = 1 := by rw [h3, one_pow]

theorem CentralExp3.two_subgroup_bound [Finite X] (h : CentralExp3 φ) {m : ℕ}
    (hX : ∀ zt gt : X, zt ^ 2 = 1 → zt ≠ 1 → gt ^ 7 = 1 → gt ≠ 1 → zt * gt = gt * zt →
      Nat.card {c : X // (∃ n : ℕ, c ^ (2 ^ n) = 1) ∧ c * zt = zt * c ∧ c * gt = gt * c} ≤ m)
    {z g : Y} (hz2 : z ^ 2 = 1) (hz1 : z ≠ 1) (hg : orderOf g = 7) (hzg : z * g = g * z)
    (Q : Subgroup Y) (hQc : ∀ q ∈ Q, q * z = z * q ∧ q * g = g * q) (hQp : IsPGroup 2 Q) :
    Nat.card ↥Q ≤ m := by
  have hg7 : g ^ 7 = 1 := by rw [← hg]; exact pow_orderOf_eq_one g
  have hg1 : g ≠ 1 := by
    intro h1
    rw [h1, orderOf_one] at hg
    omega
  obtain ⟨zt, hzt, hzt2⟩ := h.lift_two_pow (n := 1) (by simpa using hz2)
  obtain ⟨gt, hgt, hgt7⟩ := h.lift_seven hg7
  have hzt2' : zt ^ 2 = 1 := by simpa using hzt2
  have hzt1 : zt ≠ 1 := fun h1 => hz1 (by rw [← hzt, h1, map_one])
  have hgt1 : gt ≠ 1 := fun h1 => hg1 (by rw [← hgt, h1, map_one])
  have hzg' : zt * gt = gt * zt := by
    have := h.commute (a := gt) (b := zt) (k := 2) (by decide) hzt2'
      (by rw [hzt, hgt]; exact hzg.symm)
    exact this.symm
  have hT := hX zt gt hzt2' hzt1 hgt7 hgt1 hzg'
  have hex : ∀ q : ↥Q, ∃ n : ℕ, (q : Y) ^ (2 ^ n) = 1 := fun q => by
    obtain ⟨n, hn⟩ := hQp q
    exact ⟨n, by simpa using congrArg Subtype.val hn⟩
  choose n hn using hex
  have hlift : ∀ q : ↥Q, ∃ x : X, φ x = q ∧ x ^ (2 ^ n q) = 1 := fun q =>
    h.lift_two_pow (hn q)
  choose ℓ hℓ hℓ2 using hlift
  let f : ↥Q → {c : X // (∃ n : ℕ, c ^ (2 ^ n) = 1) ∧ c * zt = zt * c ∧ c * gt = gt * c} :=
    fun q => ⟨ℓ q, ⟨n q, hℓ2 q⟩, by
      have := h.commute (a := ℓ q) (b := zt) (k := 2) (by decide) hzt2'
        (by rw [hℓ q, hzt]; exact (hQc q q.2).1)
      exact this, by
      have := h.commute (a := ℓ q) (b := gt) (k := 7) (by decide) hgt7
        (by rw [hℓ q, hgt]; exact (hQc q q.2).2)
      exact this⟩
  have hinj : Function.Injective f := by
    intro q q' hq
    have : ℓ q = ℓ q' := congrArg Subtype.val hq
    apply Subtype.ext
    rw [← hℓ q, ← hℓ q', this]
  exact (Nat.card_le_card_of_injective f hinj).trans hT

end Lift

end CFSG.Quasithin.Stellmacher.CD.L3YC.Row9
