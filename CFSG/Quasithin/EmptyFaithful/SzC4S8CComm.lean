module

public import Mathlib.Data.ZMod.QuotientGroup
public import Mathlib.Tactic.Group

public section

namespace CFSG.Quasithin.SzC4S8C

open scoped commutatorElement

section CommAlg

variable {G : Type} [Group G]

theorem mem_one_c_mul {c a b : G} (hc : c * c = 1) (ha : a = 1 ∨ a = c) (hb : b = 1 ∨ b = c) :
    (a * b = 1 ∨ a * b = c) ∧ a * b = b * a := by
  rcases ha with rfl | rfl <;> rcases hb with rfl | rfl <;> simp [hc]

theorem comm_mul_left_eq {c u v z : G} {Q : Subgroup G} (hcQ : ∀ q ∈ Q, q * c * q⁻¹ = c)
    (hu : u ∈ Q) (hv : ⁅v, z⁆ = 1 ∨ ⁅v, z⁆ = c) : ⁅u * v, z⁆ = ⁅v, z⁆ * ⁅u, z⁆ := by
  have h : ⁅u * v, z⁆ = (u * ⁅v, z⁆ * u⁻¹) * ⁅u, z⁆ := by
    simp only [commutatorElement_def]
    group
  have h2 : u * ⁅v, z⁆ * u⁻¹ = ⁅v, z⁆ := by
    rcases hv with hv | hv
    · rw [hv]
      group
    · rw [hv]
      exact hcQ u hu
  rw [h, h2]

theorem comm_mul_right_eq {c u v d : G} {Q : Subgroup G} (hcQ : ∀ q ∈ Q, q * c * q⁻¹ = c)
    (hv : v ∈ Q) (hd : ⁅u, d⁆ = 1 ∨ ⁅u, d⁆ = c) : ⁅u, v * d⁆ = ⁅u, v⁆ * ⁅u, d⁆ := by
  have h : ⁅u, v * d⁆ = ⁅u, v⁆ * (v * ⁅u, d⁆ * v⁻¹) := by
    simp only [commutatorElement_def]
    group
  have h2 : v * ⁅u, d⁆ * v⁻¹ = ⁅u, d⁆ := by
    rcases hd with hd | hd
    · rw [hd]
      group
    · rw [hd]
      exact hcQ v hv
  rw [h, h2]

theorem comm_conj_eq (l x q : G) : ⁅l * x * l⁻¹, q⁆ = l * ⁅x, l⁻¹ * q * l⁆ * l⁻¹ := by
  simp only [commutatorElement_def]
  group

theorem comm_conj_conj (l x y : G) : ⁅l * x * l⁻¹, l * y * l⁻¹⁆ = l * ⁅x, y⁆ * l⁻¹ := by
  simp only [commutatorElement_def]
  group

theorem commMod_conj {c x l : G} {Q : Subgroup G} (hx : ∀ q ∈ Q, ⁅x, q⁆ = 1 ∨ ⁅x, q⁆ = c)
    (hlc : l * c * l⁻¹ = c) (hlQ : ∀ q ∈ Q, l⁻¹ * q * l ∈ Q) :
    ∀ q ∈ Q, ⁅l * x * l⁻¹, q⁆ = 1 ∨ ⁅l * x * l⁻¹, q⁆ = c := by
  intro q hq
  rw [comm_conj_eq]
  rcases hx _ (hlQ q hq) with h | h
  · left
    rw [h]
    group
  · right
    rw [h]
    exact hlc

theorem recur_final {c p0 p1 p2 p3 p4 : G} (hc : c * c = 1)
    (h0 : p0 = 1 ∨ p0 = c) (h1 : p1 = 1 ∨ p1 = c) (h2 : p2 = 1 ∨ p2 = c)
    (h3 : p3 = 1 ∨ p3 = c) (h4 : p4 = 1 ∨ p4 = c)
    (E1 : p3 = p0 * p2) (E3 : p4 = p1 * p3) (E4 : p1 = p2 * p4) : p0 = 1 := by
  by_cases hc1 : c = 1
  · rcases h0 with h | h
    · exact h
    · rw [h, hc1]
  · have hc1' : ¬ (1 : G) = c := fun h => hc1 h.symm
    rcases h0 with h0 | h0 <;> rcases h1 with h1 | h1 <;> rcases h2 with h2 | h2 <;>
      rcases h3 with h3 | h3 <;> rcases h4 with h4 | h4 <;>
      simp [h0, h1, h2, h3, h4, hc, hc1, hc1'] at E1 E3 E4 ⊢

@[expose] def commHomR (H : Subgroup G) (c x : G) (hcH : ∀ h ∈ H, h * c * h⁻¹ = c)
    (hx : ∀ h ∈ H, ⁅x, h⁆ = 1 ∨ ⁅x, h⁆ = c) : ↥H →* ↥(Subgroup.zpowers c) where
  toFun h := ⟨⁅x, (h : G)⁆, by
    rcases hx h h.2 with e | e
    · rw [e]
      exact Subgroup.one_mem _
    · rw [e]
      exact Subgroup.mem_zpowers c⟩
  map_one' := by
    apply Subtype.ext
    simp
  map_mul' h h' := by
    apply Subtype.ext
    exact comm_mul_right_eq hcH h.2 (hx h' h'.2)

theorem zpowers_comm (c : G) (a b : ↥(Subgroup.zpowers c)) : a * b = b * a := by
  obtain ⟨i, hi⟩ := Subgroup.mem_zpowers_iff.mp a.2
  obtain ⟨j, hj⟩ := Subgroup.mem_zpowers_iff.mp b.2
  apply Subtype.ext
  show (a : G) * (b : G) = (b : G) * (a : G)
  rw [← hi, ← hj, ← zpow_add, ← zpow_add, add_comm]

theorem zpowers_sq {c : G} (hc : c * c = 1) (a : ↥(Subgroup.zpowers c)) : a ^ 2 = 1 := by
  obtain ⟨i, hi⟩ := Subgroup.mem_zpowers_iff.mp a.2
  apply Subtype.ext
  show (a : G) ^ 2 = 1
  rw [← hi, ← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, pow_two, hc, one_zpow]

theorem card_zpowers_two {c : G} (hc : c * c = 1) (hc1 : c ≠ 1) :
    Nat.card ↥(Subgroup.zpowers c) = 2 := by
  rw [Nat.card_zpowers]
  exact orderOf_eq_prime (by rw [pow_two]; exact hc) hc1

theorem comm_eq_one_of_recur {Q Q₂ Φ L : Subgroup G} {c a x z : G} (hc2 : c * c = 1)
    (hcQ : ∀ q ∈ Q, q * c * q⁻¹ = c) (hLc : ∀ l ∈ L, l * c * l⁻¹ = c) (haL : a ∈ L)
    (hΦQ : Φ ≤ Q) (hQ₂Q : Q₂ ≤ Q) (hQ₂Φ : ∀ u ∈ Q₂, ∀ w ∈ Φ, ⁅u, w⁆ = 1)
    (hLQ : ∀ l ∈ L, ∀ q ∈ Q, l * q * l⁻¹ ∈ Q) (hLQ₂ : ∀ l ∈ L, ∀ q ∈ Q₂, l * q * l⁻¹ ∈ Q₂)
    (hrel : ∀ v ∈ Q₂, ∃ w ∈ Φ, a ^ 3 * v * (a ^ 3)⁻¹ = w * ((a ^ 2 * v * (a ^ 2)⁻¹) * v))
    (hx : x ∈ Q₂) (hxc : ∀ q ∈ Q, ⁅x, q⁆ = 1 ∨ ⁅x, q⁆ = c) (hz : z ∈ Q₂) : ⁅x, z⁆ = 1 := by
  have hpow : ∀ n : ℕ, a ^ n ∈ L := fun n => L.pow_mem haL n
  have hQn : ∀ n : ℕ, ∀ q ∈ Q, (a ^ n)⁻¹ * q * a ^ n ∈ Q := fun n q hq => by
    have := hLQ _ (L.inv_mem (hpow n)) q hq
    simpa using this
  have hxn : ∀ n : ℕ, a ^ n * x * (a ^ n)⁻¹ ∈ Q₂ := fun n => hLQ₂ _ (hpow n) x hx
  have hxc' : ∀ n : ℕ, ∀ q ∈ Q, ⁅a ^ n * x * (a ^ n)⁻¹, q⁆ = 1 ∨ ⁅a ^ n * x * (a ^ n)⁻¹, q⁆ = c :=
    fun n => commMod_conj hxc (hLc _ (hpow n)) (hQn n)
  have hzn : ∀ n : ℕ, a ^ n * z * (a ^ n)⁻¹ ∈ Q₂ := fun n => hLQ₂ _ (hpow n) z hz
  have hzQ : z ∈ Q := hQ₂Q hz
  set ψ : ℕ → G := fun n => ⁅a ^ n * x * (a ^ n)⁻¹, z⁆ with hψ
  have hψc : ∀ n, ψ n = 1 ∨ ψ n = c := fun n => hxc' n z hzQ
  have hshift : ∀ (k : ℕ) (u y : G), (⁅u, y⁆ = 1 ∨ ⁅u, y⁆ = c) →
      ⁅a ^ k * u * (a ^ k)⁻¹, a ^ k * y * (a ^ k)⁻¹⁆ = ⁅u, y⁆ := by
    intro k u y huy
    rw [comm_conj_conj]
    rcases huy with h | h
    · rw [h]
      group
    · rw [h]
      exact hLc _ (hpow k)
  have hrec : ∀ n : ℕ, n ≤ 1 → ψ (n + 3) = ψ n * ψ (n + 2) := by
    intro n _
    obtain ⟨w, hw, hwe⟩ := hrel _ (hxn n)
    have e3 : a ^ 3 * (a ^ n * x * (a ^ n)⁻¹) * (a ^ 3)⁻¹ =
        a ^ (n + 3) * x * (a ^ (n + 3))⁻¹ := by
      rw [pow_add, mul_inv_rev]
      group
    have e2 : a ^ 2 * (a ^ n * x * (a ^ n)⁻¹) * (a ^ 2)⁻¹ =
        a ^ (n + 2) * x * (a ^ (n + 2))⁻¹ := by
      rw [pow_add, mul_inv_rev]
      group
    rw [e3, e2] at hwe
    have h1 := comm_mul_left_eq (c := c) (u := a ^ (n + 2) * x * (a ^ (n + 2))⁻¹)
      (v := a ^ n * x * (a ^ n)⁻¹) (z := z) hcQ (hQ₂Q (hxn (n + 2))) (hψc n)
    have h2 := comm_mul_left_eq (c := c) (u := w) (v := (a ^ (n + 2) * x * (a ^ (n + 2))⁻¹) *
      (a ^ n * x * (a ^ n)⁻¹)) (z := z) hcQ (hΦQ hw) (by
        rw [h1]
        exact (mem_one_c_mul hc2 (hψc n) (hψc (n + 2))).1)
    have hwz : ⁅w, z⁆ = 1 := by
      have := hQ₂Φ z hz w hw
      rw [← commutatorElement_inv, this, inv_one]
    show ⁅a ^ (n + 3) * x * (a ^ (n + 3))⁻¹, z⁆ = _
    rw [hwe, h2, hwz, mul_one, h1]
  obtain ⟨w', hw', hw'e⟩ := hrel z hz
  have hx4 : a ^ 4 * x * (a ^ 4)⁻¹ ∈ Q₂ := hxn 4
  have hs3 : ⁅a ^ 4 * x * (a ^ 4)⁻¹, a ^ 3 * z * (a ^ 3)⁻¹⁆ = ψ 1 := by
    have e : a ^ 4 * x * (a ^ 4)⁻¹ = a ^ 3 * (a ^ 1 * x * (a ^ 1)⁻¹) * (a ^ 3)⁻¹ := by group
    rw [e, hshift 3 _ _ (hxc' 1 z hzQ)]
  have hs2 : ⁅a ^ 4 * x * (a ^ 4)⁻¹, a ^ 2 * z * (a ^ 2)⁻¹⁆ = ψ 2 := by
    have e : a ^ 4 * x * (a ^ 4)⁻¹ = a ^ 2 * (a ^ 2 * x * (a ^ 2)⁻¹) * (a ^ 2)⁻¹ := by group
    rw [e, hshift 2 _ _ (hxc' 2 z hzQ)]
  have hz2Q : a ^ 2 * z * (a ^ 2)⁻¹ ∈ Q := hQ₂Q (hzn 2)
  have h4 := comm_mul_right_eq (c := c) (u := a ^ 4 * x * (a ^ 4)⁻¹) (v := a ^ 2 * z * (a ^ 2)⁻¹)
    (d := z) hcQ hz2Q (hxc' 4 z hzQ)
  have h5 := comm_mul_right_eq (c := c) (u := a ^ 4 * x * (a ^ 4)⁻¹) (v := w')
    (d := (a ^ 2 * z * (a ^ 2)⁻¹) * z) hcQ (hΦQ hw') (by
      rw [h4]
      exact (mem_one_c_mul hc2 (by rw [hs2]; exact hψc 2) (hψc 4)).1)
  have hxw : ⁅a ^ 4 * x * (a ^ 4)⁻¹, w'⁆ = 1 := hQ₂Φ _ hx4 w' hw'
  have E4 : ψ 1 = ψ 2 * ψ 4 := by
    rw [← hs3, hw'e, h5, hxw, one_mul, h4, hs2]
  have E1 := hrec 0 (by norm_num)
  have E3 := hrec 1 (by norm_num)
  have := recur_final hc2 (hψc 0) (hψc 1) (hψc 2) (hψc 3) (hψc 4) E1 E3 E4
  simpa [hψ] using this

end CommAlg

end CFSG.Quasithin.SzC4S8C
