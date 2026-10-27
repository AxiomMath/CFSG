module

public import CFSG.Adapters.ProjectiveSpecialLinear

public section

namespace CFSG.Quasithin.H13.U3

open Subgroup CFSG.Open
open scoped IsMulCommutative

variable {X : Type*} [Group X] [Finite X]

theorem exists_orderOf_three_of_card_six {K : Subgroup X} (hK : Nat.card K = 6) :
    ∃ c ∈ K, orderOf c = 3 := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨c, hc⟩ := exists_prime_orderOf_dvd_card' (G := ↥K) 3 (by rw [hK]; norm_num)
  exact ⟨c, c.2, by rwa [Subgroup.orderOf_coe]⟩

omit [Finite X] in
theorem mem_zpowers_of_pow_three {K : Subgroup X} (hK : Nat.card K = 6) {c x : X} (hc : c ∈ K)
    (hc3 : orderOf c = 3) (hx : x ∈ K) (hx3 : x ^ 3 = 1) : x ∈ zpowers c := by
  have hCK : zpowers c ≤ K := zpowers_le.2 hc
  have hidx : ((zpowers c).subgroupOf K).index = 2 := by
    have h2 : Nat.card ↥((zpowers c).subgroupOf K) = 3 := by
      rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hCK).toEquiv, Nat.card_zpowers, hc3]
    have h3 := ((zpowers c).subgroupOf K).index_mul_card
    rw [hK, h2] at h3
    omega
  have hsq := Subgroup.sq_mem_of_index_two hidx ⟨x, hx⟩
  have hx2 : x ^ 2 ∈ zpowers c := by
    rw [Subgroup.mem_subgroupOf] at hsq
    simpa using hsq
  have e : x = x ^ 3 * (x ^ 2)⁻¹ := by group
  rw [e, hx3, one_mul]
  exact inv_mem hx2

omit [Finite X] in
theorem conj_eq_self_of_pow_three {K : Subgroup X} (hK : Nat.card K = 6) {c d : X} (hc : c ∈ K)
    (hc3 : orderOf c = 3) (hdK : ∀ y ∈ K, d * y * d⁻¹ ∈ K) (hd3 : d ^ 3 = 1) :
    d * c * d⁻¹ = c := by
  have hc3' : c ^ 3 = 1 := by rw [← hc3]; exact pow_orderOf_eq_one c
  have hc1 : c ≠ 1 := by
    rintro rfl
    rw [orderOf_one] at hc3
    omega
  have he3 : (d * c * d⁻¹) ^ 3 = 1 := by rw [conj_pow, hc3', mul_one, mul_inv_cancel]
  obtain ⟨k, hk⟩ := mem_zpowers_iff.1 (mem_zpowers_of_pow_three hK hc hc3 (hdK c hc) he3)
  have hk' : d * c * d⁻¹ = c ^ (k % 3).toNat := by
    rw [← hk, ← zpow_natCast, Int.toNat_of_nonneg (Int.emod_nonneg k (by norm_num)),
      ← zpow_mod_orderOf, hc3]
    norm_num
  have hlt : (k % 3).toNat < 3 := by omega
  interval_cases h : (k % 3).toNat
  · exfalso
    rw [pow_zero] at hk'
    apply hc1
    calc c = d⁻¹ * (d * c * d⁻¹) * d := by group
      _ = 1 := by rw [hk']; group
  · rwa [pow_one] at hk'
  · exfalso
    have h1 : d * c ^ 2 * d⁻¹ = c := by
      rw [← conj_pow, hk', ← pow_mul, show 2 * 2 = 3 + 1 from rfl, pow_succ, hc3', one_mul]
    have h2 : d * (d * c * d⁻¹) * d⁻¹ = c := by rw [hk', h1]
    have h3 : d * (d * (d * c * d⁻¹) * d⁻¹) * d⁻¹ = c ^ 2 := by rw [h2, hk']
    have e : d * (d * (d * c * d⁻¹) * d⁻¹) * d⁻¹ = d ^ 3 * c * (d ^ 3)⁻¹ := by
      simp only [pow_succ, pow_zero, one_mul, mul_inv_rev, mul_assoc]
    rw [e, hd3, one_mul, inv_one, mul_one, pow_two] at h3
    exact hc1 (mul_eq_left.1 h3.symm)

theorem le_two_of_elemAbelian_of_surjective {G : Type*} [Group G] [Finite G] {H : Subgroup G}
    {Q : Type*} [Group Q] [Finite Q] (π : ↥H →* Q) (hπ : Function.Surjective π)
    (hker : ∀ x : ↥H, π x = 1 → ∃ i : ℕ, x ^ 2 ^ i = 1) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hrank : ∀ E : Subgroup G, E ≤ H → IsElemAbelian p E → ∀ r, Nat.card E = p ^ r → r ≤ 2)
    {E : Subgroup Q} (hE : IsElemAbelian p E) {r : ℕ} (hcard : Nat.card E = p ^ r) : r ≤ 2 := by
  have : Fact p.Prime := ⟨hp⟩
  have hEp : IsPGroup p E := fun x => ⟨1, Subtype.ext (by simpa using hE.2 x x.2)⟩
  obtain ⟨Qs, hEQ⟩ := hEp.exists_le_sylow
  obtain ⟨S, hS⟩ := Sylow.mapSurjective_surjective hπ p Qs
  have hSQ : (S : Subgroup ↥H).map π = Qs := by rw [← hS]; rfl
  have hinj : ∀ a ∈ (S : Subgroup ↥H), ∀ b ∈ (S : Subgroup ↥H), π a = π b → a = b := by
    intro a ha b hb hab
    have hk : π (a⁻¹ * b) = 1 := by rw [map_mul, map_inv, hab, inv_mul_cancel]
    obtain ⟨i, hi⟩ := hker _ hk
    have hs : a⁻¹ * b ∈ (S : Subgroup ↥H) := Subgroup.mul_mem _ (Subgroup.inv_mem _ ha) hb
    obtain ⟨j, hj⟩ := S.isPGroup' ⟨_, hs⟩
    have hj' : (a⁻¹ * b) ^ p ^ j = 1 := by simpa using congrArg Subtype.val hj
    have h1 := Nat.Coprime.eq_one_of_dvd (Nat.Coprime.coprime_dvd_left
      (orderOf_dvd_of_pow_eq_one hi) (Nat.Coprime.pow_left i
        (Nat.Coprime.pow_right j ((Nat.coprime_primes Nat.prime_two hp).mpr (Ne.symm hp2)))))
      (orderOf_dvd_of_pow_eq_one hj')
    rw [orderOf_eq_one_iff, inv_mul_eq_one] at h1
    exact h1
  set E' := E.comap π ⊓ (S : Subgroup ↥H) with hE'def
  have hmap : E'.map π = E := by
    refine le_antisymm (fun _ ⟨s, hs, hse⟩ => hse ▸ hs.1) fun e he => ?_
    have heQ : e ∈ (S : Subgroup ↥H).map π := hSQ ▸ hEQ he
    obtain ⟨s, hs, rfl⟩ := heQ
    exact ⟨s, ⟨he, hs⟩, rfl⟩
  have hcard' : Nat.card E' = p ^ r := by
    rw [← hcard, ← hmap]
    refine (Nat.card_congr (Equiv.ofBijective (fun s : ↥E' => (⟨π s, s, s.2, rfl⟩ : ↥(E'.map π)))
      ⟨fun a b hab => Subtype.ext (hinj a a.2.2 b b.2.2 (congrArg Subtype.val hab)), ?_⟩))
    rintro ⟨_, s, hs, rfl⟩
    exact ⟨⟨s, hs⟩, rfl⟩
  set E'' := E'.map H.subtype with hE''def
  have hE''ab : IsElemAbelian p E'' := by
    refine ⟨⟨⟨fun a b => ?_⟩⟩, fun x hx => ?_⟩
    · obtain ⟨a', ha', haa⟩ := Subgroup.mem_map.mp a.2
      obtain ⟨b', hb', hbb⟩ := Subgroup.mem_map.mp b.2
      apply Subtype.ext
      rw [Subgroup.coe_mul, Subgroup.coe_mul, ← haa, ← hbb, ← map_mul, ← map_mul]
      congr 1
      refine hinj _ (Subgroup.mul_mem _ ha'.2 hb'.2) _ (Subgroup.mul_mem _ hb'.2 ha'.2) ?_
      rw [map_mul, map_mul]
      have := hE.1
      exact congrArg Subtype.val (mul_comm (⟨π a', ha'.1⟩ : ↥E) ⟨π b', hb'.1⟩)
    · obtain ⟨x', hx', rfl⟩ := Subgroup.mem_map.mp hx
      have h1 : x' ^ p = 1 := by
        refine hinj _ (Subgroup.pow_mem _ hx'.2 p) _ (Subgroup.one_mem _) ?_
        rw [map_pow, map_one]
        exact hE.2 _ hx'.1
      rw [← map_pow, h1, map_one]
  have hE''card : Nat.card E'' = p ^ r := by
    rw [hE''def, Subgroup.card_map_of_injective H.subtype_injective, hcard']
  exact hrank E'' (Subgroup.map_subtype_le _) hE''ab r hE''card


theorem exists_two_odd_decomp {X' : Type*} [Group X'] [Finite X'] (x : X') :
    ∃ y ∈ zpowers x, ∃ z ∈ zpowers x, x = y * z ∧ (∃ k : ℕ, y ^ 2 ^ k = 1) ∧
      ∃ m : ℕ, Odd m ∧ z ^ m = 1 := by
  obtain ⟨a, m, hm, hn⟩ := Nat.exists_eq_two_pow_mul_odd (orderOf_pos x).ne'
  have hcop : Nat.Coprime (2 ^ a) m := Nat.Coprime.pow_left a (Nat.coprime_two_left.2 hm)
  have hbez : ((2 ^ a : ℕ) : ℤ) * Nat.gcdA (2 ^ a) m + (m : ℤ) * Nat.gcdB (2 ^ a) m = 1 := by
    rw [← Nat.gcd_eq_gcd_ab, hcop.gcd_eq_one, Nat.cast_one]
  have hx1 : x ^ ((2 ^ a * m : ℕ) : ℤ) = 1 := by
    rw [zpow_natCast, ← hn, pow_orderOf_eq_one]
  refine ⟨x ^ ((m : ℤ) * Nat.gcdB (2 ^ a) m), zpow_mem_zpowers _ _,
    x ^ (((2 ^ a : ℕ) : ℤ) * Nat.gcdA (2 ^ a) m), zpow_mem_zpowers _ _, ?_, ⟨a, ?_⟩, m, hm, ?_⟩
  · rw [← zpow_add, add_comm, hbez, zpow_one]
  · rw [← zpow_natCast, ← zpow_mul, show ((m : ℤ) * Nat.gcdB (2 ^ a) m) * ((2 ^ a : ℕ) : ℤ) =
      ((2 ^ a * m : ℕ) : ℤ) * Nat.gcdB (2 ^ a) m by push_cast; ring, zpow_mul, hx1, one_zpow]
  · rw [← zpow_natCast, ← zpow_mul, show (((2 ^ a : ℕ) : ℤ) * Nat.gcdA (2 ^ a) m) * (m : ℤ) =
      ((2 ^ a * m : ℕ) : ℤ) * Nat.gcdA (2 ^ a) m by push_cast; ring, zpow_mul, hx1, one_zpow]

section Central

variable {Q : Type*} [Group Q]

open scoped commutatorElement

theorem commutatorElement_mul_central {x y z₁ z₂ : Q} (h1x : Commute z₁ x) (h1y : Commute z₁ y)
    (h2x : Commute z₂ x) (h2y : Commute z₂ y) (h12 : Commute z₁ z₂) :
    ⁅z₁ * x, z₂ * y⁆ = ⁅x, y⁆ := by
  rw [commutatorElement_def, commutatorElement_def]
  calc z₁ * x * (z₂ * y) * (z₁ * x)⁻¹ * (z₂ * y)⁻¹
      = z₁ * (x * z₂) * y * x⁻¹ * z₁⁻¹ * y⁻¹ * z₂⁻¹ := by group
    _ = z₁ * (z₂ * x) * y * x⁻¹ * z₁⁻¹ * y⁻¹ * z₂⁻¹ := by rw [h2x.eq]
    _ = z₁ * z₂ * x * y * (x⁻¹ * z₁⁻¹) * y⁻¹ * z₂⁻¹ := by group
    _ = z₁ * z₂ * x * y * (z₁⁻¹ * x⁻¹) * y⁻¹ * z₂⁻¹ := by rw [h1x.inv_left.inv_right.eq]
    _ = z₁ * z₂ * x * (y * z₁⁻¹) * x⁻¹ * y⁻¹ * z₂⁻¹ := by group
    _ = z₁ * z₂ * x * (z₁⁻¹ * y) * x⁻¹ * y⁻¹ * z₂⁻¹ := by rw [h1y.inv_left.eq]
    _ = z₁ * z₂ * (x * z₁⁻¹) * y * x⁻¹ * y⁻¹ * z₂⁻¹ := by group
    _ = z₁ * z₂ * (z₁⁻¹ * x) * y * x⁻¹ * y⁻¹ * z₂⁻¹ := by rw [h1x.inv_left.eq]
    _ = (z₁ * z₂) * z₁⁻¹ * (x * y * x⁻¹ * y⁻¹) * z₂⁻¹ := by group
    _ = (z₂ * z₁) * z₁⁻¹ * (x * y * x⁻¹ * y⁻¹) * z₂⁻¹ := by rw [h12.eq]
    _ = z₂ * (x * y * x⁻¹ * y⁻¹) * z₂⁻¹ := by group
    _ = x * y * x⁻¹ * y⁻¹ := by
      have hc : Commute z₂ (x * y * x⁻¹ * y⁻¹) :=
        ((h2x.mul_right h2y).mul_right h2x.inv_right).mul_right h2y.inv_right
      rw [hc.eq]
      group

theorem commutatorElement_inv_left_of_commute {x y : Q} (h : Commute ⁅x, y⁆ x) :
    ⁅x⁻¹, y⁆ = ⁅x, y⁆⁻¹ := by
  have h' : Commute ⁅x, y⁆⁻¹ x := h.inv_left
  calc ⁅x⁻¹, y⁆ = x⁻¹ * ⁅x, y⁆⁻¹ * x := by
        rw [commutatorElement_def, commutatorElement_def]
        group
    _ = ⁅x, y⁆⁻¹ := by rw [mul_assoc, h'.eq, ← mul_assoc, inv_mul_cancel, one_mul]

theorem commutatorElement_eq_one_of_central {u v w t : Q} (hw3 : w ^ 3 = 1)
    (huw : Commute u w) (hvw : Commute v w) (htw : Commute t w) {a b e : ℕ}
    (htu : t * u * t⁻¹ = w ^ a * u⁻¹) (htv : t * v * t⁻¹ = w ^ b * v) (huv : ⁅u, v⁆ = w ^ e) :
    ⁅u, v⁆ = 1 := by
  have hconj : t * ⁅u, v⁆ * t⁻¹ = ⁅t * u * t⁻¹, t * v * t⁻¹⁆ := by
    rw [commutatorElement_def, commutatorElement_def]
    group
  have h1 : t * ⁅u, v⁆ * t⁻¹ = ⁅u, v⁆ := by
    rw [huv, (htw.pow_right e).eq]
    group
  have h2 : ⁅t * u * t⁻¹, t * v * t⁻¹⁆ = ⁅u, v⁆⁻¹ := by
    rw [htu, htv, commutatorElement_mul_central (huw.pow_right a).symm.inv_right
      (hvw.pow_right a).symm (huw.pow_right b).symm.inv_right (hvw.pow_right b).symm
      ((Commute.refl w).pow_pow a b)]
    exact commutatorElement_inv_left_of_commute (by rw [huv]; exact (huw.pow_right e).symm)
  have h3 : ⁅u, v⁆ = ⁅u, v⁆⁻¹ := by
    calc ⁅u, v⁆ = t * ⁅u, v⁆ * t⁻¹ := h1.symm
      _ = ⁅t * u * t⁻¹, t * v * t⁻¹⁆ := hconj
      _ = ⁅u, v⁆⁻¹ := h2
  have h4 : ⁅u, v⁆ ^ 2 = 1 := by
    rw [pow_two]
    nth_rewrite 2 [h3]
    exact mul_inv_cancel _
  have h5 : ⁅u, v⁆ ^ 3 = 1 := by rw [huv, ← pow_mul, mul_comm, pow_mul, hw3, one_pow]
  calc ⁅u, v⁆ = ⁅u, v⁆ ^ 3 * (⁅u, v⁆ ^ 2)⁻¹ := by group
    _ = 1 := by rw [h4, h5]; group

theorem pow_three_eq_one_of_central {u w t : Q} (hw3 : w ^ 3 = 1) (huw : Commute u w)
    (htw : Commute t w) {a f : ℕ} (htu : t * u * t⁻¹ = w ^ a * u⁻¹) (hu3 : u ^ 3 = w ^ f) :
    u ^ 3 = 1 := by
  have h1 : t * u ^ 3 * t⁻¹ = u ^ 3 := by
    rw [hu3, (htw.pow_right f).eq]
    group
  have h2 : t * u ^ 3 * t⁻¹ = (u ^ 3)⁻¹ := by
    rw [← conj_pow, htu, ((huw.pow_right a).symm.inv_right).mul_pow, ← pow_mul,
      mul_comm a 3, pow_mul, hw3, one_pow, one_mul, inv_pow]
  have h6 : (u ^ 3) ^ 2 = 1 := by
    rw [pow_two]
    nth_rewrite 2 [← h1]
    rw [h2, mul_inv_cancel]
  have h9 : (u ^ 3) ^ 3 = 1 := by rw [hu3, ← pow_mul, mul_comm, pow_mul, hw3, one_pow]
  calc u ^ 3 = (u ^ 3) ^ 3 * ((u ^ 3) ^ 2)⁻¹ := by group
    _ = 1 := by rw [h6, h9]; group

end Central

end CFSG.Quasithin.H13.U3
