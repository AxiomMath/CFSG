module

public import CFSG.Quasithin.EmptyFaithful.Stellmacher.L3YC.V4Gl
public import CFSG.Quasithin.EmptyFaithful.Stellmacher.L3YC.Sylow3

public section

namespace CFSG.Quasithin

open scoped Pointwise

namespace Stellmacher.L3YC

section Helpers

variable {G : Type*} [Group G]

theorem eq_inv_of_mem_zpowers_order_three {y z : G} (hy3 : orderOf y = 3) (hz : z ∈ Subgroup.zpowers y)
    (hz1 : z ≠ 1) (hzy : z ≠ y) : z = y⁻¹ := by
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hz
  have hy : y ^ (3 : ℕ) = 1 := by rw [← hy3]; exact pow_orderOf_eq_one y
  have hk : y ^ (k % (3 : ℕ)) = y ^ k := by
    have := zpow_mod_orderOf y k
    rwa [hy3] at this
  have hk3 : k % (3 : ℕ) = 0 ∨ k % (3 : ℕ) = 1 ∨ k % (3 : ℕ) = 2 := by omega
  rcases hk3 with h | h | h
  · exact absurd (by rw [← hk, h, zpow_zero]) hz1
  · exact absurd (by rw [← hk, h, zpow_one]) hzy
  · rw [← hk, h]
    have : y ^ (2 : ℤ) = y ^ (2 : ℕ) := by norm_cast
    rw [this]
    apply eq_inv_of_mul_eq_one_left
    rw [← pow_succ]; exact hy

theorem pow_odd_inverts {n y : G} (h : n * y * n⁻¹ = y⁻¹) {m : ℕ} (hm : Odd m) :
    n ^ m * y * (n ^ m)⁻¹ = y⁻¹ := by
  obtain ⟨k, rfl⟩ := hm
  have h2 : n ^ 2 * y * (n ^ 2)⁻¹ = y := by
    have : n ^ 2 * y * (n ^ 2)⁻¹ = n * (n * y * n⁻¹) * n⁻¹ := by rw [pow_two]; group
    rw [this, h]
    have : n * y⁻¹ * n⁻¹ = (n * y * n⁻¹)⁻¹ := by group
    rw [this, h, inv_inv]
  have h2' : Commute (n ^ 2) y := by
    show n ^ 2 * y = y * n ^ 2
    have := h2
    calc n ^ 2 * y = n ^ 2 * y * (n ^ 2)⁻¹ * n ^ 2 := by group
      _ = y * n ^ 2 := by rw [this]
  have h3 : Commute (n ^ (2 * k)) y := by
    rw [pow_mul]; exact h2'.pow_left k
  have : n ^ (2 * k + 1) * y * (n ^ (2 * k + 1))⁻¹ = n ^ (2 * k) * (n * y * n⁻¹) * (n ^ (2 * k))⁻¹ := by
    group
  rw [this, h]
  have h4 : Commute (n ^ (2 * k)) y⁻¹ := h3.inv_right
  rw [h4.eq]
  group

theorem eq_one_of_pow_three_pow_two {a : G} (h3 : a ^ 3 = 1) {m : ℕ} (h2 : a ^ 2 ^ m = 1) : a = 1 := by
  have := pow_gcd_eq_one.mpr ⟨h3, h2⟩
  have hg : Nat.gcd 3 (2 ^ m) = 1 :=
    Nat.Coprime.pow_right m (by norm_num)
  rwa [hg, pow_one] at this

end Helpers

section Main

variable {G : Type} [Group G] [Finite G]

theorem exists_inverting_pair {Y S M V : Subgroup G} (hV4 : Nat.card V = 4)
    (hVsq : ∀ v ∈ V, v * v = 1) (hYM : Y ≤ M) (hSY : S ≤ Subgroup.normalizer (Y : Set G))
    (hYV : Y ≤ Subgroup.normalizer (V : Set G)) (hMV : M ≤ Subgroup.normalizer (V : Set G))
    (hS2 : IsPGroup 2 ↥S)
    (hYgen : ∀ K : Subgroup G, (∀ y ∈ Y, Odd (orderOf y) → y ∈ K) → Y ≤ K)
    (hY3 : padicValNat 3 (Nat.card ↥Y) = 1) (hodd : ¬ 2 ∣ S.relIndex (Y ⊔ S))
    {y₀ : G} (hy₀ : y₀ ∈ Y) (hy₀3 : orderOf y₀ = 3) (hy₀V : ∃ v ∈ V, y₀ * v * y₀⁻¹ ≠ v)
    {r₀ : G} (hr₀S : r₀ ∈ S) (hr₀M : r₀ ∈ M) (hr₀V : ∃ v ∈ V, r₀ * v * r₀⁻¹ ≠ v) :
    ∃ y ∈ Y, orderOf y = 3 ∧ (∃ v ∈ V, y * v * y⁻¹ ≠ v) ∧
      ∃ r ∈ S ⊓ M, r * y * r⁻¹ = y⁻¹ := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨Φ, hΦ⟩ := exists_gl_action hV4 hVsq
  have hy₀N : y₀ ∈ Subgroup.normalizer (V : Set G) := hYV hy₀
  have hy₀3' : y₀ ^ 3 = 1 := by rw [← hy₀3]; exact pow_orderOf_eq_one y₀
  set ρ : GL (Fin 2) (ZMod 2) := Φ ⟨y₀, hy₀N⟩ with hρ
  have hρ3 : ρ ^ 3 = 1 := by
    rw [hρ, ← map_pow]
    have : (⟨y₀, hy₀N⟩ : ↥(Subgroup.normalizer (V : Set G))) ^ 3 = 1 :=
      Subtype.ext (by simpa using hy₀3')
    rw [this, map_one]
  have hρ1 : ρ ≠ 1 := by
    intro h
    obtain ⟨v, hv, hmv⟩ := hy₀V
    exact hmv ((hΦ ⟨y₀, hy₀N⟩).mp h v hv)
  have himg : ∀ g (hg : g ∈ Y), Φ ⟨g, hYV hg⟩ ∈ Subgroup.zpowers ρ := by
    let K : Subgroup G := ((Subgroup.zpowers ρ).comap Φ).map (Subgroup.normalizer (V : Set G)).subtype
    have hYK : Y ≤ K := by
      refine hYgen K fun y hy hodd => ?_
      refine ⟨⟨y, hYV hy⟩, ?_, rfl⟩
      have h3 : (Φ ⟨y, hYV hy⟩) ^ 3 = 1 := by
        have h1 : (Φ ⟨y, hYV hy⟩) ^ orderOf y = 1 := by
          rw [← map_pow]
          have : (⟨y, hYV hy⟩ : ↥(Subgroup.normalizer (V : Set G))) ^ orderOf y = 1 :=
            Subtype.ext (by simp)
          rw [this, map_one]
        exact pow_three_eq_one_of_odd card_gl2 hodd h1
      show Φ ⟨y, hYV hy⟩ ∈ Subgroup.zpowers ρ
      rcases gl2_cube_mem ρ _ hρ3 hρ1 h3 with h | h | h
      · rw [h]; exact Subgroup.one_mem _
      · rw [h]; exact Subgroup.mem_zpowers ρ
      · rw [h]; exact Subgroup.pow_mem _ (Subgroup.mem_zpowers ρ) 2
    intro g hg
    obtain ⟨g', hg', hg'e⟩ := hYK hg
    have : g' = ⟨g, hYV hg⟩ := Subtype.ext hg'e
    rw [← this]
    exact hg'
  have hr₀Y : r₀ * y₀ * r₀⁻¹ ∈ Y := (Subgroup.mem_normalizer_iff.mp (hSY hr₀S) y₀).mp hy₀
  obtain ⟨c₁, hc₁Y, hc₁⟩ := exists_conj_order_three hY3 hr₀Y hy₀
    (by rw [orderOf_conj_eq, hy₀3]) hy₀3
  set n : G := c₁ * r₀ with hn
  have hnconj : n * y₀ * n⁻¹ = c₁ * (r₀ * y₀ * r₀⁻¹) * c₁⁻¹ := by rw [hn]; group
  have hnz : n * y₀ * n⁻¹ ∈ Subgroup.zpowers y₀ := by rw [hnconj]; exact hc₁
  have hn1 : n * y₀ * n⁻¹ ≠ 1 := by
    intro h
    have : y₀ = 1 := by
      calc y₀ = n⁻¹ * (n * y₀ * n⁻¹) * n := by group
        _ = 1 := by rw [h]; group
    rw [this, orderOf_one] at hy₀3
    omega
  have hnM : n ∈ M := M.mul_mem (hYM hc₁Y) hr₀M
  have hne : n * y₀ * n⁻¹ ≠ y₀ := by
    intro hcomm
    have hnN : n ∈ Subgroup.normalizer (V : Set G) := hMV hnM
    have hr₀N : r₀ ∈ Subgroup.normalizer (V : Set G) := hMV hr₀M
    have hc₁N : c₁ ∈ Subgroup.normalizer (V : Set G) := hYV hc₁Y
    have hcommΦ : Φ ⟨n, hnN⟩ * ρ = ρ * Φ ⟨n, hnN⟩ := by
      rw [hρ, ← map_mul, ← map_mul]
      congr 1
      apply Subtype.ext
      exact mul_inv_eq_iff_eq_mul.mp hcomm
    have hnρ : Φ ⟨n, hnN⟩ ∈ Subgroup.zpowers ρ := by
      rcases gl2_comm_mem ρ _ hρ3 hρ1 hcommΦ with h | h | h
      · rw [h]; exact Subgroup.one_mem _
      · rw [h]; exact Subgroup.mem_zpowers ρ
      · rw [h]; exact Subgroup.pow_mem _ (Subgroup.mem_zpowers ρ) 2
    have hΦn : Φ ⟨n, hnN⟩ = Φ ⟨c₁, hc₁N⟩ * Φ ⟨r₀, hr₀N⟩ := by
      rw [← map_mul]; rfl
    have hr₀Φ : Φ ⟨r₀, hr₀N⟩ ∈ Subgroup.zpowers ρ := by
      have : Φ ⟨r₀, hr₀N⟩ = (Φ ⟨c₁, hc₁N⟩)⁻¹ * Φ ⟨n, hnN⟩ := by rw [hΦn]; group
      rw [this]
      exact Subgroup.mul_mem _ (Subgroup.inv_mem _ (himg c₁ hc₁Y)) hnρ
    have hr₀3 : (Φ ⟨r₀, hr₀N⟩) ^ 3 = 1 := by
      obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hr₀Φ
      rw [← hk, ← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul]
      simp [hρ3]
    obtain ⟨m, hm⟩ := hS2 ⟨r₀, hr₀S⟩
    have hr₀2 : (Φ ⟨r₀, hr₀N⟩) ^ 2 ^ m = 1 := by
      rw [← map_pow]
      have : (⟨r₀, hr₀N⟩ : ↥(Subgroup.normalizer (V : Set G))) ^ 2 ^ m = 1 :=
        Subtype.ext (by simpa using congrArg Subtype.val hm)
      rw [this, map_one]
    have h1 : Φ ⟨r₀, hr₀N⟩ = 1 := eq_one_of_pow_three_pow_two hr₀3 hr₀2
    obtain ⟨v, hv, hmv⟩ := hr₀V
    exact hmv ((hΦ ⟨r₀, hr₀N⟩).mp h1 v hv)
  have hinv : n * y₀ * n⁻¹ = y₀⁻¹ := eq_inv_of_mem_zpowers_order_three hy₀3 hnz hn1 hne
  obtain ⟨e, m, hmodd, hord⟩ := Nat.exists_eq_two_pow_mul_odd (orderOf_pos n).ne'
  set n₂ : G := n ^ m with hn₂
  have hn₂inv : n₂ * y₀ * n₂⁻¹ = y₀⁻¹ := pow_odd_inverts hinv hmodd
  have hn₂2 : n₂ ^ 2 ^ e = 1 := by
    rw [hn₂, ← pow_mul, mul_comm, ← hord]
    exact pow_orderOf_eq_one n
  have hE2 : IsPGroup 2 ↥(Subgroup.zpowers n₂) := by
    intro g
    obtain ⟨j, hj⟩ := Subgroup.mem_zpowers_iff.mp g.2
    refine ⟨e, ?_⟩
    apply Subtype.ext
    simp only [Subgroup.coe_pow, Subgroup.coe_one]
    rw [← hj, ← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hn₂2, one_zpow]
  have hnX : n ∈ Y ⊔ S := Subgroup.mul_mem _ (Subgroup.mem_sup_left hc₁Y) (Subgroup.mem_sup_right hr₀S)
  obtain ⟨h, hhX, hh⟩ := exists_conj_le_of_odd_relIndex (X := Y ⊔ S) (S := S) (E := Subgroup.zpowers n₂)
    le_sup_right (Subgroup.zpowers_le.mpr (Subgroup.pow_mem _ hnX m)) hS2 hodd hE2
  have hset : ((Y ⊔ S : Subgroup G) : Set G) = (Y : Set G) * (S : Set G) :=
    Subgroup.coe_mul_of_right_le_normalizer_left Y S hSY
  rw [← SetLike.mem_coe, hset] at hhX
  obtain ⟨c, hcY, s, hsS, rfl⟩ := hhX
  have h1 : (c * s)⁻¹ * n₂ * (c * s) ∈ S := hh n₂ (Subgroup.mem_zpowers n₂)
  have h2 : c⁻¹ * n₂ * c ∈ S := by
    have e1 : c⁻¹ * n₂ * c = s * ((c * s)⁻¹ * n₂ * (c * s)) * s⁻¹ := by group
    rw [e1]
    exact S.mul_mem (S.mul_mem hsS h1) (S.inv_mem hsS)
  have hcM : c ∈ M := hYM hcY
  have h3 : c⁻¹ * n₂ * c ∈ M :=
    M.mul_mem (M.mul_mem (M.inv_mem hcM) (M.pow_mem hnM m)) hcM
  refine ⟨c⁻¹ * y₀ * c, Y.mul_mem (Y.mul_mem (Y.inv_mem hcY) hy₀) hcY, ?_, ?_,
    c⁻¹ * n₂ * c, ⟨h2, h3⟩, ?_⟩
  · have := orderOf_conj_eq c⁻¹ y₀
    rw [inv_inv] at this
    rw [this, hy₀3]
  · by_contra hcon
    push Not at hcon
    obtain ⟨v, hv, hmv⟩ := hy₀V
    apply hmv
    have hcN : c ∈ Subgroup.normalizer (V : Set G) := hYV hcY
    have hv' : c⁻¹ * v * c ∈ V := by
      have := (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ hcN) v).mp hv
      simpa using this
    have := hcon _ hv'
    calc y₀ * v * y₀⁻¹ = c * ((c⁻¹ * y₀ * c) * (c⁻¹ * v * c) * (c⁻¹ * y₀ * c)⁻¹) * c⁻¹ := by group
      _ = c * (c⁻¹ * v * c) * c⁻¹ := by rw [this]
      _ = v := by group
  · calc (c⁻¹ * n₂ * c) * (c⁻¹ * y₀ * c) * (c⁻¹ * n₂ * c)⁻¹ = c⁻¹ * (n₂ * y₀ * n₂⁻¹) * c := by group
      _ = c⁻¹ * y₀⁻¹ * c := by rw [hn₂inv]
      _ = (c⁻¹ * y₀ * c)⁻¹ := by group

end Main

end Stellmacher.L3YC

end CFSG.Quasithin
