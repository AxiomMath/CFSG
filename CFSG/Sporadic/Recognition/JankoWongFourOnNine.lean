module

public import Mathlib.Data.ZMod.QuotientGroup
public import Mathlib.Tactic.Group

public section

namespace CFSG.Sporadic.Recognition.JankoWong

theorem conj_sq_eq_conj_conj {G : Type*} [Group G] (g x : G) :
    g ^ 2 * x * (g ^ 2)⁻¹ = g * (g * x * g⁻¹) * g⁻¹ := by
  simp only [pow_two, mul_inv_rev, mul_assoc]

theorem eq_one_of_pow_three_of_eq_inv {G : Type*} [Group G] {x : G} (h3 : x ^ 3 = 1)
    (hx : x = x⁻¹) : x = 1 := by
  have h2 : x * x = 1 := mul_eq_one_iff_eq_inv.mpr hx
  calc x = x * (x * x) := by rw [h2, mul_one]
    _ = x ^ 3 := (pow_three x).symm
    _ = 1 := h3

theorem closure_pair_eq_of_card_eq_nine {G : Type*} [Group G] {Z : Subgroup G}
    (hZ : Nat.card Z = 9) {u v : G} (hu : u ∈ Z) (hv : v ∈ Z) (hu3 : u ^ 3 = 1) (hu1 : u ≠ 1)
    (hvu : v ∉ Subgroup.zpowers u) : Subgroup.closure ({u, v} : Set G) = Z := by
  have hord : orderOf u = 3 := orderOf_eq_prime hu3 hu1
  have hKZ : Subgroup.closure ({u, v} : Set G) ≤ Z := by
    rw [Subgroup.closure_le]
    rintro x (rfl | rfl)
    exacts [hu, hv]
  have huK : Subgroup.zpowers u ≤ Subgroup.closure ({u, v} : Set G) :=
    Subgroup.zpowers_le.mpr (Subgroup.subset_closure (Set.mem_insert u {v}))
  have hvK : v ∈ Subgroup.closure ({u, v} : Set G) :=
    Subgroup.subset_closure (Set.mem_insert_of_mem u rfl)
  have hK9 : Nat.card (Subgroup.closure ({u, v} : Set G)) ∣ 9 :=
    hZ ▸ Subgroup.card_dvd_of_le hKZ
  have h3K : 3 ∣ Nat.card (Subgroup.closure ({u, v} : Set G)) := by
    rw [← hord, ← Nat.card_zpowers]
    exact Subgroup.card_dvd_of_le huK
  have hKfin : Finite (Subgroup.closure ({u, v} : Set G)) :=
    Nat.finite_of_card_ne_zero (Nat.pos_of_dvd_of_pos hK9 (by norm_num)).ne'
  have hne : Nat.card (Subgroup.closure ({u, v} : Set G)) ≠ 3 := by
    intro h3
    apply hvu
    have : Subgroup.zpowers u = Subgroup.closure ({u, v} : Set G) :=
      Subgroup.eq_of_le_of_card_ge huK (by rw [h3, Nat.card_zpowers, hord])
    exact this ▸ hvK
  have h9 : Nat.card (Subgroup.closure ({u, v} : Set G)) = 9 := by
    have key : ∀ n : ℕ, n < 10 → 3 ∣ n → n ∣ 9 → n ≠ 3 → n = 9 := by decide
    exact key _ (Nat.lt_succ_of_le (Nat.le_of_dvd (by norm_num) hK9)) h3K hK9 hne
  have : Finite Z := Nat.finite_of_card_ne_zero (by omega)
  exact Subgroup.eq_of_le_of_card_ge hKZ (by rw [hZ, h9])

theorem conj_eq_inv_of_mem_closure_pair_of_abelian {G : Type*} [Group G] {Z : Subgroup G}
    (hab : ∀ x ∈ Z, ∀ y ∈ Z, x * y = y * x) {q u v z : G} (hu : u ∈ Z) (hv : v ∈ Z)
    (hqu : q * u * q⁻¹ = u⁻¹) (hqv : q * v * q⁻¹ = v⁻¹)
    (hz : z ∈ Subgroup.closure ({u, v} : Set G)) : q * z * q⁻¹ = z⁻¹ := by
  have hle : Subgroup.closure ({u, v} : Set G) ≤ Z := by
    rw [Subgroup.closure_le]
    rintro x (rfl | rfl)
    exacts [hu, hv]
  induction hz using Subgroup.closure_induction with
  | mem x hx =>
    rcases hx with rfl | rfl
    · exact hqu
    · exact hqv
  | one => simp
  | mul x y hx hy ihx ihy =>
    have hxy : x * y = y * x := hab x (hle hx) y (hle hy)
    calc q * (x * y) * q⁻¹ = (q * x * q⁻¹) * (q * y * q⁻¹) := by group
      _ = x⁻¹ * y⁻¹ := by rw [ihx, ihy]
      _ = (y * x)⁻¹ := (mul_inv_rev y x).symm
      _ = (x * y)⁻¹ := by rw [hxy]
  | inv x hx ih =>
    calc q * x⁻¹ * q⁻¹ = (q * x * q⁻¹)⁻¹ := by group
      _ = (x⁻¹)⁻¹ := by rw [ih]

theorem conj_sq_eq_of_conj_mem_zpowers {G : Type*} [Group G] {u g : G} (hu3 : u ^ 3 = 1)
    (hu1 : u ≠ 1) (hg : g * u * g⁻¹ ∈ Subgroup.zpowers u) :
    g * (g * u * g⁻¹) * g⁻¹ = u := by
  have hord : orderOf u = 3 := orderOf_eq_prime hu3 hu1
  obtain ⟨n, hn⟩ := Subgroup.mem_zpowers_iff.mp hg
  have hmod : u ^ (n % 3) = u ^ n := by
    have := zpow_mod_orderOf u n
    rwa [hord] at this
  have hcases : n % 3 = 0 ∨ n % 3 = 1 ∨ n % 3 = 2 := by omega
  rcases hcases with h | h | h
  · exfalso
    rw [h, zpow_zero] at hmod
    have h1 : g * u * g⁻¹ = 1 := by rw [← hn, ← hmod]
    apply hu1
    calc u = g⁻¹ * (g * u * g⁻¹) * g := by group
      _ = 1 := by rw [h1]; group
  · rw [h, zpow_one] at hmod
    have h1 : g * u * g⁻¹ = u := by rw [← hn, ← hmod]
    rw [h1, h1]
  · rw [h] at hmod
    have h1 : g * u * g⁻¹ = u⁻¹ := by
      rw [← hn, ← hmod, zpow_two]
      exact mul_eq_one_iff_eq_inv.mp (by rw [← pow_three']; exact hu3)
    calc g * (g * u * g⁻¹) * g⁻¹ = g * u⁻¹ * g⁻¹ := by rw [h1]
      _ = (g * u * g⁻¹)⁻¹ := by group
      _ = u := by rw [h1, inv_inv]

theorem false_of_four_acting_on_nine {G : Type*} [Group G] (Z : Subgroup G)
    (hZ : Nat.card Z = 9) (hab : ∀ x ∈ Z, ∀ y ∈ Z, x * y = y * x)
    (hexp : ∀ x ∈ Z, x ^ 3 = 1) {a g : G} (haZ : a ∈ Z) (ha1 : a ≠ 1)
    (hga : g * a * g⁻¹ = a) (hg4 : g ^ 4 = 1) (hgZ : ∀ x ∈ Z, g * x * g⁻¹ ∈ Z)
    (hq : ∃ y ∈ Z, g ^ 2 * y * (g ^ 2)⁻¹ ≠ y) : False := by
  obtain ⟨y, hyZ, hy⟩ := hq
  obtain ⟨y', hy'⟩ : ∃ y' : G, y' = g ^ 2 * y * (g ^ 2)⁻¹ := ⟨_, rfl⟩
  have hy'Z : y' ∈ Z := by
    have : y' = g * (g * y * g⁻¹) * g⁻¹ := hy'.trans (conj_sq_eq_conj_conj g y)
    exact this ▸ hgZ _ (hgZ _ hyZ)
  have hy'y : g ^ 2 * y' * (g ^ 2)⁻¹ = y := by
    calc g ^ 2 * y' * (g ^ 2)⁻¹ = g ^ 4 * y * (g ^ 4)⁻¹ := by rw [hy']; group
      _ = y := by rw [hg4]; group
  obtain ⟨u, hu⟩ : ∃ u : G, u = y * y'⁻¹ := ⟨_, rfl⟩
  have huZ : u ∈ Z := hu ▸ Z.mul_mem hyZ (Z.inv_mem hy'Z)
  have hu1 : u ≠ 1 := by
    intro h
    apply hy
    rw [← hy']
    exact (mul_inv_eq_one.mp (hu ▸ h)).symm
  have hu3 : u ^ 3 = 1 := hexp u huZ
  have hqu : g ^ 2 * u * (g ^ 2)⁻¹ = u⁻¹ := by
    calc g ^ 2 * u * (g ^ 2)⁻¹
        = (g ^ 2 * y * (g ^ 2)⁻¹) * (g ^ 2 * y' * (g ^ 2)⁻¹)⁻¹ := by rw [hu]; group
      _ = y' * y⁻¹ := by rw [← hy', hy'y]
      _ = u⁻¹ := by rw [hu]; group
  have hu'Z : g * u * g⁻¹ ∈ Z := hgZ u huZ
  have hqu' : g ^ 2 * (g * u * g⁻¹) * (g ^ 2)⁻¹ = (g * u * g⁻¹)⁻¹ := by
    calc g ^ 2 * (g * u * g⁻¹) * (g ^ 2)⁻¹ = g * (g ^ 2 * u * (g ^ 2)⁻¹) * g⁻¹ := by group
      _ = g * u⁻¹ * g⁻¹ := by rw [hqu]
      _ = (g * u * g⁻¹)⁻¹ := by group
  have hqa : g ^ 2 * a * (g ^ 2)⁻¹ = a := by
    rw [conj_sq_eq_conj_conj, hga, hga]
  have hmem : g * u * g⁻¹ ∈ Subgroup.zpowers u := by
    by_contra hnot
    have hcl := closure_pair_eq_of_card_eq_nine hZ huZ hu'Z hu3 hu1 hnot
    have haK : a ∈ Subgroup.closure ({u, g * u * g⁻¹} : Set G) := by
      rw [hcl]
      exact haZ
    have hinv := conj_eq_inv_of_mem_closure_pair_of_abelian hab huZ hu'Z hqu hqu' haK
    rw [hqa] at hinv
    exact ha1 (eq_one_of_pow_three_of_eq_inv (hexp a haZ) hinv)
  have hsq := conj_sq_eq_of_conj_mem_zpowers hu3 hu1 hmem
  apply hu1
  apply eq_one_of_pow_three_of_eq_inv hu3
  calc u = g * (g * u * g⁻¹) * g⁻¹ := hsq.symm
    _ = g ^ 2 * u * (g ^ 2)⁻¹ := (conj_sq_eq_conj_conj g u).symm
    _ = u⁻¹ := hqu

end CFSG.Sporadic.Recognition.JankoWong
