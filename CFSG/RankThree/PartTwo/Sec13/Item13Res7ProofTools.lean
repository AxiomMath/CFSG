module

public import CFSG.RankThree.PartOne.S12.Sec159Tools

public section

namespace CFSG.RankThree.PartTwo.Sec13.Res7Proof

open CFSG

section Coset

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem eq_one_or_eq_of_mem_zpowers {x u : G} (hx : x * x = 1) (hu : u ∈ Subgroup.zpowers x) :
    u = 1 ∨ u = x := by
  obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.mp hu
  have hx2 : x ^ (2 : ℤ) = 1 := by rw [zpow_two, hx]
  rw [zpow_eq_zpow_emod n hx2]
  rcases Int.emod_two_eq_zero_or_one n with h | h
  · left
    rw [h, zpow_zero]
  · right
    rw [h, zpow_one]

omit [Finite G] in
theorem isPGroup_zpowers_of_involution {x : G} (hx : x * x = 1) :
    IsPGroup 2 (Subgroup.zpowers x) := by
  intro g
  refine ⟨1, Subtype.ext ?_⟩
  rcases eq_one_or_eq_of_mem_zpowers hx g.2 with h | h
  · simp [h]
  · simp [h, pow_two, hx]

omit [Finite G] in
theorem exists_fixed_two_involutions {V : Subgroup G} (hV : Odd (Nat.card V)) {x₁ x₂ k : G}
    (h₁ : x₁ * x₁ = 1) (h₂ : x₂ * x₂ = 1) (h₁₂ : x₁ * x₂ = x₂ * x₁)
    (h₁V : x₁ ∈ Subgroup.normalizer (V : Set G)) (h₂V : x₂ ∈ Subgroup.normalizer (V : Set G))
    (hkV : k ∈ Subgroup.normalizer (V : Set G)) (h₁k : x₁ * k * x₁⁻¹ * k⁻¹ ∈ V)
    (h₂k : x₂ * k * x₂⁻¹ * k⁻¹ ∈ V) :
    ∃ v ∈ V, (k * v) * x₁ = x₁ * (k * v) ∧ (k * v) * x₂ = x₂ * (k * v) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hV2 : ¬ 2 ∣ Nat.card V := by
    rw [← even_iff_two_dvd]
    exact Nat.not_even_iff_odd.mpr hV
  have hU₁V : Subgroup.zpowers x₁ ≤ Subgroup.normalizer (V : Set G) :=
    (Subgroup.zpowers_le).mpr h₁V
  obtain ⟨v₁, hv₁, hfix₁⟩ := PartOne.Sec159.exists_fixed_in_coset
    (isPGroup_zpowers_of_involution h₁) hV2 hU₁V hkV (fun u hu => by
      rcases eq_one_or_eq_of_mem_zpowers h₁ hu with rfl | rfl
      · simp
      · exact h₁k)
  have hk₁ : (k * v₁) * x₁ = x₁ * (k * v₁) := by
    have := hfix₁ x₁ (Subgroup.mem_zpowers x₁)
    calc (k * v₁) * x₁ = x₁ * (k * v₁) * x₁⁻¹ * x₁ := by rw [this]
      _ = x₁ * (k * v₁) := by group
  set V₂ := V ⊓ Subgroup.centralizer {x₁} with hV₂
  have hV₂odd : ¬ 2 ∣ Nat.card V₂ := fun h =>
    hV2 (h.trans (Subgroup.card_dvd_of_le inf_le_left))
  have hcent : ∀ g : G, g * x₁ = x₁ * g → g ∈ Subgroup.normalizer
      (Subgroup.centralizer ({x₁} : Set G) : Set G) := fun g hg =>
    Subgroup.le_normalizer (Subgroup.mem_centralizer_singleton_iff.mpr hg)
  have hinf : ∀ g : G, g ∈ Subgroup.normalizer (V : Set G) → g * x₁ = x₁ * g →
      g ∈ Subgroup.normalizer (V₂ : Set G) := by
    intro g hgV hg
    have h1 := hcent g hg
    rw [Subgroup.mem_normalizer_iff] at h1 hgV ⊢
    intro h
    rw [hV₂, Subgroup.mem_inf, Subgroup.mem_inf, hgV h, h1 h]
  have hx₂N : x₂ ∈ Subgroup.normalizer (V₂ : Set G) := hinf x₂ h₂V h₁₂.symm
  have hU₂V : Subgroup.zpowers x₂ ≤ Subgroup.normalizer (V₂ : Set G) :=
    (Subgroup.zpowers_le).mpr hx₂N
  have hkvN : k * v₁ ∈ Subgroup.normalizer (V₂ : Set G) :=
    hinf _ (mul_mem hkV (Subgroup.le_normalizer hv₁)) hk₁
  have hx₂kv : x₂ * (k * v₁) * x₂⁻¹ * (k * v₁)⁻¹ ∈ V₂ := by
    refine Subgroup.mem_inf.mpr ⟨?_, ?_⟩
    · have h1 : x₂ * v₁ * x₂⁻¹ ∈ V := (Subgroup.mem_normalizer_iff.mp h₂V v₁).mp hv₁
      have h2 : k * (x₂ * v₁ * x₂⁻¹ * v₁⁻¹) * k⁻¹ ∈ V :=
        (Subgroup.mem_normalizer_iff.mp hkV _).mp (mul_mem h1 (inv_mem hv₁))
      have : x₂ * (k * v₁) * x₂⁻¹ * (k * v₁)⁻¹ =
          (x₂ * k * x₂⁻¹ * k⁻¹) * (k * (x₂ * v₁ * x₂⁻¹ * v₁⁻¹) * k⁻¹) := by group
      rw [this]
      exact mul_mem h₂k h2
    · rw [Subgroup.mem_centralizer_singleton_iff]
      have hx₂inv : x₂⁻¹ * x₁ = x₁ * x₂⁻¹ := by
        rw [inv_mul_eq_iff_eq_mul, ← mul_assoc, ← h₁₂, mul_assoc, mul_inv_cancel, mul_one]
      have hkinv : (k * v₁)⁻¹ * x₁ = x₁ * (k * v₁)⁻¹ := by
        rw [inv_mul_eq_iff_eq_mul, ← mul_assoc, hk₁, mul_assoc, mul_inv_cancel, mul_one]
      calc x₂ * (k * v₁) * x₂⁻¹ * (k * v₁)⁻¹ * x₁
          = x₂ * (k * v₁) * x₂⁻¹ * ((k * v₁)⁻¹ * x₁) := by group
        _ = x₂ * (k * v₁) * (x₂⁻¹ * x₁) * (k * v₁)⁻¹ := by rw [hkinv]; group
        _ = x₂ * ((k * v₁) * x₁) * x₂⁻¹ * (k * v₁)⁻¹ := by rw [hx₂inv]; group
        _ = (x₂ * x₁) * (k * v₁) * x₂⁻¹ * (k * v₁)⁻¹ := by rw [hk₁]; group
        _ = x₁ * (x₂ * (k * v₁) * x₂⁻¹ * (k * v₁)⁻¹) := by rw [← h₁₂]; group
  obtain ⟨v₂, hv₂, hfix₂⟩ := PartOne.Sec159.exists_fixed_in_coset
    (isPGroup_zpowers_of_involution h₂) hV₂odd hU₂V hkvN (fun u hu => by
      rcases eq_one_or_eq_of_mem_zpowers h₂ hu with rfl | rfl
      · simp
      · exact hx₂kv)
  refine ⟨v₁ * v₂, mul_mem hv₁ (Subgroup.mem_inf.mp hv₂).1, ?_, ?_⟩
  · have hv₂x : v₂ * x₁ = x₁ * v₂ :=
      Subgroup.mem_centralizer_singleton_iff.mp (Subgroup.mem_inf.mp hv₂).2
    calc k * (v₁ * v₂) * x₁ = (k * v₁) * (v₂ * x₁) := by group
      _ = (k * v₁) * x₁ * v₂ := by rw [hv₂x]; group
      _ = x₁ * (k * (v₁ * v₂)) := by rw [hk₁]; group
  · have := hfix₂ x₂ (Subgroup.mem_zpowers x₂)
    calc k * (v₁ * v₂) * x₂ = x₂ * (k * v₁ * v₂) * x₂⁻¹ * x₂ := by rw [this]; group
      _ = x₂ * (k * (v₁ * v₂)) := by group

end Coset

section Parts

variable {G : Type*} [Group G] [Finite G]

theorem exists_two_part {T : Type*} [Group T] (ψ : G →* T) {a : T} (ha : a * a = 1) (y' : G)
    (hy' : ψ y' = a) : ∃ y ∈ Subgroup.zpowers y', (∃ r : ℕ, y ^ 2 ^ r = 1) ∧ ψ y = a := by
  obtain ⟨r, m, hm, hn⟩ := Nat.exists_eq_two_pow_mul_odd (orderOf_pos y').ne'
  refine ⟨y' ^ m, ⟨m, by simp⟩, ⟨r, ?_⟩, ?_⟩
  · rw [← pow_mul, mul_comm, ← hn, pow_orderOf_eq_one]
  · obtain ⟨k, rfl⟩ := hm
    rw [map_pow, hy', pow_succ, pow_mul, sq, ha, one_pow, one_mul]

omit [Finite G] in
theorem exists_orderOf_eq_two_pow_succ {y : G} (hy : ∃ r : ℕ, y ^ 2 ^ r = 1) (hy1 : y ≠ 1) :
    ∃ s : ℕ, orderOf y = 2 ^ (s + 1) := by
  obtain ⟨r, hr⟩ := hy
  obtain ⟨t, -, ht⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp (orderOf_dvd_of_pow_eq_one hr)
  rcases t with _ | s
  · exact absurd (orderOf_eq_one_iff.mp (by simpa using ht)) hy1
  · exact ⟨s, ht⟩

omit [Finite G] in
theorem orderOf_two_pow_pred {y : G} {s : ℕ} (hy : orderOf y = 2 ^ (s + 1)) :
    orderOf (y ^ 2 ^ s) = 2 := by
  rw [orderOf_pow' y (by positivity), hy]
  have hg : Nat.gcd (2 ^ (s + 1)) (2 ^ s) = 2 ^ s :=
    Nat.gcd_eq_right (Nat.pow_dvd_pow 2 (Nat.le_succ s))
  rw [hg, pow_succ, Nat.mul_div_cancel_left _ (by positivity)]

end Parts

@[expose] def permA : Equiv.Perm (Fin 7) := Equiv.swap 0 1 * Equiv.swap 2 3

@[expose] def permB : Equiv.Perm (Fin 7) := Equiv.swap 0 2 * Equiv.swap 1 3

theorem permA_mem : permA ∈ alternatingGroup (Fin 7) := by
  change Equiv.Perm.sign permA = 1
  rw [permA, Equiv.Perm.sign_mul, Equiv.Perm.sign_swap (by decide : (0 : Fin 7) ≠ 1),
    Equiv.Perm.sign_swap (by decide : (2 : Fin 7) ≠ 3)]
  norm_num

theorem permB_mem : permB ∈ alternatingGroup (Fin 7) := by
  change Equiv.Perm.sign permB = 1
  rw [permB, Equiv.Perm.sign_mul, Equiv.Perm.sign_swap (by decide : (0 : Fin 7) ≠ 2),
    Equiv.Perm.sign_swap (by decide : (1 : Fin 7) ≠ 3)]
  norm_num

@[expose] def a7a : alternatingGroup (Fin 7) := ⟨permA, permA_mem⟩

@[expose] def a7b : alternatingGroup (Fin 7) := ⟨permB, permB_mem⟩

theorem a7a_sq : a7a * a7a = 1 := Subtype.ext (by decide)

theorem a7b_sq : a7b * a7b = 1 := Subtype.ext (by decide)

theorem a7ab_sq : a7a * a7b * (a7a * a7b) = 1 := Subtype.ext (by decide)

theorem a7ab_comm : a7a * a7b = a7b * a7a := Subtype.ext (by decide)

theorem a7a_ne_one : a7a ≠ 1 := fun h => by
  have := congrArg Subtype.val h
  revert this
  decide

theorem a7b_ne_one : a7b ≠ 1 := fun h => by
  have := congrArg Subtype.val h
  revert this
  decide

theorem a7ab_ne_one : a7a * a7b ≠ 1 := fun h => by
  have := congrArg Subtype.val h
  revert this
  decide

theorem a7a_ne_a7b : a7a ≠ a7b := fun h => by
  have := congrArg Subtype.val h
  revert this
  decide

@[expose] def kleinA7 : Subgroup (alternatingGroup (Fin 7)) := Subgroup.closure {a7a, a7b}

theorem a7a_mul_ab : a7a * (a7a * a7b) = a7b := by rw [← mul_assoc, a7a_sq, one_mul]

theorem a7b_mul_ab : a7b * (a7a * a7b) = a7a := by
  rw [a7ab_comm, ← mul_assoc, a7b_sq, one_mul]

theorem ab_mul_a7a : a7a * a7b * a7a = a7b := by
  rw [a7ab_comm, mul_assoc, a7a_sq, mul_one]

theorem ab_mul_a7b : a7a * a7b * a7b = a7a := by rw [mul_assoc, a7b_sq, mul_one]

theorem a7a_inv : a7a⁻¹ = a7a := inv_eq_of_mul_eq_one_right a7a_sq

theorem a7b_inv : a7b⁻¹ = a7b := inv_eq_of_mul_eq_one_right a7b_sq

theorem a7ab_inv : (a7a * a7b)⁻¹ = a7a * a7b := inv_eq_of_mul_eq_one_right a7ab_sq

theorem mem_kleinA7 {g : alternatingGroup (Fin 7)} (hg : g ∈ kleinA7) :
    g = 1 ∨ g = a7a ∨ g = a7b ∨ g = a7a * a7b := by
  induction hg using Subgroup.closure_induction with
  | mem x hx =>
    rcases hx with rfl | rfl
    · exact Or.inr (Or.inl rfl)
    · exact Or.inr (Or.inr (Or.inl rfl))
  | one => exact Or.inl rfl
  | mul x y _ _ hx hy =>
    rcases hx with rfl | rfl | rfl | rfl <;> rcases hy with rfl | rfl | rfl | rfl <;>
      simp only [one_mul, mul_one, a7a_sq, a7b_sq, a7ab_sq, a7a_mul_ab, a7b_mul_ab,
        ab_mul_a7a, ab_mul_a7b, ← a7ab_comm, true_or, or_true]
  | inv x _ hx =>
    rcases hx with rfl | rfl | rfl | rfl <;>
      simp only [inv_one, a7a_inv, a7b_inv, a7ab_inv, true_or, or_true]

theorem isPGroup_kleinA7 : IsPGroup 2 kleinA7 := by
  intro g
  refine ⟨1, Subtype.ext ?_⟩
  rw [pow_one, Subgroup.coe_pow, OneMemClass.coe_one]
  rcases mem_kleinA7 g.2 with h | h | h | h <;> rw [h, sq]
  exacts [mul_one 1, a7a_sq, a7b_sq, a7ab_sq]

@[expose] def a6a : alternatingGroup (Fin 6) :=
  ⟨Equiv.swap 0 1 * Equiv.swap 2 3, by
    change Equiv.Perm.sign _ = 1
    rw [Equiv.Perm.sign_mul, Equiv.Perm.sign_swap (by decide : (0 : Fin 6) ≠ 1),
      Equiv.Perm.sign_swap (by decide : (2 : Fin 6) ≠ 3)]
    norm_num⟩

theorem a6a_sq : a6a * a6a = 1 := Subtype.ext (by decide)

theorem a6a_ne_one : a6a ≠ 1 := fun h => by
  have := congrArg Subtype.val h
  revert this
  decide

end CFSG.RankThree.PartTwo.Sec13.Res7Proof
