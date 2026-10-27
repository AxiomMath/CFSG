module

public import CFSG.Quasithin.Vol2.Ch5Sec3L3ExcNF
import all CFSG.Fischer.F4

public section

namespace CFSG.Quasithin.H13.Sec53L3

open CFSG.Fischer

theorem f4_add_sq_mem (c : F4) : c + c ^ 2 = 0 ∨ c + c ^ 2 = 1 := by
  obtain ⟨i⟩ := c
  revert i
  decide

theorem f4_sq_eq_self_iff (a : F4) : a ^ 2 = a ↔ a = 0 ∨ a = 1 := by
  obtain ⟨i⟩ := a
  revert i
  decide

theorem f4_add_sq_eq_zero_iff (a : F4) : a + a ^ 2 = 0 ↔ a ^ 2 = a := by
  obtain ⟨i⟩ := a
  revert i
  decide

theorem f4_omega_add_sq : F4.ω + F4.ω ^ 2 = 1 := by decide

theorem f4_one_add_one : (1 : F4) + 1 = 0 := by decide

theorem f4_sq_add {a b : F4} (ha : a ^ 2 = a) (hb : b ^ 2 = b) : (a + b) ^ 2 = a + b := by
  linear_combination ha + hb + F4.two_eq_zero * (a * b)

namespace ExcNF

variable {G : Type} [Group G] {T S V₁ V₂ Z : Subgroup G} (N : ExcNF T S V₁ V₂ Z)

theorem Φ_zero : N.Φ (0, 0, 0) = 1 :=
  N.toHeisCoords.zero

theorem Φ_eq {c a b c' a' b' : F4} (h1 : c = c') (h2 : a = a') (h3 : b = b') :
    N.Φ (c, a, b) = N.Φ (c', a', b') := by
  rw [h1, h2, h3]

theorem Φ_inj {c a b c' a' b' : F4} (h : N.Φ (c, a, b) = N.Φ (c', a', b')) :
    c = c' ∧ a = a' ∧ b = b' := by
  have h' := N.inj h
  rw [Prod.mk.injEq, Prod.mk.injEq] at h'
  exact h'

theorem Φ_inv (c a b : F4) : (N.Φ (c, a, b))⁻¹ = N.Φ (c + a * b, a, b) := by
  rw [inv_eq_iff_mul_eq_one, N.mul, ← N.Φ_zero]
  exact N.Φ_eq (by linear_combination (c + a * b) * F4.two_eq_zero)
    (by linear_combination a * F4.two_eq_zero) (by linear_combination b * F4.two_eq_zero)

theorem Φ_conj (c₀ a₀ b₀ c a b : F4) :
    N.Φ (c₀, a₀, b₀) * N.Φ (c, a, b) * (N.Φ (c₀, a₀, b₀))⁻¹ =
      N.Φ (c + a * b₀ + a₀ * b, a, b) :=
  N.toHeisCoords.conj F4.two_eq_zero c₀ a₀ b₀ c a b

theorem x_inv : N.x⁻¹ = N.x :=
  inv_eq_of_mul_eq_one_right N.x_mul_self

theorem x_mul_Φ (c a b : F4) : N.x * N.Φ (c, a, b) = N.Φ (c ^ 2, a ^ 2, b ^ 2) * N.x := by
  rw [← N.x_act]
  group

theorem Φx_not_mem (p : F4 × F4 × F4) : N.Φ p * N.x ∉ S := fun h =>
  N.x_not_mem (by
    have := S.mul_mem (S.inv_mem (N.mem p)) h
    rwa [inv_mul_cancel_left] at this)

theorem Φ_ne_Φx (p q : F4 × F4 × F4) : N.Φ p ≠ N.Φ q * N.x := fun h =>
  N.Φx_not_mem q (h ▸ N.mem p)

theorem mem_T_iff (hST : S ≤ T) {t : G} :
    t ∈ T ↔ ∃ c a b, t = N.Φ (c, a, b) ∨ t = N.Φ (c, a, b) * N.x := by
  constructor
  · intro ht
    rcases N.cover t ht with h | h
    · obtain ⟨⟨c, a, b⟩, rfl⟩ := N.surj t h
      exact ⟨c, a, b, Or.inl rfl⟩
    · obtain ⟨⟨c, a, b⟩, hp⟩ := N.surj _ h
      refine ⟨c, a, b, Or.inr ?_⟩
      rw [hp, mul_assoc, N.x_mul_self, mul_one]
  · rintro ⟨c, a, b, rfl | rfl⟩
    · exact hST (N.mem _)
    · exact T.mul_mem (hST (N.mem _)) N.x_mem

theorem comm_Φ (c a b c' a' b' : F4) :
    N.Φ (c, a, b) * N.Φ (c', a', b') * (N.Φ (c, a, b))⁻¹ * (N.Φ (c', a', b'))⁻¹ =
      N.Φ (a' * b + a * b', 0, 0) := by
  rw [N.Φ_conj, N.Φ_inv c' a' b', N.mul]
  exact N.Φ_eq (by linear_combination (c' + a' * b') * F4.two_eq_zero)
    (by linear_combination a' * F4.two_eq_zero) (by linear_combination b' * F4.two_eq_zero)

theorem comm_Φ_Φx (c a b c' a' b' : F4) :
    N.Φ (c, a, b) * (N.Φ (c', a', b') * N.x) * (N.Φ (c, a, b))⁻¹ * (N.Φ (c', a', b') * N.x)⁻¹ =
      N.Φ (c + ((c + a * b) ^ 2 + a ^ 2 * b' + a' * b ^ 2) + a ^ 2 * b, a + a ^ 2, b + b ^ 2) := by
  have e : N.Φ (c, a, b) * (N.Φ (c', a', b') * N.x) * (N.Φ (c, a, b))⁻¹ *
      (N.Φ (c', a', b') * N.x)⁻¹ = N.Φ (c, a, b) * (N.Φ (c', a', b') *
        (N.x * (N.Φ (c, a, b))⁻¹ * N.x⁻¹) * (N.Φ (c', a', b'))⁻¹) := by
    rw [mul_inv_rev]
    group
  rw [e, N.Φ_inv c a b, N.x_act, N.Φ_conj, N.mul]

theorem comm_Φx_Φ (c a b c' a' b' : F4) :
    N.Φ (c, a, b) * N.x * N.Φ (c', a', b') * (N.Φ (c, a, b) * N.x)⁻¹ * (N.Φ (c', a', b'))⁻¹ =
      N.Φ (c' ^ 2 + a' ^ 2 * b + a * b' ^ 2 + (c' + a' * b') + a' * b' ^ 2, a' ^ 2 + a',
        b' ^ 2 + b') := by
  have e : N.Φ (c, a, b) * N.x * N.Φ (c', a', b') * (N.Φ (c, a, b) * N.x)⁻¹ *
      (N.Φ (c', a', b'))⁻¹ = N.Φ (c, a, b) * (N.x * N.Φ (c', a', b') * N.x⁻¹) *
        (N.Φ (c, a, b))⁻¹ * (N.Φ (c', a', b'))⁻¹ := by
    group
  rw [e, N.x_act, N.Φ_conj, N.Φ_inv c' a' b', N.mul]

theorem sq_Φ (c a b : F4) : N.Φ (c, a, b) * N.Φ (c, a, b) = N.Φ (a * b, 0, 0) := by
  rw [N.mul]
  exact N.Φ_eq (by linear_combination c * F4.two_eq_zero)
    (by linear_combination a * F4.two_eq_zero) (by linear_combination b * F4.two_eq_zero)

theorem sq_Φx (c a b : F4) : N.Φ (c, a, b) * N.x * (N.Φ (c, a, b) * N.x) =
    N.Φ (c + c ^ 2 + a ^ 2 * b, a + a ^ 2, b + b ^ 2) := by
  have e : N.Φ (c, a, b) * N.x * (N.Φ (c, a, b) * N.x) =
      N.Φ (c, a, b) * (N.x * N.Φ (c, a, b) * N.x⁻¹) * (N.x * N.x) := by
    group
  rw [e, N.x_act, N.x_mul_self, mul_one, N.mul]

theorem z_mul_self : N.Φ (1, 0, 0) * N.Φ (1, 0, 0) = 1 := by
  rw [N.sq_Φ, mul_zero, N.Φ_zero]

theorem mem_zpowers_iff {g : G} :
    g ∈ Subgroup.zpowers (N.Φ (1, 0, 0)) ↔ g = 1 ∨ g = N.Φ (1, 0, 0) := by
  constructor
  · intro hg
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hg
    have h2 : N.Φ (1, 0, 0) ^ (2 : ℤ) = 1 := by
      rw [zpow_two, N.z_mul_self]
    obtain ⟨m, hm | hm⟩ := Int.even_or_odd' k
    · left
      rw [hm, zpow_mul, h2, one_zpow]
    · right
      rw [hm, zpow_add_one, zpow_mul, h2, one_zpow, one_mul]
  · rintro (rfl | rfl)
    · exact Subgroup.one_mem _
    · exact Subgroup.mem_zpowers _

theorem Φ_mem_zpowers_iff {c a b : F4} :
    N.Φ (c, a, b) ∈ Subgroup.zpowers (N.Φ (1, 0, 0)) ↔ (c = 0 ∨ c = 1) ∧ a = 0 ∧ b = 0 := by
  rw [N.mem_zpowers_iff]
  constructor
  · rintro (h | h)
    · rw [← N.Φ_zero] at h
      obtain ⟨h1, h2, h3⟩ := N.Φ_inj h
      exact ⟨Or.inl h1, h2, h3⟩
    · obtain ⟨h1, h2, h3⟩ := N.Φ_inj h
      exact ⟨Or.inr h1, h2, h3⟩
  · rintro ⟨h1 | h1, rfl, rfl⟩ <;> rw [h1]
    · exact Or.inl N.Φ_zero
    · exact Or.inr rfl

theorem eq_zero_of_Φ_mem {c a b : F4} (h : N.Φ (c, a, b) ∈ Subgroup.zpowers (N.Φ (1, 0, 0))) :
    a = 0 ∧ b = 0 :=
  ((N.Φ_mem_zpowers_iff).mp h).2

theorem Φx_not_mem_zpowers (p : F4 × F4 × F4) :
    N.Φ p * N.x ∉ Subgroup.zpowers (N.Φ (1, 0, 0)) := by
  rw [N.mem_zpowers_iff]
  rintro (h | h)
  · exact N.Φ_ne_Φx (0, 0, 0) p (N.Φ_zero.trans h.symm)
  · exact N.Φ_ne_Φx (1, 0, 0) p h.symm

@[expose] def Q : Subgroup G where
  carrier := {g | ∃ c a b : F4, a ^ 2 = a ∧ b ^ 2 = b ∧
    (g = N.Φ (c, a, b) ∨ g = N.Φ (c, a, b) * N.x)}
  mul_mem' := by
    rintro _ _ ⟨c, a, b, ha, hb, rfl | rfl⟩ ⟨c', a', b', ha', hb', rfl | rfl⟩
    · refine ⟨c + c' + a' * b, a + a', b + b', f4_sq_add ha ha', f4_sq_add hb hb', Or.inl ?_⟩
      exact N.mul c a b c' a' b'
    · refine ⟨c + c' + a' * b, a + a', b + b', f4_sq_add ha ha', f4_sq_add hb hb', Or.inr ?_⟩
      rw [← mul_assoc, N.mul]
    · refine ⟨c + c' ^ 2 + a' * b, a + a', b + b', f4_sq_add ha ha', f4_sq_add hb hb',
        Or.inr ?_⟩
      rw [mul_assoc, N.x_mul_Φ, ← mul_assoc, N.mul, ha', hb']
    · refine ⟨c + c' ^ 2 + a' * b, a + a', b + b', f4_sq_add ha ha', f4_sq_add hb hb',
        Or.inl ?_⟩
      have e : N.Φ (c, a, b) * N.x * (N.Φ (c', a', b') * N.x) =
          N.Φ (c, a, b) * (N.x * N.Φ (c', a', b')) * N.x := by group
      rw [e, N.x_mul_Φ, ← mul_assoc, mul_assoc _ N.x N.x, N.x_mul_self, mul_one, N.mul, ha', hb']
  one_mem' := ⟨0, 0, 0, by decide, by decide, Or.inl N.Φ_zero.symm⟩
  inv_mem' := by
    rintro _ ⟨c, a, b, ha, hb, rfl | rfl⟩
    · exact ⟨c + a * b, a, b, ha, hb, Or.inl (N.Φ_inv c a b)⟩
    · refine ⟨(c + a * b) ^ 2, a, b, ha, hb, Or.inr ?_⟩
      show (N.Φ (c, a, b) * N.x)⁻¹ = N.Φ ((c + a * b) ^ 2, a, b) * N.x
      rw [mul_inv_rev, N.x_inv, N.Φ_inv, N.x_mul_Φ, ha, hb]

theorem Q_le (hST : S ≤ T) : N.Q ≤ T := by
  rintro _ ⟨c, a, b, -, -, rfl | rfl⟩
  · exact hST (N.mem _)
  · exact T.mul_mem (hST (N.mem _)) N.x_mem

theorem x_mem_Q : N.x ∈ N.Q :=
  ⟨0, 0, 0, by decide, by decide, Or.inr (by rw [N.Φ_zero, one_mul])⟩

theorem Φ_mem_Q {c a b : F4} (ha : a ^ 2 = a) (hb : b ^ 2 = b) : N.Φ (c, a, b) ∈ N.Q :=
  ⟨c, a, b, ha, hb, Or.inl rfl⟩

theorem comm_mem_zpowers_Z (hST : S ≤ T) (c : F4) {t : G} (ht : t ∈ T) :
    N.Φ (c, 0, 0) * t * (N.Φ (c, 0, 0))⁻¹ * t⁻¹ ∈ Subgroup.zpowers (N.Φ (1, 0, 0)) := by
  obtain ⟨c', a', b', rfl | rfl⟩ := (N.mem_T_iff hST).mp ht
  · rw [N.comm_Φ, N.Φ_mem_zpowers_iff]
    refine ⟨Or.inl (by ring), rfl, rfl⟩
  · rw [N.comm_Φ_Φx, N.Φ_mem_zpowers_iff]
    refine ⟨?_, by ring, by ring⟩
    have e : c + ((c + 0 * 0) ^ 2 + 0 ^ 2 * b' + a' * 0 ^ 2) + 0 ^ 2 * 0 = c + c ^ 2 := by ring
    rw [e]
    exact f4_add_sq_mem c

theorem mem_Q_of_sq (hST : S ≤ T) {y : G} (hyT : y ∈ T) (hyS : y ∉ S)
    (hy : y * y ∈ Subgroup.zpowers (N.Φ (1, 0, 0))) : y ∈ N.Q := by
  obtain ⟨c, a, b, rfl | rfl⟩ := (N.mem_T_iff hST).mp hyT
  · exact absurd (N.mem _) hyS
  · rw [N.sq_Φx] at hy
    obtain ⟨ha, hb⟩ := N.eq_zero_of_Φ_mem hy
    exact ⟨c, a, b, (f4_add_sq_eq_zero_iff a).mp ha, (f4_add_sq_eq_zero_iff b).mp hb, Or.inr rfl⟩

theorem Q_le_of (hST : S ≤ T) {W : Subgroup G} (hZW : ∀ c, N.Φ (c, 0, 0) ∈ W)
    (hTW : ∀ t ∈ T, ∀ g ∈ W, t * g * t⁻¹ ∈ W) {v : G} (hvW : v ∈ W) (hvS : v ∉ S)
    (hvQ : v ∈ N.Q) : N.Q ≤ W := by
  obtain ⟨c', a', b', ha', hb', rfl | rfl⟩ := hvQ
  · exact absurd (N.mem _) hvS
  have hcomm : ∀ c a b : F4, N.Φ (c, a, b) * (N.Φ (c', a', b') * N.x) * (N.Φ (c, a, b))⁻¹ *
      (N.Φ (c', a', b') * N.x)⁻¹ ∈ W := fun c a b =>
    W.mul_mem (hTW _ (hST (N.mem _)) _ hvW) (W.inv_mem hvW)
  have h10 : ∀ c, N.Φ (c, 1, 0) ∈ W := by
    intro c
    have h1 := hcomm 0 F4.ω 0
    rw [N.comm_Φ_Φx] at h1
    have e1 : N.Φ (0 + ((0 + F4.ω * 0) ^ 2 + F4.ω ^ 2 * b' + a' * 0 ^ 2) + F4.ω ^ 2 * 0,
        F4.ω + F4.ω ^ 2, 0 + 0 ^ 2) = N.Φ (F4.ω ^ 2 * b', 1, 0) :=
      N.Φ_eq (by ring) f4_omega_add_sq (by ring)
    rw [e1] at h1
    have e2 : N.Φ (c + F4.ω ^ 2 * b', 0, 0) * N.Φ (F4.ω ^ 2 * b', 1, 0) = N.Φ (c, 1, 0) := by
      rw [N.mul]
      exact N.Φ_eq (by linear_combination (F4.ω ^ 2 * b') * F4.two_eq_zero) (by ring) (by ring)
    rw [← e2]
    exact W.mul_mem (hZW _) h1
  have h01 : ∀ c, N.Φ (c, 0, 1) ∈ W := by
    intro c
    have h1 := hcomm 0 0 F4.ω
    rw [N.comm_Φ_Φx] at h1
    have e1 : N.Φ (0 + ((0 + 0 * F4.ω) ^ 2 + 0 ^ 2 * b' + a' * F4.ω ^ 2) + 0 ^ 2 * F4.ω,
        0 + 0 ^ 2, F4.ω + F4.ω ^ 2) = N.Φ (a' * F4.ω ^ 2, 0, 1) :=
      N.Φ_eq (by ring) (by ring) f4_omega_add_sq
    rw [e1] at h1
    have e2 : N.Φ (c + a' * F4.ω ^ 2, 0, 0) * N.Φ (a' * F4.ω ^ 2, 0, 1) = N.Φ (c, 0, 1) := by
      rw [N.mul]
      exact N.Φ_eq (by linear_combination (a' * F4.ω ^ 2) * F4.two_eq_zero) (by ring) (by ring)
    rw [← e2]
    exact W.mul_mem (hZW _) h1
  have hS : ∀ c a b : F4, a ^ 2 = a → b ^ 2 = b → N.Φ (c, a, b) ∈ W := by
    intro c a b ha hb
    rcases (f4_sq_eq_self_iff a).mp ha with rfl | rfl <;>
      rcases (f4_sq_eq_self_iff b).mp hb with rfl | rfl
    · exact hZW c
    · exact h01 c
    · exact h10 c
    · have e : N.Φ (c, 1, 0) * N.Φ (0, 0, 1) = N.Φ (c, 1, 1) := by
        rw [N.mul]
        exact N.Φ_eq (by ring) (by ring) (by ring)
      rw [← e]
      exact W.mul_mem (h10 c) (h01 0)
  rintro _ ⟨c, a, b, ha, hb, rfl | rfl⟩
  · exact hS c a b ha hb
  · have e : N.Φ (c, a, b) * N.x =
        (N.Φ (c, a, b) * N.Φ (c' + a' * b', a', b')) * (N.Φ (c', a', b') * N.x) := by
      rw [← N.Φ_inv]
      group
    rw [e, N.mul]
    exact W.mul_mem (hS _ _ _ (f4_sq_add ha ha') (f4_sq_add hb hb')) hvW

theorem mem_Q_of_comm_Q (hST : S ≤ T) {t : G} (htT : t ∈ T)
    (h : ∀ q ∈ N.Q, t * q * t⁻¹ * q⁻¹ ∈ Subgroup.zpowers (N.Φ (1, 0, 0))) : t ∈ N.Q := by
  obtain ⟨c, a, b, rfl | rfl⟩ := (N.mem_T_iff hST).mp htT
  · have h1 := h _ N.x_mem_Q
    have e : N.x = N.Φ (0, 0, 0) * N.x := by rw [N.Φ_zero, one_mul]
    rw [e, N.comm_Φ_Φx] at h1
    obtain ⟨ha, hb⟩ := N.eq_zero_of_Φ_mem h1
    exact N.Φ_mem_Q ((f4_add_sq_eq_zero_iff a).mp ha) ((f4_add_sq_eq_zero_iff b).mp hb)
  · have h1 := h _ (N.Φ_mem_Q (c := 0) (a := 1) (b := 0) (by decide) (by decide))
    have h2 := h _ (N.Φ_mem_Q (c := 0) (a := 0) (b := 1) (by decide) (by decide))
    rw [N.comm_Φx_Φ] at h1 h2
    have e1 : N.Φ (0 ^ 2 + 1 ^ 2 * b + a * 0 ^ 2 + (0 + 1 * 0) + 1 * 0 ^ 2, 1 ^ 2 + 1,
        0 ^ 2 + 0) = N.Φ (b, 0, 0) :=
      N.Φ_eq (by ring) (by rw [one_pow]; exact f4_one_add_one) (by ring)
    have e2 : N.Φ (0 ^ 2 + 0 ^ 2 * b + a * 1 ^ 2 + (0 + 0 * 1) + 0 * 1 ^ 2, 0 ^ 2 + 0,
        1 ^ 2 + 1) = N.Φ (a, 0, 0) :=
      N.Φ_eq (by ring) (by ring) (by rw [one_pow]; exact f4_one_add_one)
    rw [e1, N.Φ_mem_zpowers_iff] at h1
    rw [e2, N.Φ_mem_zpowers_iff] at h2
    exact ⟨c, a, b, (f4_sq_eq_self_iff a).mpr h2.1, (f4_sq_eq_self_iff b).mpr h1.1, Or.inr rfl⟩

include N in
theorem centerOf_eq {Y : Subgroup G} (hYS : Y ≤ S) (hZY : Z ≤ Y)
    (hY : ∃ y₁ ∈ Y, ∃ y₂ ∈ Y, y₁ * y₂ ≠ y₂ * y₁) : centerOf Y = Z := by
  obtain ⟨y₁, hy₁, y₂, hy₂, hne⟩ := hY
  obtain ⟨⟨c₁, a₁, b₁⟩, rfl⟩ := N.surj y₁ (hYS hy₁)
  obtain ⟨⟨c₂, a₂, b₂⟩, rfl⟩ := N.surj y₂ (hYS hy₂)
  rw [N.mul, N.mul] at hne
  have hd : a₂ * b₁ - a₁ * b₂ ≠ 0 := by
    intro h0
    apply hne
    exact N.Φ_eq (by linear_combination h0) (by ring) (by ring)
  apply le_antisymm
  · intro y hy
    obtain ⟨hyY, hyc⟩ := Subgroup.mem_inf.mp hy
    obtain ⟨⟨c, a, b⟩, rfl⟩ := N.surj y (hYS hyY)
    have hc₁ := Subgroup.mem_centralizer_iff.mp hyc _ hy₁
    have hc₂ := Subgroup.mem_centralizer_iff.mp hyc _ hy₂
    rw [N.mul, N.mul] at hc₁ hc₂
    have e₁ := (N.Φ_inj hc₁).1
    have e₂ := (N.Φ_inj hc₂).1
    have ha : a = 0 := by
      have : a * (a₂ * b₁ - a₁ * b₂) = 0 := by linear_combination a₂ * e₁ - a₁ * e₂
      exact (mul_eq_zero.mp this).resolve_right hd
    have hb : b = 0 := by
      have : b * (a₂ * b₁ - a₁ * b₂) = 0 := by linear_combination b₂ * e₁ - b₁ * e₂
      exact (mul_eq_zero.mp this).resolve_right hd
    rw [ha, hb, N.mem_Z]
    exact ⟨c, rfl⟩
  · intro g hg
    refine Subgroup.mem_inf.mpr ⟨hZY hg, Subgroup.mem_centralizer_iff.mpr fun y hy => ?_⟩
    obtain ⟨c, rfl⟩ := (N.mem_Z g).mp hg
    obtain ⟨⟨c', a', b'⟩, rfl⟩ := N.surj y (hYS hy)
    rw [N.mul, N.mul]
    exact N.Φ_eq (by ring) (by ring) (by ring)

end ExcNF

end CFSG.Quasithin.H13.Sec53L3
