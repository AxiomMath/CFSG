module

public import Mathlib.LinearAlgebra.Matrix.SpecialLinearGroup
public import Mathlib.Tactic.NormNum.Prime
public import Mathlib.GroupTheory.PGroup

public section

namespace CFSG.Quasithin.H13.A6

open Matrix

section General

variable {K : Type*} [Group K]

theorem le_or_le_of_subset_union {Y X₁ X₂ : Subgroup K}
    (h : ∀ y ∈ Y, y ∈ X₁ ∨ y ∈ X₂) : Y ≤ X₁ ∨ Y ≤ X₂ := by
  by_contra hc
  push Not at hc
  obtain ⟨h₁, h₂⟩ := hc
  obtain ⟨a, haY, ha⟩ := IsConcreteLE.not_le_iff_exists.1 h₁
  obtain ⟨b, hbY, hb⟩ := IsConcreteLE.not_le_iff_exists.1 h₂
  have ha2 : a ∈ X₂ := (h a haY).resolve_left ha
  have hb1 : b ∈ X₁ := (h b hbY).resolve_right hb
  rcases h (a * b) (Y.mul_mem haY hbY) with hab | hab
  · exact ha (by simpa using X₁.mul_mem hab (X₁.inv_mem hb1))
  · exact hb (by simpa using X₂.mul_mem (X₂.inv_mem ha2) hab)

theorem eq_or_eq_of_index_three [Finite K] {A B Y : Subgroup K}
    (hAY : A ≤ Y) (hYB : Y ≤ B) (hcard : Nat.card B = 3 * Nat.card A) : Y = A ∨ Y = B := by
  have hA : 0 < Nat.card A := Nat.card_pos
  obtain ⟨k, hk⟩ := Subgroup.card_dvd_of_le hAY
  obtain ⟨m, hm⟩ := Subgroup.card_dvd_of_le hYB
  rw [hk, mul_assoc, hcard] at hm
  have hkm : k * m = 3 := by
    have := Nat.eq_of_mul_eq_mul_left hA (show Nat.card A * 3 = Nat.card A * (k * m) by
      rw [mul_comm 3] at hm; linarith)
    exact this.symm
  have hk3 : k = 1 ∨ k = 3 := (Nat.dvd_prime Nat.prime_three).1 ⟨m, hkm.symm⟩
  rcases hk3 with rfl | rfl
  · left
    exact (Subgroup.eq_of_le_of_card_ge hAY (by rw [hk, mul_one])).symm
  · right
    exact Subgroup.eq_of_le_of_card_ge hYB (by rw [hcard, hk, mul_comm])

theorem overgroups_four [Finite K] {P₀ X₁ X₂ : Subgroup K} (_h₁ : P₀ ≤ X₁) (_h₂ : P₀ ≤ X₂)
    (hc₁ : Nat.card X₁ = 3 * Nat.card P₀) (hc₂ : Nat.card X₂ = 3 * Nat.card P₀)
    (hgen : ∀ Y : Subgroup K, P₀ ≤ Y → (∃ y ∈ Y, y ∉ X₁ ∧ y ∉ X₂) → Y = ⊤)
    (Y : Subgroup K) (hY : P₀ ≤ Y) : Y = P₀ ∨ Y = X₁ ∨ Y = X₂ ∨ Y = ⊤ := by
  by_cases hout : ∃ y ∈ Y, y ∉ X₁ ∧ y ∉ X₂
  · exact Or.inr (Or.inr (Or.inr (hgen Y hY hout)))
  push Not at hout
  rcases le_or_le_of_subset_union (fun y hy => by
      by_cases h : y ∈ X₁
      · exact Or.inl h
      · exact Or.inr (hout y hy h)) with h | h
  · rcases eq_or_eq_of_index_three hY h hc₁ with h' | h'
    · exact Or.inl h'
    · exact Or.inr (Or.inl h')
  · rcases eq_or_eq_of_index_three hY h hc₂ with h' | h'
    · exact Or.inl h'
    · exact Or.inr (Or.inr (Or.inl h'))

theorem eq_top_of_le_le [Finite K] {X₁ X₂ Y : Subgroup K} (h₁ : X₁ ≤ Y) (h₂ : X₂ ≤ Y)
    (h₂₁ : ¬ X₂ ≤ X₁) (hp : (X₁.index).Prime) : Y = ⊤ := by
  have hdvd : Y.index ∣ X₁.index := Subgroup.index_dvd_of_le h₁
  rcases (Nat.dvd_prime hp).1 hdvd with h | h
  · exact Subgroup.index_eq_one.1 h
  · exfalso
    have hrel : X₁.relIndex Y * Y.index = X₁.index := Subgroup.relIndex_mul_index h₁
    rw [h] at hrel
    have hr1 : X₁.relIndex Y = 1 :=
      Nat.eq_of_mul_eq_mul_right hp.pos (hrel.trans (one_mul _).symm)
    have hYX : Y ≤ X₁ := Subgroup.relIndex_eq_one.1 hr1
    exact h₂₁ (h₂.trans hYX)

end General

namespace SL3

abbrev S : Type := SpecialLinearGroup (Fin 3) (ZMod 2)

@[expose] def InX1 (A : S) : Prop := (A : Matrix (Fin 3) (Fin 3) (ZMod 2)) 1 0 = 0 ∧
  (A : Matrix (Fin 3) (Fin 3) (ZMod 2)) 2 0 = 0

@[expose] def InX2 (A : S) : Prop := (A : Matrix (Fin 3) (Fin 3) (ZMod 2)) 2 0 = 0 ∧
  (A : Matrix (Fin 3) (Fin 3) (ZMod 2)) 2 1 = 0

instance : DecidablePred InX1 := fun A => by unfold InX1; infer_instance

instance : DecidablePred InX2 := fun A => by unfold InX2; infer_instance

theorem inX1_mul : ∀ A B : S, InX1 A → InX1 B → InX1 (A * B) := by
  rintro A B ⟨ha1, ha2⟩ ⟨hb1, hb2⟩
  simp only [InX1, SpecialLinearGroup.coe_mul, Matrix.mul_apply, Fin.sum_univ_three, ha1, ha2,
    hb1, hb2, mul_zero, zero_mul, add_zero, and_self]

theorem inX2_mul : ∀ A B : S, InX2 A → InX2 B → InX2 (A * B) := by
  rintro A B ⟨ha1, ha2⟩ ⟨hb1, hb2⟩
  simp only [InX2, SpecialLinearGroup.coe_mul, Matrix.mul_apply, Fin.sum_univ_three, ha1, ha2,
    hb1, hb2, mul_zero, zero_mul, add_zero, and_self]

theorem inX1_inv : ∀ A : S, InX1 A → InX1 A⁻¹ := by decide +kernel

theorem inX2_inv : ∀ A : S, InX2 A → InX2 A⁻¹ := by decide +kernel

@[expose] def X1 : Subgroup S where
  carrier := {A | InX1 A}
  one_mem' := by decide +kernel
  mul_mem' := fun {a b} => inX1_mul a b
  inv_mem' := fun {a} => inX1_inv a

@[expose] def X2 : Subgroup S where
  carrier := {A | InX2 A}
  one_mem' := by decide +kernel
  mul_mem' := fun {a b} => inX2_mul a b
  inv_mem' := fun {a} => inX2_inv a

@[expose] def P0 : Subgroup S := X1 ⊓ X2

theorem card_P0 : Nat.card P0 = 8 := by
  have : Fintype.card {A : S // InX1 A ∧ InX2 A} = 8 := by decide +kernel
  rw [← this, ← Nat.card_eq_fintype_card]
  rfl

theorem card_X1 : Nat.card X1 = 24 := by
  have : Fintype.card {A : S // InX1 A} = 24 := by decide +kernel
  rw [← this, ← Nat.card_eq_fintype_card]
  rfl

theorem card_X2 : Nat.card X2 = 24 := by
  have : Fintype.card {A : S // InX2 A} = 24 := by decide +kernel
  rw [← this, ← Nat.card_eq_fintype_card]
  rfl

theorem card_S : Nat.card S = 168 := by
  rw [Nat.card_eq_fintype_card]
  decide +kernel

@[expose] def ex : S := ⟨!![1, 1, 0; 0, 1, 0; 0, 0, 1], by decide +kernel⟩

@[expose] def ey : S := ⟨!![1, 0, 0; 0, 1, 1; 0, 0, 1], by decide +kernel⟩

@[expose] def ez : S := ⟨!![1, 0, 1; 0, 1, 0; 0, 0, 1], by decide +kernel⟩

@[expose] def s1 : S := ⟨!![0, 1, 0; 1, 0, 0; 0, 0, 1], by decide +kernel⟩

@[expose] def s2 : S := ⟨!![1, 0, 0; 0, 0, 1; 0, 1, 0], by decide +kernel⟩

@[expose] def w1 : S := ⟨!![0, 0, 1; 0, 1, 0; 1, 0, 0], by decide +kernel⟩

@[expose] def w2 : S := ⟨!![0, 0, 1; 1, 0, 0; 0, 1, 0], by decide +kernel⟩

@[expose] def w3 : S := ⟨!![0, 1, 0; 0, 0, 1; 1, 0, 0], by decide +kernel⟩

@[expose] def P0list : List S := [1, ey, ez, ey * ez, ex, ey * ex, ex * ez, ex * ey]

theorem dc_cert : ∀ y : S, ¬ InX1 y → ¬ InX2 y →
    ∃ p ∈ P0list, ∃ q ∈ P0list, p * y * q = w1 ∨ p * y * q = w2 ∨ p * y * q = w3 := by
  decide +kernel

theorem words : ex * w1 * ey * w1 * ex = s1 ∧ ey * w1 * ex * w1 * ey = s2 ∧
    ex * w2 * ez * w3 * ex = s1 ∧ ey * w3 * ez * w2 * ey = s2 ∧ w2 * w3 = 1 := by
  decide +kernel

theorem X_cert : (∀ x : S, InX1 x → ∃ p ∈ P0list, ∃ q ∈ P0list, x = p ∨ x = p * s2 * q) ∧
    (∀ x : S, InX2 x → ∃ p ∈ P0list, ∃ q ∈ P0list, x = p ∨ x = p * s1 * q) := by
  decide +kernel

theorem P0list_mem {Y : Subgroup S} (hY : P0 ≤ Y) : ∀ p ∈ P0list, p ∈ Y := by
  have hx : ex ∈ Y := hY (show InX1 ex ∧ InX2 ex by decide +kernel)
  have hy : ey ∈ Y := hY (show InX1 ey ∧ InX2 ey by decide +kernel)
  have hz : ez ∈ Y := hY (show InX1 ez ∧ InX2 ez by decide +kernel)
  intro p hp
  simp only [P0list, List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact Y.one_mem
  · exact hy
  · exact hz
  · exact Y.mul_mem hy hz
  · exact hx
  · exact Y.mul_mem hy hx
  · exact Y.mul_mem hx hz
  · exact Y.mul_mem hx hy

theorem overgroups_SL3 (Y : Subgroup S) (hY : P0 ≤ Y) : Y = P0 ∨ Y = X1 ∨ Y = X2 ∨ Y = ⊤ := by
  refine overgroups_four (show P0 ≤ X1 from inf_le_left) (show P0 ≤ X2 from inf_le_right)
    (by rw [card_X1, card_P0])
    (by rw [card_X2, card_P0]) (fun Y hY ⟨y, hy, hy1, hy2⟩ => ?_) Y hY
  have hP := P0list_mem hY
  have hx : ex ∈ Y := hP ex (by simp [P0list])
  have hyy : ey ∈ Y := hP ey (by simp [P0list])
  have hz : ez ∈ Y := hP ez (by simp [P0list])
  obtain ⟨c1, c2, c3, c4, c7⟩ := words
  have hs : s1 ∈ Y ∧ s2 ∈ Y := by
    obtain ⟨p, hp, q, hq, hw⟩ := dc_cert y hy1 hy2
    have hwY : p * y * q ∈ Y := Y.mul_mem (Y.mul_mem (hP p hp) hy) (hP q hq)
    rcases hw with h | h | h <;> rw [h] at hwY
    · exact ⟨c1 ▸ Y.mul_mem (Y.mul_mem (Y.mul_mem (Y.mul_mem hx hwY) hyy) hwY) hx,
        c2 ▸ Y.mul_mem (Y.mul_mem (Y.mul_mem (Y.mul_mem hyy hwY) hx) hwY) hyy⟩
    · have h3 : w3 ∈ Y := by
        have := Y.inv_mem hwY
        rwa [inv_eq_of_mul_eq_one_right c7] at this
      exact ⟨c3 ▸ Y.mul_mem (Y.mul_mem (Y.mul_mem (Y.mul_mem hx hwY) hz) h3) hx,
        c4 ▸ Y.mul_mem (Y.mul_mem (Y.mul_mem (Y.mul_mem hyy h3) hz) hwY) hyy⟩
    · have h2 : w2 ∈ Y := by
        have := Y.inv_mem hwY
        rwa [inv_eq_of_mul_eq_one_left c7] at this
      exact ⟨c3 ▸ Y.mul_mem (Y.mul_mem (Y.mul_mem (Y.mul_mem hx h2) hz) hwY) hx,
        c4 ▸ Y.mul_mem (Y.mul_mem (Y.mul_mem (Y.mul_mem hyy hwY) hz) h2) hyy⟩
  obtain ⟨X1c, X2c⟩ := X_cert
  have hX1 : X1 ≤ Y := fun x hx' => by
    obtain ⟨p, hp, q, hq, h | h⟩ := X1c x hx'
    · exact h ▸ hP p hp
    · exact h ▸ Y.mul_mem (Y.mul_mem (hP p hp) hs.2) (hP q hq)
  have hX2 : X2 ≤ Y := fun x hx' => by
    obtain ⟨p, hp, q, hq, h | h⟩ := X2c x hx'
    · exact h ▸ hP p hp
    · exact h ▸ Y.mul_mem (Y.mul_mem (hP p hp) hs.1) (hP q hq)
  refine eq_top_of_le_le hX1 hX2 (fun h => ?_) ?_
  · have : InX1 s1 := h (show InX2 s1 by decide +kernel)
    exact absurd this (by decide +kernel)
  · have hidx : X1.index = 7 := by
      have := Subgroup.card_mul_index X1
      rw [card_X1, card_S] at this
      omega
    rw [hidx]
    norm_num

theorem P0_sylow : IsPGroup 2 P0 ∧ ¬ 2 ∣ P0.index := by
  refine ⟨IsPGroup.of_card (n := 3) (by rw [card_P0]; norm_num), ?_⟩
  have := Subgroup.card_mul_index P0
  rw [card_P0, card_S] at this
  have h21 : P0.index = 21 := by omega
  rw [h21]
  norm_num

theorem X_incomparable : ¬ X1 ≤ X2 ∧ ¬ X2 ≤ X1 := by
  refine ⟨fun h => ?_, fun h => ?_⟩
  · have : InX2 s2 := h (show InX1 s2 by decide +kernel)
    exact absurd this (by decide +kernel)
  · have : InX1 s1 := h (show InX2 s1 by decide +kernel)
    exact absurd this (by decide +kernel)

end SL3

namespace SL22

abbrev S2 : Type := SpecialLinearGroup (Fin 2) (ZMod 2)

abbrev K : Type := S2 × S2

@[expose] def InU (a : S2) : Prop := (a : Matrix (Fin 2) (Fin 2) (ZMod 2)) 1 0 = 0

instance : DecidablePred InU := fun a => by unfold InU; infer_instance

theorem inU_mul : ∀ a b : S2, InU a → InU b → InU (a * b) := by
  intro a b ha hb
  unfold InU at ha hb ⊢
  simp only [SpecialLinearGroup.coe_mul, Matrix.mul_apply, Fin.sum_univ_two, ha, hb,
    zero_mul, mul_zero, add_zero]

theorem inU_inv : ∀ a : S2, InU a → InU a⁻¹ := by decide +kernel

@[expose] def U : Subgroup S2 where
  carrier := {a | InU a}
  one_mem' := by decide +kernel
  mul_mem' := fun {a b} => inU_mul a b
  inv_mem' := fun {a} => inU_inv a

@[expose] def X1 : Subgroup K := (⊤ : Subgroup S2).prod U

@[expose] def X2 : Subgroup K := U.prod ⊤

@[expose] def P0 : Subgroup K := U.prod U

theorem mem_X1 {x : K} : x ∈ X1 ↔ InU x.2 := by
  simp [X1, Subgroup.mem_prod, U]

theorem mem_X2 {x : K} : x ∈ X2 ↔ InU x.1 := by
  simp [X2, Subgroup.mem_prod, U]

theorem card_P0 : Nat.card P0 = 4 := by
  have : Fintype.card {x : K // InU x.1 ∧ InU x.2} = 4 := by decide +kernel
  rw [← this, ← Nat.card_eq_fintype_card]
  rfl

theorem card_X1 : Nat.card X1 = 12 := by
  have : Fintype.card {x : K // True ∧ InU x.2} = 12 := by decide +kernel
  rw [← this, ← Nat.card_eq_fintype_card]
  rfl

theorem card_X2 : Nat.card X2 = 12 := by
  have : Fintype.card {x : K // InU x.1 ∧ True} = 12 := by decide +kernel
  rw [← this, ← Nat.card_eq_fintype_card]
  rfl

theorem card_K : Nat.card K = 36 := by
  rw [Nat.card_eq_fintype_card]
  decide +kernel

@[expose] def u : S2 := ⟨!![1, 1; 0, 1], by decide +kernel⟩

@[expose] def s : S2 := ⟨!![0, 1; 1, 0], by decide +kernel⟩

@[expose] def P0list : List K := [1, (u, 1), (1, u), (u, u)]

theorem dc_cert : ∀ y : K, ¬ InU y.2 → ¬ InU y.1 →
    ∃ p ∈ P0list, ∃ q ∈ P0list, p * y * q = (s, s) := by
  decide +kernel

theorem words : ((u, 1) : K) * (s, s) * (u, 1) * (s, s) * (u, 1) = (s, 1) ∧
    ((1, u) : K) * (s, s) * (1, u) * (s, s) * (1, u) = (1, s) := by
  decide +kernel

theorem X_cert : (∀ x : K, InU x.2 → ∃ p ∈ P0list, ∃ q ∈ P0list, x = p ∨ x = p * (s, 1) * q) ∧
    (∀ x : K, InU x.1 → ∃ p ∈ P0list, ∃ q ∈ P0list, x = p ∨ x = p * (1, s) * q) := by
  decide +kernel

theorem P0list_mem {Y : Subgroup K} (hY : P0 ≤ Y) : ∀ p ∈ P0list, p ∈ Y := by
  intro p hp
  simp only [P0list, List.mem_cons, List.not_mem_nil, or_false] at hp
  have hmem : ∀ x : K, InU x.1 → InU x.2 → x ∈ Y := fun x h1 h2 =>
    hY (Subgroup.mem_prod.2 ⟨h1, h2⟩)
  rcases hp with rfl | rfl | rfl | rfl
  · exact Y.one_mem
  · exact hmem _ (by decide +kernel) (by decide +kernel)
  · exact hmem _ (by decide +kernel) (by decide +kernel)
  · exact hmem _ (by decide +kernel) (by decide +kernel)

theorem overgroups_SL22 (Y : Subgroup K) (hY : P0 ≤ Y) :
    Y = P0 ∨ Y = X1 ∨ Y = X2 ∨ Y = ⊤ := by
  refine overgroups_four (show P0 ≤ X1 from fun x hx => mem_X1.2 (Subgroup.mem_prod.1 hx).2)
    (show P0 ≤ X2 from fun x hx => mem_X2.2 (Subgroup.mem_prod.1 hx).1)
    (by rw [card_X1, card_P0]) (by rw [card_X2, card_P0]) (fun Y hY ⟨y, hy, hy1, hy2⟩ => ?_) Y hY
  have hP := P0list_mem hY
  have ha : ((u, 1) : K) ∈ Y := hP _ (by simp [P0list])
  have hb : ((1, u) : K) ∈ Y := hP _ (by simp [P0list])
  obtain ⟨c1, c2⟩ := words
  obtain ⟨p, hp, q, hq, hw⟩ := dc_cert y (fun h => hy1 (mem_X1.2 h)) (fun h => hy2 (mem_X2.2 h))
  have hwY : ((s, s) : K) ∈ Y := hw ▸ Y.mul_mem (Y.mul_mem (hP p hp) hy) (hP q hq)
  have hs1 : ((s, 1) : K) ∈ Y := c1 ▸ Y.mul_mem (Y.mul_mem (Y.mul_mem (Y.mul_mem ha hwY) ha)
    hwY) ha
  have hs2 : ((1, s) : K) ∈ Y := c2 ▸ Y.mul_mem (Y.mul_mem (Y.mul_mem (Y.mul_mem hb hwY) hb)
    hwY) hb
  obtain ⟨X1c, X2c⟩ := X_cert
  have hX1 : X1 ≤ Y := fun x hx' => by
    obtain ⟨p, hp, q, hq, h | h⟩ := X1c x (mem_X1.1 hx')
    · exact h ▸ hP p hp
    · exact h ▸ Y.mul_mem (Y.mul_mem (hP p hp) hs1) (hP q hq)
  have hX2 : X2 ≤ Y := fun x hx' => by
    obtain ⟨p, hp, q, hq, h | h⟩ := X2c x (mem_X2.1 hx')
    · exact h ▸ hP p hp
    · exact h ▸ Y.mul_mem (Y.mul_mem (hP p hp) hs2) (hP q hq)
  refine eq_top_of_le_le hX1 hX2 (fun h => ?_) ?_
  · have h1 : ((1, s) : K) ∈ X2 := mem_X2.2 (by decide +kernel)
    exact absurd (mem_X1.1 (h h1)) (by decide +kernel)
  · have hidx : X1.index = 3 := by
      have := Subgroup.card_mul_index X1
      rw [card_X1, card_K] at this
      omega
    rw [hidx]
    norm_num

theorem P0_sylow : IsPGroup 2 P0 ∧ ¬ 2 ∣ P0.index := by
  refine ⟨IsPGroup.of_card (n := 2) (by rw [card_P0]; norm_num), ?_⟩
  have := Subgroup.card_mul_index P0
  rw [card_P0, card_K] at this
  have h9 : P0.index = 9 := by omega
  rw [h9]
  norm_num

theorem X_incomparable : ¬ X1 ≤ X2 ∧ ¬ X2 ≤ X1 := by
  refine ⟨fun h => ?_, fun h => ?_⟩
  · have h1 : ((s, 1) : K) ∈ X1 := mem_X1.2 (by decide +kernel)
    exact absurd (mem_X2.1 (h h1)) (by decide +kernel)
  · have h1 : ((1, s) : K) ∈ X2 := mem_X2.2 (by decide +kernel)
    exact absurd (mem_X1.1 (h h1)) (by decide +kernel)

end SL22

end CFSG.Quasithin.H13.A6
