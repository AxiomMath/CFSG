module

public import CFSG.LocalAnalysis.StandardType.ZS.PrimExtEta

public section

namespace CFSG.StandardType.ZS

variable {p : ℕ} [Fact p.Prime]

@[expose] def h3Cross (α w₁ w₂ ψ₁ ψ₂ : ZMod p) : ZMod p := ((2 - α) * ψ₁ * w₂ + ψ₂ * w₁) / 2

@[expose] def H3EtaConstraints (α w₁ w₂ ψ₁ ψ₂ : ZMod p) : Prop :=
  EtaOK 5 ψ₁ (2 * w₁) ∧ EtaOK 5 ψ₂ (2 * w₂) ∧
    ∀ s : ZMod p, (s = 1 ∨ s = -1) →
      EtaOK 5 ((1 + α) * (ψ₁ + s * ψ₂)) ((w₁ + s * (2 - α) * w₂) / 2) ∧
      EtaOK 5 ((α - 1) * (ψ₁ + s * ψ₂)) ((α * w₁ + s * (α - 1) * w₂) / 2) ∧
      EtaOK 5 ((1 - α) * ψ₁ + s * (1 + α) * ψ₂) (((1 - α) * w₁ + s * w₂) / 2)

private lemma zmod2_sq_ne (x : ZMod 2) : x ^ 2 ≠ x + 1 := by
  fin_cases x <;> decide

private lemma h3_prime_ne_two {α : ZMod p} (hα : α ^ 2 = α + 1) : p ≠ 2 := by
  rintro rfl
  exact zmod2_sq_ne α hα

private lemma h3_two_ne_zero_of_sq {α : ZMod p} (hα : α ^ 2 = α + 1) : (2 : ZMod p) ≠ 0 := by
  intro h2
  have hd : p ∣ 2 := (ZMod.natCast_eq_zero_iff 2 p).mp h2
  have hle : p ≤ 2 := Nat.le_of_dvd (by norm_num) hd
  have hpge : 2 ≤ p := (Fact.out : p.Prime).two_le
  exact h3_prime_ne_two hα (le_antisymm hle hpge)

private lemma h3_two_ne_zero (hp : 7 < p) : (2 : ZMod p) ≠ 0 := by
  intro h
  have hd : p ∣ 2 := (ZMod.natCast_eq_zero_iff 2 p).mp h
  have hle : p ≤ 2 := Nat.le_of_dvd (by norm_num) hd
  omega

private lemma h3_three_ne_zero (hp : 7 < p) : (3 : ZMod p) ≠ 0 := by
  intro h
  have hd : p ∣ 3 := (ZMod.natCast_eq_zero_iff 3 p).mp h
  have hle : p ≤ 3 := Nat.le_of_dvd (by norm_num) hd
  omega

private lemma h3_four_ne_zero (hp : 7 < p) : (4 : ZMod p) ≠ 0 := by
  intro h
  have hd : p ∣ 4 := (ZMod.natCast_eq_zero_iff 4 p).mp h
  have hle : p ≤ 4 := Nat.le_of_dvd (by norm_num) hd
  omega

private lemma h3_five_ne_zero (hp : 7 < p) : (5 : ZMod p) ≠ 0 := by
  intro h
  have hd : p ∣ 5 := (ZMod.natCast_eq_zero_iff 5 p).mp h
  have hle : p ≤ 5 := Nat.le_of_dvd (by norm_num) hd
  omega

private lemma h3_nine_ne_zero (hp : 7 < p) : (9 : ZMod p) ≠ 0 := by
  have h3 : (3 : ZMod p) ≠ 0 := by
    intro h
    have hd : p ∣ 3 := (ZMod.natCast_eq_zero_iff 3 p).mp h
    have hle : p ≤ 3 := Nat.le_of_dvd (by norm_num) hd
    omega
  have : (9 : ZMod p) = 3 ^ 2 := by norm_num
  rw [this]; exact pow_ne_zero 2 h3

private lemma h3_sixteen_ne_zero (hp : 7 < p) : (16 : ZMod p) ≠ 0 := by
  have h4 := h3_four_ne_zero hp
  have : (16 : ZMod p) = 4 ^ 2 := by norm_num
  rw [this]; exact pow_ne_zero 2 h4

private lemma h3_norm_eq_zero {R : Type*} [CommRing R] {α : R} (hα : α ^ 2 = α + 1)
    {c₀ c₁ : R} (h : c₀ + c₁ * α = 0) : c₀ ^ 2 + c₀ * c₁ - c₁ ^ 2 = 0 := by
  linear_combination (c₀ + c₁ - c₁ * α) * h + c₁ ^ 2 * hα

private lemma h3_two_sub_mul_one_add {R : Type*} [CommRing R] {α : R} (hα : α ^ 2 = α + 1) :
    (2 - α) * (1 + α) = 1 := by linear_combination (-1) * hα

private lemma h3_one_add_ne_zero {R : Type*} [CommRing R] [Nontrivial R] {α : R}
    (hα : α ^ 2 = α + 1) : (1 + α) ≠ 0 := by
  intro hz
  have hunit := h3_two_sub_mul_one_add hα
  rw [hz, mul_zero] at hunit
  exact one_ne_zero hunit.symm

private lemma h3_two_sub_ne_zero {R : Type*} [CommRing R] [Nontrivial R] {α : R}
    (hα : α ^ 2 = α + 1) : (2 - α) ≠ 0 := by
  intro hz
  have hunit := h3_two_sub_mul_one_add hα
  rw [hz, zero_mul] at hunit
  exact one_ne_zero hunit.symm

private lemma h3_key1 {R : Type*} [CommRing R] {α X Y : R} (hα : α ^ 2 = α + 1) :
    2 * X - (1 + α) * ((2 - α) * X + Y) + (1 + α) * (2 * Y - ((2 - α) * X + Y)) = 0 := by
  linear_combination (2 * X) * hα

private lemma h3_key2 {R : Type*} [CommRing R] {α X Y : R} (hα : α ^ 2 = α + 1) :
    4 * X * Y = (1 + α) * (((2 - α) * X + Y) ^ 2 - (2 * Y - ((2 - α) * X + Y)) ^ 2) := by
  linear_combination (4 * X * Y) * hα

private lemma h3_two_mul_sub_half {R : Type*} [Field R] (a b : R) (h : (2 : R) ≠ 0) :
    2 * (a / 2 - b / 2) = a - b := by
  rw [mul_sub, mul_div_cancel₀ _ h, mul_div_cancel₀ _ h]

private lemma h3_family_three_key {R : Type*} [CommRing R] {α s ψ₁ ψ₂ w₁ w₂ : R}
    (hα : α ^ 2 = α + 1) (hss : s * s = 1) :
    ((1 - α) * ψ₁ + s * (1 + α) * ψ₂) * ((1 - α) * w₁ + s * w₂) =
      (2 - α) * (ψ₁ * w₁) + (1 + α) * (ψ₂ * w₂) -
        s * α * ((2 - α) * ψ₁ * w₂ + ψ₂ * w₁) := by
  linear_combination (-s * ψ₂ * w₁ - s * ψ₁ * w₂ + ψ₁ * w₁) * hα +
    ((α + 1) * ψ₂ * w₂) * hss

private lemma h3Cross_eq_alg {R : Type*} [Field R] {α X Y C : R} (hα : α ^ 2 = α + 1)
    (h1a : (1 + α) ≠ 0) (h2nz : (2 : R) ≠ 0)
    (hD : 2 * C = (2 - α) * X + Y) (h : 4 * X * Y = (1 + α) * (2 * C) ^ 2) :
    X = (1 + α) * C ∧ Y = C := by
  have hD' : (2 - α) * X + Y = 2 * C := hD.symm
  have key1 := h3_key1 (α := α) (X := X) (Y := Y) hα
  have key2 := h3_key2 (α := α) (X := X) (Y := Y) hα
  have h4 : 4 * X * Y = (1 + α) * ((2 - α) * X + Y) ^ 2 := by rw [h, hD']
  have hB2 : (1 + α) * (2 * Y - ((2 - α) * X + Y)) ^ 2 = 0 := by
    linear_combination key2 - h4
  have hB' : 2 * Y - ((2 - α) * X + Y) = 0 := by
    have h2 : (2 * Y - ((2 - α) * X + Y)) ^ 2 = 0 :=
      (mul_eq_zero.mp hB2).resolve_left h1a
    exact sq_eq_zero_iff.mp h2
  have hA' : 2 * X - (1 + α) * ((2 - α) * X + Y) = 0 := by
    linear_combination key1 - (1 + α) * hB'
  have hXeq : X = (1 + α) * C := by
    have h2 : 2 * (X - (1 + α) * C) = 0 := by
      linear_combination hA' + (1 + α) * hD'
    exact sub_eq_zero.mp ((mul_eq_zero.mp h2).resolve_left h2nz)
  have hYeq : Y = C := by
    have h2 : 2 * (Y - C) = 0 := by linear_combination hB' + hD'
    exact sub_eq_zero.mp ((mul_eq_zero.mp h2).resolve_left h2nz)
  exact ⟨hXeq, hYeq⟩

private lemma h3_two_mul_add_half {R : Type*} [Field R] (a b : R) (h : (2 : R) ≠ 0) :
    2 * (a / 2 + b / 2) = a + b := by
  rw [mul_add, mul_div_cancel₀ _ h, mul_div_cancel₀ _ h]

private lemma h3_family_one_key {R : Type*} [CommRing R] {α s ψ₁ ψ₂ w₁ w₂ : R}
    (hα : α ^ 2 = α + 1) (hss : s * s = 1) :
    ((1 + α) * (ψ₁ + s * ψ₂)) * (w₁ + s * (2 - α) * w₂) =
      (1 + α) * (ψ₁ * w₁) + ψ₂ * w₂ +
        s * (1 + α) * ((2 - α) * ψ₁ * w₂ + ψ₂ * w₁) := by
  linear_combination (-(ψ₂ * w₂)) * hα + ((2 + α - α ^ 2) * (ψ₂ * w₂)) * hss

private lemma h3_family_one_key2 {R : Type*} [CommRing R] {α s ψ₁ ψ₂ w₁ w₂ : R}
    (hα : α ^ 2 = α + 1) (hss : s * s = 1) :
    ((α - 1) * (ψ₁ + s * ψ₂)) * (α * w₁ + s * (α - 1) * w₂) =
      (2 - α) * (((1 + α) * (ψ₁ + s * ψ₂)) * (w₁ + s * (2 - α) * w₂)) := by
  linear_combination
    (-α * s * ψ₁ * w₂ + 2 * s * ψ₂ * w₁ + 3 * s * ψ₁ * w₂ - α * ψ₂ * w₂ +
      2 * ψ₁ * w₁ + 3 * ψ₂ * w₂) * hα +
    (-α ^ 3 * ψ₂ * w₂ + 4 * α ^ 2 * ψ₂ * w₂ - 2 * α * ψ₂ * w₂ - 3 * ψ₂ * w₂) * hss

private lemma h3_c42 {R : Type*} [Field R] {α : R} (hα : α ^ 2 = α + 1)
    (h : (4 : R) + (-2) * α = 0) : (4 : R) = 0 := by
  have hn := h3_norm_eq_zero hα h; linear_combination hn
private lemma h3_c32 {R : Type*} [Field R] {α : R} (hα : α ^ 2 = α + 1)
    (h : (3 : R) + (-2) * α = 0) : (1 : R) = 0 := by
  have hn := h3_norm_eq_zero hα h; linear_combination -hn
private lemma h3_c22 {R : Type*} [Field R] {α : R} (hα : α ^ 2 = α + 1)
    (h : (2 : R) + (-2) * α = 0) : (4 : R) = 0 := by
  have hn := h3_norm_eq_zero hα h; linear_combination -hn
private lemma h3_c33 {R : Type*} [Field R] {α : R} (hα : α ^ 2 = α + 1)
    (h : (3 : R) + (-3) * α = 0) : (9 : R) = 0 := by
  have hn := h3_norm_eq_zero hα h; linear_combination -hn
private lemma h3_c21 {R : Type*} [Field R] {α : R} (hα : α ^ 2 = α + 1)
    (h : (2 : R) + (-1) * α = 0) : (1 : R) = 0 := by
  have hn := h3_norm_eq_zero hα h; linear_combination hn
private lemma h3_c53 {R : Type*} [Field R] {α : R} (hα : α ^ 2 = α + 1)
    (h : (5 : R) + (-3) * α = 0) : (1 : R) = 0 := by
  have hn := h3_norm_eq_zero hα h; linear_combination hn
private lemma h3_c43 {R : Type*} [Field R] {α : R} (hα : α ^ 2 = α + 1)
    (h : (4 : R) + (-3) * α = 0) : (5 : R) = 0 := by
  have hn := h3_norm_eq_zero hα h; linear_combination -hn
private lemma h3_c44 {R : Type*} [Field R] {α : R} (hα : α ^ 2 = α + 1)
    (h : (4 : R) + (-4) * α = 0) : (16 : R) = 0 := by
  have hn := h3_norm_eq_zero hα h; linear_combination -hn

private lemma h3_c3m1 {R : Type*} [Field R] {α : R} (hα : α ^ 2 = α + 1)
    (h : (3 : R) + (-1) * α = 0) : (5 : R) = 0 := by
  have hn := h3_norm_eq_zero hα h; linear_combination hn
private lemma h3_c21p {R : Type*} [Field R] {α : R} (hα : α ^ 2 = α + 1)
    (h : (2 : R) + (1) * α = 0) : (5 : R) = 0 := by
  have hn := h3_norm_eq_zero hα h; linear_combination hn
private lemma h3_c23 {R : Type*} [Field R] {α : R} (hα : α ^ 2 = α + 1)
    (h : (2 : R) + (3) * α = 0) : (1 : R) = 0 := by
  have hn := h3_norm_eq_zero hα h; linear_combination hn
private lemma h3_c13 {R : Type*} [Field R] {α : R} (hα : α ^ 2 = α + 1)
    (h : (1 : R) + (3) * α = 0) : (5 : R) = 0 := by
  have hn := h3_norm_eq_zero hα h; linear_combination -hn
private lemma h3_c03 {R : Type*} [Field R] {α : R} (hα : α ^ 2 = α + 1)
    (h : (0 : R) + (3) * α = 0) : (9 : R) = 0 := by
  have hn := h3_norm_eq_zero hα h; linear_combination -hn
private lemma h3_c12 {R : Type*} [Field R] {α : R} (hα : α ^ 2 = α + 1)
    (h : (1 : R) + (2) * α = 0) : (1 : R) = 0 := by
  have hn := h3_norm_eq_zero hα h; linear_combination -hn
private lemma h3_c04 {R : Type*} [Field R] {α : R} (hα : α ^ 2 = α + 1)
    (h : (0 : R) + (4) * α = 0) : (16 : R) = 0 := by
  have hn := h3_norm_eq_zero hα h; linear_combination -hn

private lemma h3_mul2_eq_zero {R : Type*} [Field R] {α : R} (hα : α ^ 2 = α + 1)
    (h : (2 - α) * 2 = 0) : (4 : R) = 0 :=
  h3_c42 hα (by linear_combination h)
private lemma h3_mul2_eq_one {R : Type*} [Field R] {α : R} (hα : α ^ 2 = α + 1)
    (h : (2 - α) * 2 = 1) : (1 : R) = 0 :=
  h3_c32 hα (by linear_combination h)
private lemma h3_mul2_eq_two {R : Type*} [Field R] {α : R} (hα : α ^ 2 = α + 1)
    (h : (2 - α) * 2 = 2) : (4 : R) = 0 :=
  h3_c22 hα (by linear_combination h)
private lemma h3_mul2_eq_one_add {R : Type*} [Field R] {α : R} (hα : α ^ 2 = α + 1)
    (h : (2 - α) * 2 = 1 + α) : (9 : R) = 0 :=
  h3_c33 hα (by linear_combination h)
private lemma h3_mul2_eq_two_sub {R : Type*} [Field R] {α : R} (hα : α ^ 2 = α + 1)
    (h : (2 - α) * 2 = 2 - α) : (1 : R) = 0 :=
  h3_c21 hα (by linear_combination h)
private lemma h3_sq2_eq_zero {R : Type*} [Field R] {α : R} (hα : α ^ 2 = α + 1)
    (h : (2 - α) ^ 2 = 0) : (1 : R) = 0 :=
  h3_c53 hα (by linear_combination h - hα)
private lemma h3_sq2_eq_one {R : Type*} [Field R] {α : R} (hα : α ^ 2 = α + 1)
    (h : (2 - α) ^ 2 = 1) : (5 : R) = 0 :=
  h3_c43 hα (by linear_combination h - hα)
private lemma h3_sq2_eq_two {R : Type*} [Field R] {α : R} (hα : α ^ 2 = α + 1)
    (h : (2 - α) ^ 2 = 2) : (9 : R) = 0 :=
  h3_c33 hα (by linear_combination h - hα)
private lemma h3_sq2_eq_one_add {R : Type*} [Field R] {α : R} (hα : α ^ 2 = α + 1)
    (h : (2 - α) ^ 2 = 1 + α) : (16 : R) = 0 :=
  h3_c44 hα (by linear_combination h - hα)
private lemma h3_sq2_eq_two_sub {R : Type*} [Field R] {α : R} (hα : α ^ 2 = α + 1)
    (h : (2 - α) ^ 2 = 2 - α) : (1 : R) = 0 :=
  h3_c32 hα (by linear_combination h - hα)

private lemma h3_P1_zero {α w₁ w₂ ψ₁ ψ₂ : ZMod p} (hα : α ^ 2 = α + 1)
    (hc : H3EtaConstraints α w₁ w₂ ψ₁ ψ₂) {s : ZMod p} (hs : s = 1 ∨ s = -1)
    (hss : s * s = 1)
    (h : ((1 + α) * (ψ₁ * w₁) + ψ₂ * w₂) / 2 + s * (1 + α) * h3Cross α w₁ w₂ ψ₁ ψ₂ = 0) :
    (1 + α) * (ψ₁ + s * ψ₂) = 0 ∧ (w₁ + s * (2 - α) * w₂) / 2 = 0 := by
  have h2nz : (2 : ZMod p) ≠ 0 := h3_two_ne_zero_of_sq hα
  have h2P1 : 2 * (((1 + α) * (ψ₁ * w₁) + ψ₂ * w₂) / 2 +
      s * (1 + α) * h3Cross α w₁ w₂ ψ₁ ψ₂) =
      (1 + α) * (ψ₁ * w₁) + ψ₂ * w₂ +
        s * (1 + α) * ((2 - α) * ψ₁ * w₂ + ψ₂ * w₁) := by
    simp only [h3Cross]
    rw [show s * (1 + α) * (((2 - α) * ψ₁ * w₂ + ψ₂ * w₁) / 2) =
        (s * (1 + α) * ((2 - α) * ψ₁ * w₂ + ψ₂ * w₁)) / 2 by ring]
    rw [h3_two_mul_add_half _ _ h2nz]
  have hkey := h3_family_one_key (α := α) (s := s) (ψ₁ := ψ₁) (ψ₂ := ψ₂) (w₁ := w₁)
    (w₂ := w₂) hα hss
  have hzero : ((1 + α) * (ψ₁ + s * ψ₂)) * ((w₁ + s * (2 - α) * w₂) / 2) = 0 := by
    have h2XY : 2 * (((1 + α) * (ψ₁ + s * ψ₂)) * ((w₁ + s * (2 - α) * w₂) / 2)) =
        ((1 + α) * (ψ₁ + s * ψ₂)) * (w₁ + s * (2 - α) * w₂) := by
      rw [show 2 * (((1 + α) * (ψ₁ + s * ψ₂)) * ((w₁ + s * (2 - α) * w₂) / 2)) =
          ((1 + α) * (ψ₁ + s * ψ₂)) * (2 * ((w₁ + s * (2 - α) * w₂) / 2)) by ring]
      rw [mul_div_cancel₀ _ h2nz]
    have h2 : 2 * (((1 + α) * (ψ₁ + s * ψ₂)) * ((w₁ + s * (2 - α) * w₂) / 2)) = 0 := by
      rw [h2XY, hkey, ← h2P1, h, mul_zero]
    exact (mul_eq_zero.mp h2).resolve_left h2nz
  have h0S : (0 : ZMod p) ∉ ({1, 2, 1 + α, 2 - α} : Set (ZMod p)) := by
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or]
    exact ⟨fun hh => one_ne_zero hh.symm, fun hh => h3_two_ne_zero_of_sq hα hh.symm,
      fun hh => h3_one_add_ne_zero (R := ZMod p) hα hh.symm,
      fun hh => h3_two_sub_ne_zero (R := ZMod p) hα hh.symm⟩
  have key : ∀ c : ZMod p, ((1 + α) * (ψ₁ + s * ψ₂)) * ((w₁ + s * (2 - α) * w₂) / 2) = c →
      c = 0 := fun c h1 => h1.symm.trans hzero
  rcases (etaOK_five_iff hα).mp (hc.2.2 s hs).1 with ⟨ha, hb⟩ | h1 | h1 | h1 | h1
  · exact ⟨ha, hb⟩
  · exfalso; refine h0S ?_; simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
    exact Or.inl (key 1 h1).symm
  · exfalso; refine h0S ?_; simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
    exact Or.inr (Or.inl (key 2 h1).symm)
  · exfalso; refine h0S ?_; simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
    exact Or.inr (Or.inr (Or.inl (key (1 + α) h1).symm))
  · exfalso; refine h0S ?_; simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
    exact Or.inr (Or.inr (Or.inr (key (2 - α) h1).symm))

private lemma h3_P3_zero {α w₁ w₂ ψ₁ ψ₂ : ZMod p} (hα : α ^ 2 = α + 1)
    (hc : H3EtaConstraints α w₁ w₂ ψ₁ ψ₂) {s : ZMod p} (hs : s = 1 ∨ s = -1)
    (hss : s * s = 1)
    (h : ((2 - α) * (ψ₁ * w₁) + (1 + α) * (ψ₂ * w₂)) / 2 -
        s * α * h3Cross α w₁ w₂ ψ₁ ψ₂ = 0) :
    (1 - α) * ψ₁ + s * (1 + α) * ψ₂ = 0 ∧ ((1 - α) * w₁ + s * w₂) / 2 = 0 := by
  have h2nz : (2 : ZMod p) ≠ 0 := h3_two_ne_zero_of_sq hα
  have h2P3 : 2 * (((2 - α) * (ψ₁ * w₁) + (1 + α) * (ψ₂ * w₂)) / 2 -
      s * α * h3Cross α w₁ w₂ ψ₁ ψ₂) =
      (2 - α) * (ψ₁ * w₁) + (1 + α) * (ψ₂ * w₂) -
        s * α * ((2 - α) * ψ₁ * w₂ + ψ₂ * w₁) := by
    simp only [h3Cross]
    rw [show s * α * (((2 - α) * ψ₁ * w₂ + ψ₂ * w₁) / 2) =
        (s * α * ((2 - α) * ψ₁ * w₂ + ψ₂ * w₁)) / 2 by ring]
    rw [h3_two_mul_sub_half _ _ h2nz]
  have hkey := h3_family_three_key (α := α) (s := s) (ψ₁ := ψ₁) (ψ₂ := ψ₂) (w₁ := w₁)
    (w₂ := w₂) hα hss
  have hzero : ((1 - α) * ψ₁ + s * (1 + α) * ψ₂) * (((1 - α) * w₁ + s * w₂) / 2) = 0 := by
    have h2XY : 2 * (((1 - α) * ψ₁ + s * (1 + α) * ψ₂) * (((1 - α) * w₁ + s * w₂) / 2)) =
        ((1 - α) * ψ₁ + s * (1 + α) * ψ₂) * ((1 - α) * w₁ + s * w₂) := by
      rw [show 2 * (((1 - α) * ψ₁ + s * (1 + α) * ψ₂) * (((1 - α) * w₁ + s * w₂) / 2)) =
          ((1 - α) * ψ₁ + s * (1 + α) * ψ₂) * (2 * (((1 - α) * w₁ + s * w₂) / 2)) by ring]
      rw [mul_div_cancel₀ _ h2nz]
    have h2 : 2 * (((1 - α) * ψ₁ + s * (1 + α) * ψ₂) * (((1 - α) * w₁ + s * w₂) / 2)) = 0 := by
      rw [h2XY, hkey, ← h2P3, h, mul_zero]
    exact (mul_eq_zero.mp h2).resolve_left h2nz
  have h0S : (0 : ZMod p) ∉ ({1, 2, 1 + α, 2 - α} : Set (ZMod p)) := by
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or]
    exact ⟨fun hh => one_ne_zero hh.symm, fun hh => h3_two_ne_zero_of_sq hα hh.symm,
      fun hh => h3_one_add_ne_zero (R := ZMod p) hα hh.symm,
      fun hh => h3_two_sub_ne_zero (R := ZMod p) hα hh.symm⟩
  have key : ∀ c : ZMod p, ((1 - α) * ψ₁ + s * (1 + α) * ψ₂) * (((1 - α) * w₁ + s * w₂) / 2) = c →
      c = 0 := fun c h1 => h1.symm.trans hzero
  rcases (etaOK_five_iff hα).mp (hc.2.2 s hs).2.2 with ⟨ha, hb⟩ | h1 | h1 | h1 | h1
  · exact ⟨ha, hb⟩
  · exfalso; refine h0S ?_; simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
    exact Or.inl (key 1 h1).symm
  · exfalso; refine h0S ?_; simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
    exact Or.inr (Or.inl (key 2 h1).symm)
  · exfalso; refine h0S ?_; simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
    exact Or.inr (Or.inr (Or.inl (key (1 + α) h1).symm))
  · exfalso; refine h0S ?_; simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
    exact Or.inr (Or.inr (Or.inr (key (2 - α) h1).symm))

namespace H3EtaConstraints

variable {α w₁ w₂ ψ₁ ψ₂ : ZMod p}

theorem two_mul_mem (hα : α ^ 2 = α + 1) (hc : H3EtaConstraints α w₁ w₂ ψ₁ ψ₂) :
    ((ψ₁ = 0 ∧ w₁ = 0) ∨ 2 * (ψ₁ * w₁) ∈ ({1, 2, 1 + α, 2 - α} : Set (ZMod p))) ∧
      ((ψ₂ = 0 ∧ w₂ = 0) ∨ 2 * (ψ₂ * w₂) ∈ ({1, 2, 1 + α, 2 - α} : Set (ZMod p))) := by
  have key : ∀ (s t : ZMod p), EtaOK 5 s t →
      (s = 0 ∧ t = 0) ∨ s * t = 1 ∨ s * t = 2 ∨ s * t = 1 + α ∨ s * t = 2 - α :=
    fun s t h => (etaOK_five_iff hα).mp h
  refine ⟨?_, ?_⟩
  · rcases key ψ₁ (2 * w₁) hc.1 with ⟨hψ, h2w⟩ | h | h | h | h
    · by_cases hw : w₁ = 0
      · exact Or.inl ⟨hψ, hw⟩
      · right
        have h2 : (2 : ZMod p) = 0 := (mul_eq_zero.mp h2w).resolve_right hw
        have he : 2 * (ψ₁ * w₁) = 2 := by rw [← mul_assoc, h2, zero_mul, zero_mul]
        simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
        rw [he]; exact Or.inr (Or.inl rfl)
    · right; simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
      left; rw [show 2 * (ψ₁ * w₁) = ψ₁ * (2 * w₁) by ring]; exact h
    · right; simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
      right; left; rw [show 2 * (ψ₁ * w₁) = ψ₁ * (2 * w₁) by ring]; exact h
    · right; simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
      right; right; left; rw [show 2 * (ψ₁ * w₁) = ψ₁ * (2 * w₁) by ring]; exact h
    · right; simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
      right; right; right; rw [show 2 * (ψ₁ * w₁) = ψ₁ * (2 * w₁) by ring]; exact h
  · rcases key ψ₂ (2 * w₂) hc.2.1 with ⟨hψ, h2w⟩ | h | h | h | h
    · by_cases hw : w₂ = 0
      · exact Or.inl ⟨hψ, hw⟩
      · right
        have h2 : (2 : ZMod p) = 0 := (mul_eq_zero.mp h2w).resolve_right hw
        have he : 2 * (ψ₂ * w₂) = 2 := by rw [← mul_assoc, h2, zero_mul, zero_mul]
        simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
        rw [he]; exact Or.inr (Or.inl rfl)
    · right; simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
      left; rw [show 2 * (ψ₂ * w₂) = ψ₂ * (2 * w₂) by ring]; exact h
    · right; simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
      right; left; rw [show 2 * (ψ₂ * w₂) = ψ₂ * (2 * w₂) by ring]; exact h
    · right; simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
      right; right; left; rw [show 2 * (ψ₂ * w₂) = ψ₂ * (2 * w₂) by ring]; exact h
    · right; simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
      right; right; right; rw [show 2 * (ψ₂ * w₂) = ψ₂ * (2 * w₂) by ring]; exact h

private lemma h3_fam1_h2P1 (hα : α ^ 2 = α + 1) {s : ZMod p} :
    2 * (((1 + α) * (ψ₁ * w₁) + ψ₂ * w₂) / 2 +
      s * (1 + α) * h3Cross α w₁ w₂ ψ₁ ψ₂) =
      (1 + α) * (ψ₁ * w₁) + ψ₂ * w₂ +
        s * (1 + α) * ((2 - α) * ψ₁ * w₂ + ψ₂ * w₁) := by
  have h2nz : (2 : ZMod p) ≠ 0 := h3_two_ne_zero_of_sq hα
  simp only [h3Cross]
  rw [show s * (1 + α) * (((2 - α) * ψ₁ * w₂ + ψ₂ * w₁) / 2) =
      (s * (1 + α) * ((2 - α) * ψ₁ * w₂ + ψ₂ * w₁)) / 2 by ring]
  rw [h3_two_mul_add_half _ _ h2nz]

private lemma h3_fam1_key1 (_hp5 : p ≠ 5) (hα : α ^ 2 = α + 1)
    (_hc : H3EtaConstraints α w₁ w₂ ψ₁ ψ₂) {s : ZMod p} (hss : s * s = 1) :
    ∀ c : ZMod p,
      ((1 + α) * (ψ₁ + s * ψ₂)) * ((w₁ + s * (2 - α) * w₂) / 2) = c →
      ((1 + α) * (ψ₁ * w₁) + ψ₂ * w₂) / 2 + s * (1 + α) * h3Cross α w₁ w₂ ψ₁ ψ₂ = c := by
  have h2nz : (2 : ZMod p) ≠ 0 := h3_two_ne_zero_of_sq hα
  have h2P1 := h3_fam1_h2P1 (α := α) (ψ₁ := ψ₁) (ψ₂ := ψ₂) (w₁ := w₁) (w₂ := w₂)
    (s := s) hα
  have hL1 : ((1 + α) * (ψ₁ + s * ψ₂)) * (w₁ + s * (2 - α) * w₂) =
      2 * (((1 + α) * (ψ₁ * w₁) + ψ₂ * w₂) / 2 +
        s * (1 + α) * h3Cross α w₁ w₂ ψ₁ ψ₂) := by
    rw [h2P1]; exact h3_family_one_key hα hss
  intro c hc'
  have h2XY : 2 * (((1 + α) * (ψ₁ + s * ψ₂)) * ((w₁ + s * (2 - α) * w₂) / 2)) =
      ((1 + α) * (ψ₁ + s * ψ₂)) * (w₁ + s * (2 - α) * w₂) := by
    rw [show 2 * (((1 + α) * (ψ₁ + s * ψ₂)) * ((w₁ + s * (2 - α) * w₂) / 2)) =
        ((1 + α) * (ψ₁ + s * ψ₂)) * (2 * ((w₁ + s * (2 - α) * w₂) / 2)) by ring]
    rw [mul_div_cancel₀ _ h2nz]
  have h2 : 2 * (((1 + α) * (ψ₁ * w₁) + ψ₂ * w₂) / 2 +
      s * (1 + α) * h3Cross α w₁ w₂ ψ₁ ψ₂) = 2 * c := by
    rw [← hL1, ← h2XY, hc']
  exact mul_left_cancel₀ h2nz h2

private lemma h3_fam1_key2 (_hp5 : p ≠ 5) (hα : α ^ 2 = α + 1)
    (_hc : H3EtaConstraints α w₁ w₂ ψ₁ ψ₂) {s : ZMod p} (hss : s * s = 1) :
    ∀ c : ZMod p,
      ((α - 1) * (ψ₁ + s * ψ₂)) * ((α * w₁ + s * (α - 1) * w₂) / 2) = c →
      (2 - α) * (((1 + α) * (ψ₁ * w₁) + ψ₂ * w₂) / 2 +
        s * (1 + α) * h3Cross α w₁ w₂ ψ₁ ψ₂) = c := by
  have h2nz : (2 : ZMod p) ≠ 0 := h3_two_ne_zero_of_sq hα
  have h2P1 := h3_fam1_h2P1 (α := α) (ψ₁ := ψ₁) (ψ₂ := ψ₂) (w₁ := w₁) (w₂ := w₂)
    (s := s) hα
  have hL1 : ((1 + α) * (ψ₁ + s * ψ₂)) * (w₁ + s * (2 - α) * w₂) =
      2 * (((1 + α) * (ψ₁ * w₁) + ψ₂ * w₂) / 2 +
        s * (1 + α) * h3Cross α w₁ w₂ ψ₁ ψ₂) := by
    rw [h2P1]; exact h3_family_one_key hα hss
  have hL2 : ((α - 1) * (ψ₁ + s * ψ₂)) * (α * w₁ + s * (α - 1) * w₂) =
      (2 - α) * (((1 + α) * (ψ₁ + s * ψ₂)) * (w₁ + s * (2 - α) * w₂)) :=
    h3_family_one_key2 hα hss
  intro c hc'
  have h2XY : 2 * (((α - 1) * (ψ₁ + s * ψ₂)) * ((α * w₁ + s * (α - 1) * w₂) / 2)) =
      ((α - 1) * (ψ₁ + s * ψ₂)) * (α * w₁ + s * (α - 1) * w₂) := by
    rw [show 2 * (((α - 1) * (ψ₁ + s * ψ₂)) * ((α * w₁ + s * (α - 1) * w₂) / 2)) =
        ((α - 1) * (ψ₁ + s * ψ₂)) * (2 * ((α * w₁ + s * (α - 1) * w₂) / 2)) by ring]
    rw [mul_div_cancel₀ _ h2nz]
  have hEq : 2 * ((2 - α) * (((1 + α) * (ψ₁ * w₁) + ψ₂ * w₂) / 2 +
      s * (1 + α) * h3Cross α w₁ w₂ ψ₁ ψ₂)) =
      ((α - 1) * (ψ₁ + s * ψ₂)) * (α * w₁ + s * (α - 1) * w₂) := by
    rw [hL2, hL1]; ring
  have h2 : 2 * ((2 - α) * (((1 + α) * (ψ₁ * w₁) + ψ₂ * w₂) / 2 +
      s * (1 + α) * h3Cross α w₁ w₂ ψ₁ ψ₂)) = 2 * c := by
    rw [hEq, ← h2XY, hc']
  exact mul_left_cancel₀ h2nz h2

private lemma h3_fam1_bad2 (hp7 : 7 < p) (hα : α ^ 2 = α + 1)
    (hc : H3EtaConstraints α w₁ w₂ ψ₁ ψ₂) {s : ZMod p} (hs : s = 1 ∨ s = -1)
    (key2 : ∀ c : ZMod p,
      ((α - 1) * (ψ₁ + s * ψ₂)) * ((α * w₁ + s * (α - 1) * w₂) / 2) = c →
      (2 - α) * (((1 + α) * (ψ₁ * w₁) + ψ₂ * w₂) / 2 +
        s * (1 + α) * h3Cross α w₁ w₂ ψ₁ ψ₂) = c)
    (hP1 : ((1 + α) * (ψ₁ * w₁) + ψ₂ * w₂) / 2 +
        s * (1 + α) * h3Cross α w₁ w₂ ψ₁ ψ₂ = 2) : False := by
  have hh2 := (etaOK_five_iff hα).mp (hc.2.2 s hs).2.1
  rcases hh2 with ⟨ha2, hb2⟩ | h2' | h2' | h2' | h2'
  · have hP2 : (2 - α) * (((1 + α) * (ψ₁ * w₁) + ψ₂ * w₂) / 2 +
        s * (1 + α) * h3Cross α w₁ w₂ ψ₁ ψ₂) = 0 :=
      key2 0 (by rw [ha2, hb2, mul_zero])
    have he : (2 - α) * 2 = 0 := by linear_combination hP2 - (2 - α) * hP1
    exact absurd (h3_mul2_eq_zero hα he) (h3_four_ne_zero hp7)
  · have hP2 : (2 - α) * (((1 + α) * (ψ₁ * w₁) + ψ₂ * w₂) / 2 +
        s * (1 + α) * h3Cross α w₁ w₂ ψ₁ ψ₂) = 1 := key2 1 h2'
    have he : (2 - α) * 2 = 1 := by linear_combination hP2 - (2 - α) * hP1
    exact absurd (h3_mul2_eq_one hα he) one_ne_zero
  · have hP2 : (2 - α) * (((1 + α) * (ψ₁ * w₁) + ψ₂ * w₂) / 2 +
        s * (1 + α) * h3Cross α w₁ w₂ ψ₁ ψ₂) = 2 := key2 2 h2'
    have he : (2 - α) * 2 = 2 := by linear_combination hP2 - (2 - α) * hP1
    exact absurd (h3_mul2_eq_two hα he) (h3_four_ne_zero hp7)
  · have hP2 : (2 - α) * (((1 + α) * (ψ₁ * w₁) + ψ₂ * w₂) / 2 +
        s * (1 + α) * h3Cross α w₁ w₂ ψ₁ ψ₂) = 1 + α := key2 (1 + α) h2'
    have he : (2 - α) * 2 = 1 + α := by linear_combination hP2 - (2 - α) * hP1
    exact absurd (h3_mul2_eq_one_add hα he) (h3_nine_ne_zero hp7)
  · have hP2 : (2 - α) * (((1 + α) * (ψ₁ * w₁) + ψ₂ * w₂) / 2 +
        s * (1 + α) * h3Cross α w₁ w₂ ψ₁ ψ₂) = 2 - α := key2 (2 - α) h2'
    have he : (2 - α) * 2 = 2 - α := by linear_combination hP2 - (2 - α) * hP1
    exact absurd (h3_mul2_eq_two_sub hα he) one_ne_zero

private lemma h3_fam1_bad2s (hp7 : 7 < p) (hα : α ^ 2 = α + 1)
    (hc : H3EtaConstraints α w₁ w₂ ψ₁ ψ₂) {s : ZMod p} (hs : s = 1 ∨ s = -1)
    (key2 : ∀ c : ZMod p,
      ((α - 1) * (ψ₁ + s * ψ₂)) * ((α * w₁ + s * (α - 1) * w₂) / 2) = c →
      (2 - α) * (((1 + α) * (ψ₁ * w₁) + ψ₂ * w₂) / 2 +
        s * (1 + α) * h3Cross α w₁ w₂ ψ₁ ψ₂) = c)
    (hP1 : ((1 + α) * (ψ₁ * w₁) + ψ₂ * w₂) / 2 +
        s * (1 + α) * h3Cross α w₁ w₂ ψ₁ ψ₂ = 2 - α) : False := by
  have hh2 := (etaOK_five_iff hα).mp (hc.2.2 s hs).2.1
  rcases hh2 with ⟨ha2, hb2⟩ | h2' | h2' | h2' | h2'
  · have hP2 : (2 - α) * (((1 + α) * (ψ₁ * w₁) + ψ₂ * w₂) / 2 +
        s * (1 + α) * h3Cross α w₁ w₂ ψ₁ ψ₂) = 0 :=
      key2 0 (by rw [ha2, hb2, mul_zero])
    have he : (2 - α) ^ 2 = 0 := by linear_combination hP2 - (2 - α) * hP1
    exact absurd (h3_sq2_eq_zero hα he) one_ne_zero
  · have hP2 : (2 - α) * (((1 + α) * (ψ₁ * w₁) + ψ₂ * w₂) / 2 +
        s * (1 + α) * h3Cross α w₁ w₂ ψ₁ ψ₂) = 1 := key2 1 h2'
    have he : (2 - α) ^ 2 = 1 := by linear_combination hP2 - (2 - α) * hP1
    exact absurd (h3_sq2_eq_one hα he) (h3_five_ne_zero hp7)
  · have hP2 : (2 - α) * (((1 + α) * (ψ₁ * w₁) + ψ₂ * w₂) / 2 +
        s * (1 + α) * h3Cross α w₁ w₂ ψ₁ ψ₂) = 2 := key2 2 h2'
    have he : (2 - α) ^ 2 = 2 := by linear_combination hP2 - (2 - α) * hP1
    exact absurd (h3_sq2_eq_two hα he) (h3_nine_ne_zero hp7)
  · have hP2 : (2 - α) * (((1 + α) * (ψ₁ * w₁) + ψ₂ * w₂) / 2 +
        s * (1 + α) * h3Cross α w₁ w₂ ψ₁ ψ₂) = 1 + α := key2 (1 + α) h2'
    have he : (2 - α) ^ 2 = 1 + α := by linear_combination hP2 - (2 - α) * hP1
    exact absurd (h3_sq2_eq_one_add hα he) (h3_sixteen_ne_zero hp7)
  · have hP2 : (2 - α) * (((1 + α) * (ψ₁ * w₁) + ψ₂ * w₂) / 2 +
        s * (1 + α) * h3Cross α w₁ w₂ ψ₁ ψ₂) = 2 - α := key2 (2 - α) h2'
    have he : (2 - α) ^ 2 = 2 - α := by linear_combination hP2 - (2 - α) * hP1
    exact absurd (h3_sq2_eq_two_sub hα he) one_ne_zero
theorem family_one_mem (hp5 : p ≠ 5) (hα : α ^ 2 = α + 1)
    (hc : H3EtaConstraints α w₁ w₂ ψ₁ ψ₂) {s : ZMod p} (hs : s = 1 ∨ s = -1) :
    ((1 + α) * (ψ₁ * w₁) + ψ₂ * w₂) / 2 + s * (1 + α) * h3Cross α w₁ w₂ ψ₁ ψ₂ ∈
      ({0, 1, 1 + α} : Set (ZMod p)) := by
  have hp7 : 7 < p := seven_lt_of_sq_eq_add_one hp5 hα
  have hss : s * s = 1 := by
    rcases hs with h | h
    · rw [h, one_mul]
    · rw [h]
      have h2 := neg_mul_neg (1 : ZMod p) (1 : ZMod p)
      rw [mul_one] at h2
      exact h2
  have key1 := h3_fam1_key1 hp5 hα hc hss
  have key2 := h3_fam1_key2 hp5 hα hc hss
  have hh1 := (etaOK_five_iff hα).mp (hc.2.2 s hs).1
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
  rcases hh1 with ⟨ha, hb⟩ | h1 | h1 | h1 | h1
  · left; exact key1 0 (by rw [ha, hb, mul_zero])
  · right; left; exact key1 1 h1
  · exfalso; exact h3_fam1_bad2 hp7 hα hc hs key2 (key1 2 h1)
  · right; right; exact key1 (1 + α) h1
  · exfalso; exact h3_fam1_bad2s hp7 hα hc hs key2 (key1 (2 - α) h1)

theorem family_three_mem (hα : α ^ 2 = α + 1) (hc : H3EtaConstraints α w₁ w₂ ψ₁ ψ₂)
    {s : ZMod p} (hs : s = 1 ∨ s = -1) :
    ((2 - α) * (ψ₁ * w₁) + (1 + α) * (ψ₂ * w₂)) / 2 - s * α * h3Cross α w₁ w₂ ψ₁ ψ₂ ∈
      ({0, 1, 2, 1 + α, 2 - α} : Set (ZMod p)) := by
  have h2nz : (2 : ZMod p) ≠ 0 := h3_two_ne_zero_of_sq hα
  have hss : s * s = 1 := by
    rcases hs with h | h
    · rw [h, one_mul]
    · rw [h]
      have h2 := neg_mul_neg (1 : ZMod p) (1 : ZMod p)
      rw [mul_one] at h2
      exact h2
  have hkey := h3_family_three_key (α := α) (s := s) (ψ₁ := ψ₁) (ψ₂ := ψ₂)
    (w₁ := w₁) (w₂ := w₂) hα hss
  have h2P3 : 2 * (((2 - α) * (ψ₁ * w₁) + (1 + α) * (ψ₂ * w₂)) / 2 -
      s * α * h3Cross α w₁ w₂ ψ₁ ψ₂) =
      (2 - α) * (ψ₁ * w₁) + (1 + α) * (ψ₂ * w₂) -
        s * α * ((2 - α) * ψ₁ * w₂ + ψ₂ * w₁) := by
    simp only [h3Cross]
    rw [show s * α * (((2 - α) * ψ₁ * w₂ + ψ₂ * w₁) / 2) =
        (s * α * ((2 - α) * ψ₁ * w₂ + ψ₂ * w₁)) / 2 by ring]
    rw [h3_two_mul_sub_half _ _ h2nz]
  have hXY : ((1 - α) * ψ₁ + s * (1 + α) * ψ₂) * ((1 - α) * w₁ + s * w₂) =
      2 * (((2 - α) * (ψ₁ * w₁) + (1 + α) * (ψ₂ * w₂)) / 2 -
        s * α * h3Cross α w₁ w₂ ψ₁ ψ₂) := by
    rw [h2P3]; exact hkey
  have key : ∀ c : ZMod p,
      ((1 - α) * ψ₁ + s * (1 + α) * ψ₂) * (((1 - α) * w₁ + s * w₂) / 2) = c →
      ((2 - α) * (ψ₁ * w₁) + (1 + α) * (ψ₂ * w₂)) / 2 -
        s * α * h3Cross α w₁ w₂ ψ₁ ψ₂ = c := by
    intro c hc'
    have h2XY : 2 * (((1 - α) * ψ₁ + s * (1 + α) * ψ₂) *
        (((1 - α) * w₁ + s * w₂) / 2)) =
        ((1 - α) * ψ₁ + s * (1 + α) * ψ₂) * ((1 - α) * w₁ + s * w₂) := by
      rw [show 2 * (((1 - α) * ψ₁ + s * (1 + α) * ψ₂) * (((1 - α) * w₁ + s * w₂) / 2)) =
          ((1 - α) * ψ₁ + s * (1 + α) * ψ₂) * (2 * (((1 - α) * w₁ + s * w₂) / 2)) by ring]
      rw [mul_div_cancel₀ _ h2nz]
    have h2 : 2 * (((2 - α) * (ψ₁ * w₁) + (1 + α) * (ψ₂ * w₂)) / 2 -
        s * α * h3Cross α w₁ w₂ ψ₁ ψ₂) = 2 * c := by rw [← hXY, ← h2XY, hc']
    exact mul_left_cancel₀ h2nz h2
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
  rcases (etaOK_five_iff hα).mp (hc.2.2 s hs).2.2 with ⟨ha, hb⟩ | h | h | h | h
  · left; exact key 0 (by rw [ha, hb, mul_zero])
  · right; left; exact key 1 h
  · right; right; left; exact key 2 h
  · right; right; right; left; exact key (1 + α) h
  · right; right; right; right; exact key (2 - α) h

private lemma h3_coord_cases (hp7 : 7 < p) (hα : α ^ 2 = α + 1)
    (hc : H3EtaConstraints α w₁ w₂ ψ₁ ψ₂) (hw : w₁ ≠ 0 ∨ w₂ ≠ 0)
    (_hψ1 : ψ₁ = 0) (hw1 : w₁ = 0)
    (h0S : (0 : ZMod p) ∉ ({1, 2, 1 + α, 2 - α} : Set (ZMod p)))
    (h4S : (4 : ZMod p) ∉ ({1, 2, 1 + α, 2 - α} : Set (ZMod p)))
    (h23S0 : (2 + 3 * α : ZMod p) ∉ ({0, 1, 2, 1 + α, 2 - α} : Set (ZMod p)))
    (hhalf : ψ₂ * w₂ / 2 ∈ ({0, 1, 1 + α} : Set (ZMod p)))
    (hP3 : (1 + α) * (ψ₂ * w₂ / 2) ∈ ({0, 1, 2, 1 + α, 2 - α} : Set (ZMod p))) : False := by
  have h2nz : (2 : ZMod p) ≠ 0 := h3_two_ne_zero hp7
  have hv := (two_mul_mem hα hc).2
  have h2half : 2 * (ψ₂ * w₂ / 2) = ψ₂ * w₂ := mul_div_cancel₀ (ψ₂ * w₂) h2nz
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hhalf
  rcases hhalf with hh | hh | hh
  · have h2w : 2 * (ψ₂ * w₂) = 0 := by rw [← h2half, hh]; ring
    rcases hv with hz2 | hmem
    · exact hw.elim (fun h1 => h1 hw1) (fun h2 => h2 hz2.2)
    · exact absurd (by rw [← h2w]; exact hmem) h0S
  · have hw2 : ψ₂ * w₂ = 2 := by rw [← h2half, hh]; ring
    have h2w : 2 * (ψ₂ * w₂) = 4 := by rw [hw2]; ring
    rcases hv with hz2 | hmem
    · exact h3_four_ne_zero hp7 (by rw [← h2w, hz2.1, hz2.2]; ring)
    · exact absurd (by rw [← h2w]; exact hmem) h4S
  · have h23 : (1 + α) * (ψ₂ * w₂ / 2) = 2 + 3 * α := by
      rw [hh]; linear_combination hα
    exact absurd (by rw [← h23]; exact hP3) h23S0

theorem coord_mul_ne_zero (hp5 : p ≠ 5) (hα : α ^ 2 = α + 1)
    (hc : H3EtaConstraints α w₁ w₂ ψ₁ ψ₂) (hw : w₁ ≠ 0 ∨ w₂ ≠ 0) : ψ₁ * w₁ ≠ 0 := by
  have hp7 : 7 < p := seven_lt_of_sq_eq_add_one hp5 hα
  have h2nz : (2 : ZMod p) ≠ 0 := h3_two_ne_zero hp7
  have h1a := h3_one_add_ne_zero (R := ZMod p) hα
  have h2a := h3_two_sub_ne_zero (R := ZMod p) hα
  have h0S : (0 : ZMod p) ∉ ({1, 2, 1 + α, 2 - α} : Set (ZMod p)) := by
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or]
    exact ⟨fun hh => one_ne_zero hh.symm, fun hh => h3_two_ne_zero_of_sq hα hh.symm,
      fun hh => h1a hh.symm, fun hh => h2a hh.symm⟩
  have h4S : (4 : ZMod p) ∉ ({1, 2, 1 + α, 2 - α} : Set (ZMod p)) := by
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or]
    refine ⟨?_, ?_, ?_, ?_⟩
    · intro hh; exact h3_three_ne_zero hp7 (by linear_combination hh)
    · intro hh; exact h2nz (by linear_combination hh)
    · intro hh; exact h3_five_ne_zero hp7 (h3_c3m1 hα (by linear_combination hh))
    · intro hh; exact h3_five_ne_zero hp7 (h3_c21p hα (by linear_combination hh))
  have h23S0 : (2 + 3 * α : ZMod p) ∉ ({0, 1, 2, 1 + α, 2 - α} : Set (ZMod p)) := by
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or]
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · intro hh; exact one_ne_zero (h3_c23 hα (by linear_combination hh))
    · intro hh; exact h3_five_ne_zero hp7 (h3_c13 hα (by linear_combination hh))
    · intro hh; exact h3_nine_ne_zero hp7 (h3_c03 hα (by linear_combination hh))
    · intro hh; exact one_ne_zero (h3_c12 hα (by linear_combination hh))
    · intro hh; exact h3_sixteen_ne_zero hp7 (h3_c04 hα (by linear_combination hh))
  intro h
  have h2z : 2 * (ψ₁ * w₁) = 0 := by rw [h, mul_zero]
  have hz : ψ₁ = 0 ∧ w₁ = 0 := by
    rcases (two_mul_mem hα hc).1 with hz | hmem
    · exact hz
    · exact absurd (by rw [← h2z]; exact hmem) h0S
  obtain ⟨hψ1, hw1⟩ := hz
  have hC : h3Cross α w₁ w₂ ψ₁ ψ₂ = 0 := by simp only [h3Cross]; rw [hψ1, hw1]; ring
  have hhalf : ψ₂ * w₂ / 2 ∈ ({0, 1, 1 + α} : Set (ZMod p)) := by
    have h := family_one_mem hp5 hα hc (s := 1) (Or.inl rfl)
    have hEq : ((1 + α) * (ψ₁ * w₁) + ψ₂ * w₂) / 2 +
        1 * (1 + α) * h3Cross α w₁ w₂ ψ₁ ψ₂ = ψ₂ * w₂ / 2 := by
      rw [hC, hψ1, hw1]; ring
    rwa [hEq] at h
  have hP3 : (1 + α) * (ψ₂ * w₂ / 2) ∈ ({0, 1, 2, 1 + α, 2 - α} : Set (ZMod p)) := by
    have h := family_three_mem hα hc (s := 1) (Or.inl rfl)
    have hEq : ((2 - α) * (ψ₁ * w₁) + (1 + α) * (ψ₂ * w₂)) / 2 -
        1 * α * h3Cross α w₁ w₂ ψ₁ ψ₂ = (1 + α) * (ψ₂ * w₂ / 2) := by
      rw [hC, hψ1, hw1]; ring
    rwa [hEq] at h
  have hv := (two_mul_mem hα hc).2
  have h2half : 2 * (ψ₂ * w₂ / 2) = ψ₂ * w₂ := mul_div_cancel₀ (ψ₂ * w₂) h2nz
  exact h3_coord_cases hp7 hα hc hw hψ1 hw1 h0S h4S h23S0 hhalf hP3

private lemma h3_S3_neg_alpha {R : Type*} [Field R] {α : R} (hα : α ^ 2 = α + 1)
    (h4 : (4 : R) ≠ 0) (h5 : (5 : R) ≠ 0)
    (h : -α ∈ ({0, 1, 2, 1 + α, 2 - α} : Set R)) : False := by
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at h
  rcases h with h | h | h | h | h
  · have t := h3_norm_eq_zero hα (show (0 : R) + (-1) * α = 0 by linear_combination h);
    norm_num at t
  · have t := h3_norm_eq_zero hα (show (-1 : R) + (-1) * α = 0 by linear_combination h);
    norm_num at t
  · have t := h3_norm_eq_zero hα (show (-2 : R) + (-1) * α = 0 by linear_combination h);
    norm_num at t; exact h5 t
  · have t := h3_norm_eq_zero hα (show (-1 : R) + (-2) * α = 0 by linear_combination h);
    norm_num at t
  · have t := h3_norm_eq_zero hα (show (-2 : R) + 0 * α = 0 by linear_combination h); norm_num at t;
    exact h4 t
private lemma h3_S3_one_sub_alpha {R : Type*} [Field R] {α : R} (hα : α ^ 2 = α + 1)
    (h4 : (4 : R) ≠ 0)
    (h : 1 - α ∈ ({0, 1, 2, 1 + α, 2 - α} : Set R)) : False := by
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at h
  rcases h with h | h | h | h | h
  · have t := h3_norm_eq_zero hα (show (1 : R) + (-1) * α = 0 by linear_combination h);
    norm_num at t
  · have t := h3_norm_eq_zero hα (show (0 : R) + (-1) * α = 0 by linear_combination h);
    norm_num at t
  · have t := h3_norm_eq_zero hα (show (-1 : R) + (-1) * α = 0 by linear_combination h);
    norm_num at t
  · have t := h3_norm_eq_zero hα (show (0 : R) + (-2) * α = 0 by linear_combination h);
    norm_num at t; exact h4 t
  · have t := h3_norm_eq_zero hα (show (-1 : R) + 0 * α = 0 by linear_combination h); norm_num at t
private lemma h3_S3_two_add_alpha {R : Type*} [Field R] {α : R} (hα : α ^ 2 = α + 1)
    (h4 : (4 : R) ≠ 0) (h5 : (5 : R) ≠ 0)
    (h : 2 + α ∈ ({0, 1, 2, 1 + α, 2 - α} : Set R)) : False := by
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at h
  rcases h with h | h | h | h | h
  · have t := h3_norm_eq_zero hα (show (2 : R) + 1 * α = 0 by linear_combination h); norm_num at t;
    exact h5 t
  · have t := h3_norm_eq_zero hα (show (1 : R) + 1 * α = 0 by linear_combination h); norm_num at t
  · have t := h3_norm_eq_zero hα (show (0 : R) + 1 * α = 0 by linear_combination h); norm_num at t
  · have t := h3_norm_eq_zero hα (show (1 : R) + 0 * α = 0 by linear_combination h); norm_num at t
  · have t := h3_norm_eq_zero hα (show (0 : R) + 2 * α = 0 by linear_combination h); norm_num at t;
    exact h4 t
private lemma h3_S3_two_add_two_alpha {R : Type*} [Field R] {α : R} (hα : α ^ 2 = α + 1)
    (h4 : (4 : R) ≠ 0) (h9 : (9 : R) ≠ 0)
    (h : 2 + 2 * α ∈ ({0, 1, 2, 1 + α, 2 - α} : Set R)) : False := by
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at h
  rcases h with h | h | h | h | h
  · have t := h3_norm_eq_zero hα (show (2 : R) + 2 * α = 0 by linear_combination h); norm_num at t;
    exact h4 t
  · have t := h3_norm_eq_zero hα (show (1 : R) + 2 * α = 0 by linear_combination h); norm_num at t
  · have t := h3_norm_eq_zero hα (show (0 : R) + 2 * α = 0 by linear_combination h); norm_num at t;
    exact h4 t
  · have t := h3_norm_eq_zero hα (show (1 : R) + 1 * α = 0 by linear_combination h); norm_num at t
  · have t := h3_norm_eq_zero hα (show (0 : R) + 3 * α = 0 by linear_combination h); norm_num at t;
    exact h9 t
private lemma h3_S3_neg_two_alpha {R : Type*} [Field R] {α : R} (hα : α ^ 2 = α + 1)
    (h4 : (4 : R) ≠ 0) (h5 : (5 : R) ≠ 0)
    (h : -2 * α ∈ ({0, 1, 2, 1 + α, 2 - α} : Set R)) : False := by
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at h
  rcases h with h | h | h | h | h
  · have t := h3_norm_eq_zero hα (show (0 : R) + (-2) * α = 0 by linear_combination h);
    norm_num at t; exact h4 t
  · have t := h3_norm_eq_zero hα (show (-1 : R) + (-2) * α = 0 by linear_combination h);
    norm_num at t
  · have t := h3_norm_eq_zero hα (show (-2 : R) + (-2) * α = 0 by linear_combination h);
    norm_num at t; exact h4 t
  · have t := h3_norm_eq_zero hα (show (-1 : R) + (-3) * α = 0 by linear_combination h);
    norm_num at t; exact h5 t
  · have t := h3_norm_eq_zero hα (show (-2 : R) + (-1) * α = 0 by linear_combination h);
    norm_num at t; exact h5 t
private lemma h3_S3_one_sub_two_alpha {R : Type*} [Field R] {α : R} (hα : α ^ 2 = α + 1)
    (h4 : (4 : R) ≠ 0) (h5 : (5 : R) ≠ 0) (h9 : (9 : R) ≠ 0)
    (h : 1 - 2 * α ∈ ({0, 1, 2, 1 + α, 2 - α} : Set R)) : False := by
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at h
  rcases h with h | h | h | h | h
  · have t := h3_norm_eq_zero hα (show (1 : R) + (-2) * α = 0 by linear_combination h);
    norm_num at t; exact h5 t
  · have t := h3_norm_eq_zero hα (show (0 : R) + (-2) * α = 0 by linear_combination h);
    norm_num at t; exact h4 t
  · have t := h3_norm_eq_zero hα (show (-1 : R) + (-2) * α = 0 by linear_combination h);
    norm_num at t
  · have t := h3_norm_eq_zero hα (show (0 : R) + (-3) * α = 0 by linear_combination h);
    norm_num at t; exact h9 t
  · have t := h3_norm_eq_zero hα (show (-1 : R) + (-1) * α = 0 by linear_combination h);
    norm_num at t
private lemma h3_S_three_sub_alpha {R : Type*} [Field R] {α : R} (hα : α ^ 2 = α + 1)
    (h4 : (4 : R) ≠ 0)
    (h : 3 - α ∈ ({1, 2, 1 + α, 2 - α} : Set R)) : False := by
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at h
  rcases h with h | h | h | h
  · have t := h3_norm_eq_zero hα (show (2 : R) + (-1) * α = 0 by linear_combination h);
    norm_num at t
  · have t := h3_norm_eq_zero hα (show (1 : R) + (-1) * α = 0 by linear_combination h);
    norm_num at t
  · have t := h3_norm_eq_zero hα (show (2 : R) + (-2) * α = 0 by linear_combination h);
    norm_num at t; exact h4 t
  · have t := h3_norm_eq_zero hα (show (1 : R) + 0 * α = 0 by linear_combination h); norm_num at t
private lemma h3_S_three {R : Type*} [Field R] {α : R} (hα : α ^ 2 = α + 1)
    (h4 : (4 : R) ≠ 0)
    (h : (3 : R) ∈ ({1, 2, 1 + α, 2 - α} : Set R)) : False := by
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at h
  rcases h with h | h | h | h
  · have t := h3_norm_eq_zero hα (show (2 : R) + 0 * α = 0 by linear_combination h); norm_num at t;
    exact h4 t
  · have t := h3_norm_eq_zero hα (show (1 : R) + 0 * α = 0 by linear_combination h); norm_num at t
  · have t := h3_norm_eq_zero hα (show (2 : R) + (-1) * α = 0 by linear_combination h);
    norm_num at t
  · have t := h3_norm_eq_zero hα (show (1 : R) + 1 * α = 0 by linear_combination h); norm_num at t
private lemma h3_S_two_add_alpha {R : Type*} [Field R] {α : R} (hα : α ^ 2 = α + 1)
    (h4 : (4 : R) ≠ 0)
    (h : 2 + α ∈ ({1, 2, 1 + α, 2 - α} : Set R)) : False := by
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at h
  rcases h with h | h | h | h
  · have t := h3_norm_eq_zero hα (show (1 : R) + 1 * α = 0 by linear_combination h); norm_num at t
  · have t := h3_norm_eq_zero hα (show (0 : R) + 1 * α = 0 by linear_combination h); norm_num at t
  · have t := h3_norm_eq_zero hα (show (1 : R) + 0 * α = 0 by linear_combination h); norm_num at t
  · have t := h3_norm_eq_zero hα (show (0 : R) + 2 * α = 0 by linear_combination h); norm_num at t;
    exact h4 t
private lemma h3_S3_three_add_two_alpha {R : Type*} [Field R] {α : R} (hα : α ^ 2 = α + 1)
    (h4 : (4 : R) ≠ 0) (h5 : (5 : R) ≠ 0)
    (h : 3 + 2 * α ∈ ({0, 1, 2, 1 + α, 2 - α} : Set R)) (hz : 3 + 2 * α = 0 → False) : False := by
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at h
  rcases h with h | h | h | h | h
  · exact hz h
  · have t := h3_norm_eq_zero hα (show (2 : R) + 2 * α = 0 by linear_combination h); norm_num at t;
    exact h4 t
  · have t := h3_norm_eq_zero hα (show (1 : R) + 2 * α = 0 by linear_combination h); norm_num at t
  · have t := h3_norm_eq_zero hα (show (2 : R) + 1 * α = 0 by linear_combination h); norm_num at t;
    exact h5 t
  · have t := h3_norm_eq_zero hα (show (1 : R) + 3 * α = 0 by linear_combination h); norm_num at t;
    exact h5 t

private lemma h3_alg_one_p0 {R : Type*} [Field R] {α : R} (hα : α ^ 2 = α + 1)
    (h2 : (2 : R) ≠ 0) (h4 : (4 : R) ≠ 0) (_h5 : (5 : R) ≠ 0) (_h9 : (9 : R) ≠ 0)
    (h1a : 1 + α ≠ 0) (_h2a : 2 - α ≠ 0)
    {a b C pp pm : R}
    (ha : a = 1)
    (_hb : b = 1 ∨ b = 2 ∨ b = 1 + α ∨ b = 2 - α)
    (hpp : pp = 0)
    (hpm : pm = 0 ∨ pm = 1 ∨ pm = 1 + α)
    (hbsum : b = 2 * (pp + pm) - (1 + α) * a)
    (hCsum : pp - pm = 2 * (1 + α) * C)
    (_hP3p : pp + α * pm - α * a ∈ ({0, 1, 2, 1 + α, 2 - α} : Set R))
    (hP3m : α * pp + pm - α * a ∈ ({0, 1, 2, 1 + α, 2 - α} : Set R))
    (hzero : pp = 0 → pm = 0 → a = 0)
    (_hP3zero : pp = pm → pp + α * pm - α * a = 0 → a = 0) :
    (a = 2 - α ∧ b = 1 ∧ (C = α / 2 - 1 ∨ C = 1 - α / 2)) ∨
    (a = 1 + α ∧ b = 2 - α ∧ (C = (1 - α) / 2 ∨ C = (α - 1) / 2)) ∨
    (a = 1 ∧ b = 1 + α ∧ (C = 1 / 2 ∨ C = -1 / 2)) ∨
    (a = 2 ∧ b = 2) := by
  rcases hpm with hpm | hpm | hpm
  · exact absurd (hzero hpp hpm) (by rw [ha]; exact one_ne_zero)
  · exfalso
    have hval : α * pp + pm - α * a = 1 - α := by rw [hpp, hpm, ha]; ring
    rw [hval] at hP3m
    exact h3_S3_one_sub_alpha hα h4 hP3m
  · refine Or.inr (Or.inr (Or.inl ⟨ha, ?_, Or.inr ?_⟩))
    · rw [hbsum, hpp, hpm, ha]; ring
    · have h : -(1 + α) = 2 * (1 + α) * C := by rw [← hCsum, hpp, hpm]; ring
      have h1m : (1 + α) * (C * 2) = (1 + α) * (-1) := by linear_combination -h
      have hC : C * 2 = -1 := mul_left_cancel₀ h1a h1m
      rw [eq_div_iff h2]; linear_combination hC

private lemma h3_alg_one_p1 {R : Type*} [Field R] {α : R} (hα : α ^ 2 = α + 1)
    (_h2 : (2 : R) ≠ 0) (h4 : (4 : R) ≠ 0) (h5 : (5 : R) ≠ 0) (_h9 : (9 : R) ≠ 0)
    (_h1a : 1 + α ≠ 0) (_h2a : 2 - α ≠ 0)
    {a b C pp pm : R}
    (ha : a = 1)
    (hb : b = 1 ∨ b = 2 ∨ b = 1 + α ∨ b = 2 - α)
    (hpp : pp = 1)
    (hpm : pm = 0 ∨ pm = 1 ∨ pm = 1 + α)
    (hbsum : b = 2 * (pp + pm) - (1 + α) * a)
    (_hCsum : pp - pm = 2 * (1 + α) * C)
    (hP3p : pp + α * pm - α * a ∈ ({0, 1, 2, 1 + α, 2 - α} : Set R))
    (_hP3m : α * pp + pm - α * a ∈ ({0, 1, 2, 1 + α, 2 - α} : Set R))
    (_hzero : pp = 0 → pm = 0 → a = 0)
    (_hP3zero : pp = pm → pp + α * pm - α * a = 0 → a = 0) :
    (a = 2 - α ∧ b = 1 ∧ (C = α / 2 - 1 ∨ C = 1 - α / 2)) ∨
    (a = 1 + α ∧ b = 2 - α ∧ (C = (1 - α) / 2 ∨ C = (α - 1) / 2)) ∨
    (a = 1 ∧ b = 1 + α ∧ (C = 1 / 2 ∨ C = -1 / 2)) ∨
    (a = 2 ∧ b = 2) := by
  rcases hpm with hpm | hpm | hpm
  · exfalso
    have hval : pp + α * pm - α * a = 1 - α := by rw [hpp, hpm, ha]; ring
    rw [hval] at hP3p
    exact h3_S3_one_sub_alpha hα h4 hP3p
  · exfalso
    have hbmem : b ∈ ({1, 2, 1 + α, 2 - α} : Set R) := by
      rcases hb with h | h | h | h <;> rw [h] <;> simp
    have hval : b = 3 - α := by rw [hbsum, hpp, hpm, ha]; ring
    rw [hval] at hbmem
    exact h3_S_three_sub_alpha hα h4 hbmem
  · exfalso
    have hval : pp + α * pm - α * a = 2 + α := by rw [hpp, hpm, ha]; linear_combination hα
    rw [hval] at hP3p
    exact h3_S3_two_add_alpha hα h4 h5 hP3p

private lemma h3_alg_one_p1a {R : Type*} [Field R] {α : R} (hα : α ^ 2 = α + 1)
    (h2 : (2 : R) ≠ 0) (h4 : (4 : R) ≠ 0) (h5 : (5 : R) ≠ 0) (h9 : (9 : R) ≠ 0)
    (h1a : 1 + α ≠ 0) (_h2a : 2 - α ≠ 0)
    {a b C pp pm : R}
    (ha : a = 1)
    (_hb : b = 1 ∨ b = 2 ∨ b = 1 + α ∨ b = 2 - α)
    (hpp : pp = 1 + α)
    (hpm : pm = 0 ∨ pm = 1 ∨ pm = 1 + α)
    (hbsum : b = 2 * (pp + pm) - (1 + α) * a)
    (hCsum : pp - pm = 2 * (1 + α) * C)
    (hP3p : pp + α * pm - α * a ∈ ({0, 1, 2, 1 + α, 2 - α} : Set R))
    (hP3m : α * pp + pm - α * a ∈ ({0, 1, 2, 1 + α, 2 - α} : Set R))
    (_hzero : pp = 0 → pm = 0 → a = 0)
    (_hP3zero : pp = pm → pp + α * pm - α * a = 0 → a = 0) :
    (a = 2 - α ∧ b = 1 ∧ (C = α / 2 - 1 ∨ C = 1 - α / 2)) ∨
    (a = 1 + α ∧ b = 2 - α ∧ (C = (1 - α) / 2 ∨ C = (α - 1) / 2)) ∨
    (a = 1 ∧ b = 1 + α ∧ (C = 1 / 2 ∨ C = -1 / 2)) ∨
    (a = 2 ∧ b = 2) := by
  rcases hpm with hpm | hpm | hpm
  · refine Or.inr (Or.inr (Or.inl ⟨ha, ?_, Or.inl ?_⟩))
    · rw [hbsum, hpp, hpm, ha]; ring
    · have h : 1 + α = 2 * (1 + α) * C := by rw [← hCsum, hpp, hpm]; ring
      have h1m : (1 + α) * (C * 2) = (1 + α) * 1 := by linear_combination -h
      have hC : C * 2 = 1 := mul_left_cancel₀ h1a h1m
      rw [eq_div_iff h2]; linear_combination hC
  · exfalso
    have hval : α * pp + pm - α * a = 2 + α := by rw [hpp, hpm, ha]; linear_combination hα
    rw [hval] at hP3m
    exact h3_S3_two_add_alpha hα h4 h5 hP3m
  · exfalso
    have hval : pp + α * pm - α * a = 2 + 2 * α := by rw [hpp, hpm, ha]; linear_combination hα
    rw [hval] at hP3p
    exact h3_S3_two_add_two_alpha hα h4 h9 hP3p

private lemma h3_alg_one {R : Type*} [Field R] {α : R} (hα : α ^ 2 = α + 1)
    (h2 : (2 : R) ≠ 0) (h4 : (4 : R) ≠ 0) (h5 : (5 : R) ≠ 0) (h9 : (9 : R) ≠ 0)
    (h1a : 1 + α ≠ 0) (h2a : 2 - α ≠ 0)
    {a b C pp pm : R}
    (ha : a = 1)
    (hb : b = 1 ∨ b = 2 ∨ b = 1 + α ∨ b = 2 - α)
    (hpp : pp = 0 ∨ pp = 1 ∨ pp = 1 + α)
    (hpm : pm = 0 ∨ pm = 1 ∨ pm = 1 + α)
    (hbsum : b = 2 * (pp + pm) - (1 + α) * a)
    (hCsum : pp - pm = 2 * (1 + α) * C)
    (hP3p : pp + α * pm - α * a ∈ ({0, 1, 2, 1 + α, 2 - α} : Set R))
    (hP3m : α * pp + pm - α * a ∈ ({0, 1, 2, 1 + α, 2 - α} : Set R))
    (hzero : pp = 0 → pm = 0 → a = 0)
    (hP3zero : pp = pm → pp + α * pm - α * a = 0 → a = 0) :
    (a = 2 - α ∧ b = 1 ∧ (C = α / 2 - 1 ∨ C = 1 - α / 2)) ∨
    (a = 1 + α ∧ b = 2 - α ∧ (C = (1 - α) / 2 ∨ C = (α - 1) / 2)) ∨
    (a = 1 ∧ b = 1 + α ∧ (C = 1 / 2 ∨ C = -1 / 2)) ∨
    (a = 2 ∧ b = 2) := by
  rcases hpp with hpp | hpp | hpp
  · exact h3_alg_one_p0 (a := a) (b := b) (C := C)
      (pp := pp) (pm := pm) hα h2 h4 h5 h9 h1a h2a
      ha hb hpp hpm hbsum hCsum hP3p hP3m hzero hP3zero
  · exact h3_alg_one_p1 (a := a) (b := b) (C := C)
      (pp := pp) (pm := pm) hα h2 h4 h5 h9 h1a h2a
      ha hb hpp hpm hbsum hCsum hP3p hP3m hzero hP3zero
  · exact h3_alg_one_p1a (a := a) (b := b) (C := C)
      (pp := pp) (pm := pm) hα h2 h4 h5 h9 h1a h2a
      ha hb hpp hpm hbsum hCsum hP3p hP3m hzero hP3zero

private lemma h3_alg_one_add_p0 {R : Type*} [Field R] {α : R} (hα : α ^ 2 = α + 1)
    (_h2 : (2 : R) ≠ 0) (h4 : (4 : R) ≠ 0) (h5 : (5 : R) ≠ 0) (_h9 : (9 : R) ≠ 0)
    (h1a : 1 + α ≠ 0) (_h2a : 2 - α ≠ 0)
    {a b C pp pm : R}
    (ha : a = 1 + α)
    (_hb : b = 1 ∨ b = 2 ∨ b = 1 + α ∨ b = 2 - α)
    (hpp : pp = 0)
    (hpm : pm = 0 ∨ pm = 1 ∨ pm = 1 + α)
    (_hbsum : b = 2 * (pp + pm) - (1 + α) * a)
    (_hCsum : pp - pm = 2 * (1 + α) * C)
    (_hP3p : pp + α * pm - α * a ∈ ({0, 1, 2, 1 + α, 2 - α} : Set R))
    (hP3m : α * pp + pm - α * a ∈ ({0, 1, 2, 1 + α, 2 - α} : Set R))
    (hzero : pp = 0 → pm = 0 → a = 0)
    (_hP3zero : pp = pm → pp + α * pm - α * a = 0 → a = 0) :
    (a = 2 - α ∧ b = 1 ∧ (C = α / 2 - 1 ∨ C = 1 - α / 2)) ∨
    (a = 1 + α ∧ b = 2 - α ∧ (C = (1 - α) / 2 ∨ C = (α - 1) / 2)) ∨
    (a = 1 ∧ b = 1 + α ∧ (C = 1 / 2 ∨ C = -1 / 2)) ∨
    (a = 2 ∧ b = 2) := by
  rcases hpm with hpm | hpm | hpm
  · exact absurd (hzero hpp hpm) (by rw [ha]; exact h1a)
  · exfalso
    have hval : α * pp + pm - α * a = -2 * α := by rw [hpp, hpm, ha]; linear_combination -hα
    rw [hval] at hP3m
    exact h3_S3_neg_two_alpha hα h4 h5 hP3m
  · exfalso
    have hval : α * pp + pm - α * a = -α := by rw [hpp, hpm, ha]; linear_combination -hα
    rw [hval] at hP3m
    exact h3_S3_neg_alpha hα h4 h5 hP3m

private lemma h3_alg_one_add_p1 {R : Type*} [Field R] {α : R} (hα : α ^ 2 = α + 1)
    (h2 : (2 : R) ≠ 0) (h4 : (4 : R) ≠ 0) (h5 : (5 : R) ≠ 0) (_h9 : (9 : R) ≠ 0)
    (h1a : 1 + α ≠ 0) (_h2a : 2 - α ≠ 0)
    {a b C pp pm : R}
    (ha : a = 1 + α)
    (_hb : b = 1 ∨ b = 2 ∨ b = 1 + α ∨ b = 2 - α)
    (hpp : pp = 1)
    (hpm : pm = 0 ∨ pm = 1 ∨ pm = 1 + α)
    (hbsum : b = 2 * (pp + pm) - (1 + α) * a)
    (hCsum : pp - pm = 2 * (1 + α) * C)
    (hP3p : pp + α * pm - α * a ∈ ({0, 1, 2, 1 + α, 2 - α} : Set R))
    (_hP3m : α * pp + pm - α * a ∈ ({0, 1, 2, 1 + α, 2 - α} : Set R))
    (_hzero : pp = 0 → pm = 0 → a = 0)
    (_hP3zero : pp = pm → pp + α * pm - α * a = 0 → a = 0) :
    (a = 2 - α ∧ b = 1 ∧ (C = α / 2 - 1 ∨ C = 1 - α / 2)) ∨
    (a = 1 + α ∧ b = 2 - α ∧ (C = (1 - α) / 2 ∨ C = (α - 1) / 2)) ∨
    (a = 1 ∧ b = 1 + α ∧ (C = 1 / 2 ∨ C = -1 / 2)) ∨
    (a = 2 ∧ b = 2) := by
  rcases hpm with hpm | hpm | hpm
  · exfalso
    have hval : pp + α * pm - α * a = -2 * α := by rw [hpp, hpm, ha]; linear_combination -hα
    rw [hval] at hP3p
    exact h3_S3_neg_two_alpha hα h4 h5 hP3p
  · exfalso
    have hval : pp + α * pm - α * a = -α := by rw [hpp, hpm, ha]; linear_combination -hα
    rw [hval] at hP3p
    exact h3_S3_neg_alpha hα h4 h5 hP3p
  · refine Or.inr (Or.inl ⟨ha, ?_, Or.inl ?_⟩)
    · rw [hbsum, hpp, hpm, ha]; linear_combination -hα
    · have h : -α = 2 * (1 + α) * C := by rw [← hCsum, hpp, hpm]; ring
      have h1m : (1 + α) * (1 - α) = -α := by linear_combination -hα
      have h2C : (1 + α) * (C * 2) = (1 + α) * (1 - α) := by rw [h1m]; linear_combination -h
      have hC : C * 2 = 1 - α := mul_left_cancel₀ h1a h2C
      rw [eq_div_iff h2]; linear_combination hC

private lemma h3_alg_one_add_p1a {R : Type*} [Field R] {α : R} (hα : α ^ 2 = α + 1)
    (h2 : (2 : R) ≠ 0) (h4 : (4 : R) ≠ 0) (h5 : (5 : R) ≠ 0) (_h9 : (9 : R) ≠ 0)
    (h1a : 1 + α ≠ 0) (_h2a : 2 - α ≠ 0)
    {a b C pp pm : R}
    (ha : a = 1 + α)
    (hb : b = 1 ∨ b = 2 ∨ b = 1 + α ∨ b = 2 - α)
    (hpp : pp = 1 + α)
    (hpm : pm = 0 ∨ pm = 1 ∨ pm = 1 + α)
    (hbsum : b = 2 * (pp + pm) - (1 + α) * a)
    (hCsum : pp - pm = 2 * (1 + α) * C)
    (hP3p : pp + α * pm - α * a ∈ ({0, 1, 2, 1 + α, 2 - α} : Set R))
    (_hP3m : α * pp + pm - α * a ∈ ({0, 1, 2, 1 + α, 2 - α} : Set R))
    (_hzero : pp = 0 → pm = 0 → a = 0)
    (_hP3zero : pp = pm → pp + α * pm - α * a = 0 → a = 0) :
    (a = 2 - α ∧ b = 1 ∧ (C = α / 2 - 1 ∨ C = 1 - α / 2)) ∨
    (a = 1 + α ∧ b = 2 - α ∧ (C = (1 - α) / 2 ∨ C = (α - 1) / 2)) ∨
    (a = 1 ∧ b = 1 + α ∧ (C = 1 / 2 ∨ C = -1 / 2)) ∨
    (a = 2 ∧ b = 2) := by
  rcases hpm with hpm | hpm | hpm
  · exfalso
    have hval : pp + α * pm - α * a = -α := by rw [hpp, hpm, ha]; linear_combination -hα
    rw [hval] at hP3p
    exact h3_S3_neg_alpha hα h4 h5 hP3p
  · refine Or.inr (Or.inl ⟨ha, ?_, Or.inr ?_⟩)
    · rw [hbsum, hpp, hpm, ha]; linear_combination -hα
    · have h : α = 2 * (1 + α) * C := by rw [← hCsum, hpp, hpm]; ring
      have h1m : (1 + α) * (α - 1) = α := by linear_combination hα
      have h2C : (1 + α) * (C * 2) = (1 + α) * (α - 1) := by rw [h1m]; linear_combination -h
      have hC : C * 2 = α - 1 := mul_left_cancel₀ h1a h2C
      rw [eq_div_iff h2]; linear_combination hC
  · exfalso
    have hbmem : b ∈ ({1, 2, 1 + α, 2 - α} : Set R) := by
      rcases hb with h | h | h | h <;> rw [h] <;> simp
    have hval : b = 2 + α := by rw [hbsum, hpp, hpm, ha]; linear_combination -hα
    rw [hval] at hbmem
    exact h3_S_two_add_alpha hα h4 hbmem

private lemma h3_alg_one_add {R : Type*} [Field R] {α : R} (hα : α ^ 2 = α + 1)
    (h2 : (2 : R) ≠ 0) (h4 : (4 : R) ≠ 0) (h5 : (5 : R) ≠ 0) (h9 : (9 : R) ≠ 0)
    (h1a : 1 + α ≠ 0) (h2a : 2 - α ≠ 0)
    {a b C pp pm : R}
    (ha : a = 1 + α)
    (hb : b = 1 ∨ b = 2 ∨ b = 1 + α ∨ b = 2 - α)
    (hpp : pp = 0 ∨ pp = 1 ∨ pp = 1 + α)
    (hpm : pm = 0 ∨ pm = 1 ∨ pm = 1 + α)
    (hbsum : b = 2 * (pp + pm) - (1 + α) * a)
    (hCsum : pp - pm = 2 * (1 + α) * C)
    (hP3p : pp + α * pm - α * a ∈ ({0, 1, 2, 1 + α, 2 - α} : Set R))
    (hP3m : α * pp + pm - α * a ∈ ({0, 1, 2, 1 + α, 2 - α} : Set R))
    (hzero : pp = 0 → pm = 0 → a = 0)
    (hP3zero : pp = pm → pp + α * pm - α * a = 0 → a = 0) :
    (a = 2 - α ∧ b = 1 ∧ (C = α / 2 - 1 ∨ C = 1 - α / 2)) ∨
    (a = 1 + α ∧ b = 2 - α ∧ (C = (1 - α) / 2 ∨ C = (α - 1) / 2)) ∨
    (a = 1 ∧ b = 1 + α ∧ (C = 1 / 2 ∨ C = -1 / 2)) ∨
    (a = 2 ∧ b = 2) := by
  rcases hpp with hpp | hpp | hpp
  · exact h3_alg_one_add_p0 (a := a) (b := b) (C := C)
      (pp := pp) (pm := pm) hα h2 h4 h5 h9 h1a h2a
      ha hb hpp hpm hbsum hCsum hP3p hP3m hzero hP3zero
  · exact h3_alg_one_add_p1 (a := a) (b := b) (C := C)
      (pp := pp) (pm := pm) hα h2 h4 h5 h9 h1a h2a
      ha hb hpp hpm hbsum hCsum hP3p hP3m hzero hP3zero
  · exact h3_alg_one_add_p1a (a := a) (b := b) (C := C)
      (pp := pp) (pm := pm) hα h2 h4 h5 h9 h1a h2a
      ha hb hpp hpm hbsum hCsum hP3p hP3m hzero hP3zero

private lemma h3_alg_two_sub_p0 {R : Type*} [Field R] {α : R} (hα : α ^ 2 = α + 1)
    (h2 : (2 : R) ≠ 0) (h4 : (4 : R) ≠ 0) (h5 : (5 : R) ≠ 0) (_h9 : (9 : R) ≠ 0)
    (h1a : 1 + α ≠ 0) (h2a : 2 - α ≠ 0)
    {a b C pp pm : R}
    (ha : a = 2 - α)
    (_hb : b = 1 ∨ b = 2 ∨ b = 1 + α ∨ b = 2 - α)
    (hpp : pp = 0)
    (hpm : pm = 0 ∨ pm = 1 ∨ pm = 1 + α)
    (hbsum : b = 2 * (pp + pm) - (1 + α) * a)
    (hCsum : pp - pm = 2 * (1 + α) * C)
    (hP3p : pp + α * pm - α * a ∈ ({0, 1, 2, 1 + α, 2 - α} : Set R))
    (_hP3m : α * pp + pm - α * a ∈ ({0, 1, 2, 1 + α, 2 - α} : Set R))
    (hzero : pp = 0 → pm = 0 → a = 0)
    (_hP3zero : pp = pm → pp + α * pm - α * a = 0 → a = 0) :
    (a = 2 - α ∧ b = 1 ∧ (C = α / 2 - 1 ∨ C = 1 - α / 2)) ∨
    (a = 1 + α ∧ b = 2 - α ∧ (C = (1 - α) / 2 ∨ C = (α - 1) / 2)) ∨
    (a = 1 ∧ b = 1 + α ∧ (C = 1 / 2 ∨ C = -1 / 2)) ∨
    (a = 2 ∧ b = 2) := by
  rcases hpm with hpm | hpm | hpm
  · exact absurd (hzero hpp hpm) (by rw [ha]; exact h2a)
  · refine Or.inl ⟨ha, ?_, Or.inl ?_⟩
    · rw [hbsum, hpp, hpm, ha]; linear_combination hα
    · have h : -1 = 2 * (1 + α) * C := by rw [← hCsum, hpp, hpm]; ring
      have h2C : (1 + α) * (C * 2) = (1 + α) * (α - 2) := by
        rw [show (1 + α) * (α - 2) = -1 by linear_combination hα]
        linear_combination -h
      have hC : C * 2 = α - 2 := mul_left_cancel₀ h1a h2C
      rw [show α / 2 - 1 = (α - 2) / 2 by field_simp, eq_div_iff h2]; linear_combination hC
  · exfalso
    have hval : pp + α * pm - α * a = α + 2 := by rw [hpp, hpm, ha]; linear_combination (2) * hα
    rw [hval] at hP3p
    rw [show α + 2 = 2 + α by ring] at hP3p
    exact h3_S3_two_add_alpha hα h4 h5 hP3p

private lemma h3_alg_two_sub_p1 {R : Type*} [Field R] {α : R} (hα : α ^ 2 = α + 1)
    (h2 : (2 : R) ≠ 0) (h4 : (4 : R) ≠ 0) (h5 : (5 : R) ≠ 0) (_h9 : (9 : R) ≠ 0)
    (h1a : 1 + α ≠ 0) (h2a : 2 - α ≠ 0)
    {a b C pp pm : R}
    (ha : a = 2 - α)
    (hb : b = 1 ∨ b = 2 ∨ b = 1 + α ∨ b = 2 - α)
    (hpp : pp = 1)
    (hpm : pm = 0 ∨ pm = 1 ∨ pm = 1 + α)
    (hbsum : b = 2 * (pp + pm) - (1 + α) * a)
    (hCsum : pp - pm = 2 * (1 + α) * C)
    (_hP3p : pp + α * pm - α * a ∈ ({0, 1, 2, 1 + α, 2 - α} : Set R))
    (hP3m : α * pp + pm - α * a ∈ ({0, 1, 2, 1 + α, 2 - α} : Set R))
    (_hzero : pp = 0 → pm = 0 → a = 0)
    (_hP3zero : pp = pm → pp + α * pm - α * a = 0 → a = 0) :
    (a = 2 - α ∧ b = 1 ∧ (C = α / 2 - 1 ∨ C = 1 - α / 2)) ∨
    (a = 1 + α ∧ b = 2 - α ∧ (C = (1 - α) / 2 ∨ C = (α - 1) / 2)) ∨
    (a = 1 ∧ b = 1 + α ∧ (C = 1 / 2 ∨ C = -1 / 2)) ∨
    (a = 2 ∧ b = 2) := by
  rcases hpm with hpm | hpm | hpm
  · refine Or.inl ⟨ha, ?_, Or.inr ?_⟩
    · rw [hbsum, hpp, hpm, ha]; linear_combination hα
    · have h : 1 = 2 * (1 + α) * C := by rw [← hCsum, hpp, hpm]; ring
      have h2C : (1 + α) * (C * 2) = (1 + α) * (2 - α) := by
        rw [show (1 + α) * (2 - α) = 1 by linear_combination -hα]
        linear_combination -h
      have hC : C * 2 = 2 - α := mul_left_cancel₀ h1a h2C
      rw [show 1 - α / 2 = (2 - α) / 2 by field_simp, eq_div_iff h2]; linear_combination hC
  · exfalso
    have hbmem : b ∈ ({1, 2, 1 + α, 2 - α} : Set R) := by
      rcases hb with h | h | h | h <;> rw [h] <;> simp
    have hval : b = 3 := by rw [hbsum, hpp, hpm, ha]; linear_combination hα
    rw [hval] at hbmem
    exact h3_S_three hα h4 hbmem
  · exfalso
    have hval : α * pp + pm - α * a = 2 + α := by rw [hpp, hpm, ha]; linear_combination hα
    rw [hval] at hP3m
    exact h3_S3_two_add_alpha hα h4 h5 hP3m

private lemma h3_alg_two_sub_p1a {R : Type*} [Field R] {α : R} (hα : α ^ 2 = α + 1)
    (_h2 : (2 : R) ≠ 0) (h4 : (4 : R) ≠ 0) (h5 : (5 : R) ≠ 0) (_h9 : (9 : R) ≠ 0)
    (_h1a : 1 + α ≠ 0) (h2a : 2 - α ≠ 0)
    {a b C pp pm : R}
    (ha : a = 2 - α)
    (_hb : b = 1 ∨ b = 2 ∨ b = 1 + α ∨ b = 2 - α)
    (hpp : pp = 1 + α)
    (hpm : pm = 0 ∨ pm = 1 ∨ pm = 1 + α)
    (_hbsum : b = 2 * (pp + pm) - (1 + α) * a)
    (_hCsum : pp - pm = 2 * (1 + α) * C)
    (hP3p : pp + α * pm - α * a ∈ ({0, 1, 2, 1 + α, 2 - α} : Set R))
    (hP3m : α * pp + pm - α * a ∈ ({0, 1, 2, 1 + α, 2 - α} : Set R))
    (_hzero : pp = 0 → pm = 0 → a = 0)
    (hP3zero : pp = pm → pp + α * pm - α * a = 0 → a = 0) :
    (a = 2 - α ∧ b = 1 ∧ (C = α / 2 - 1 ∨ C = 1 - α / 2)) ∨
    (a = 1 + α ∧ b = 2 - α ∧ (C = (1 - α) / 2 ∨ C = (α - 1) / 2)) ∨
    (a = 1 ∧ b = 1 + α ∧ (C = 1 / 2 ∨ C = -1 / 2)) ∨
    (a = 2 ∧ b = 2) := by
  rcases hpm with hpm | hpm | hpm
  · exfalso
    have hval : α * pp + pm - α * a = α + 2 := by rw [hpp, hpm, ha]; linear_combination (2) * hα
    rw [hval] at hP3m
    rw [show α + 2 = 2 + α by ring] at hP3m
    exact h3_S3_two_add_alpha hα h4 h5 hP3m
  · exfalso
    have hval : pp + α * pm - α * a = 2 + α := by rw [hpp, hpm, ha]; linear_combination hα
    rw [hval] at hP3p
    exact h3_S3_two_add_alpha hα h4 h5 hP3p
  · exfalso
    have hval : pp + α * pm - α * a = 3 + 2 * α := by rw [hpp, hpm, ha]; linear_combination (2) * hα
    rw [hval] at hP3p
    have hz : 3 + 2 * α = 0 → False := by
      intro h0
      have haz : a = 0 := hP3zero (by rw [hpp, hpm]) (by
        rw [show pp + α * pm - α * a = 3 + 2 * α by rw [hpp, hpm, ha]; linear_combination (2) * hα]
        exact h0)
      exact h2a (by rw [← haz, ha])
    exact h3_S3_three_add_two_alpha hα h4 h5 hP3p hz

private lemma h3_alg_two_sub {R : Type*} [Field R] {α : R} (hα : α ^ 2 = α + 1)
    (h2 : (2 : R) ≠ 0) (h4 : (4 : R) ≠ 0) (h5 : (5 : R) ≠ 0) (h9 : (9 : R) ≠ 0)
    (h1a : 1 + α ≠ 0) (h2a : 2 - α ≠ 0)
    {a b C pp pm : R}
    (ha : a = 2 - α)
    (hb : b = 1 ∨ b = 2 ∨ b = 1 + α ∨ b = 2 - α)
    (hpp : pp = 0 ∨ pp = 1 ∨ pp = 1 + α)
    (hpm : pm = 0 ∨ pm = 1 ∨ pm = 1 + α)
    (hbsum : b = 2 * (pp + pm) - (1 + α) * a)
    (hCsum : pp - pm = 2 * (1 + α) * C)
    (hP3p : pp + α * pm - α * a ∈ ({0, 1, 2, 1 + α, 2 - α} : Set R))
    (hP3m : α * pp + pm - α * a ∈ ({0, 1, 2, 1 + α, 2 - α} : Set R))
    (hzero : pp = 0 → pm = 0 → a = 0)
    (hP3zero : pp = pm → pp + α * pm - α * a = 0 → a = 0) :
    (a = 2 - α ∧ b = 1 ∧ (C = α / 2 - 1 ∨ C = 1 - α / 2)) ∨
    (a = 1 + α ∧ b = 2 - α ∧ (C = (1 - α) / 2 ∨ C = (α - 1) / 2)) ∨
    (a = 1 ∧ b = 1 + α ∧ (C = 1 / 2 ∨ C = -1 / 2)) ∨
    (a = 2 ∧ b = 2) := by
  rcases hpp with hpp | hpp | hpp
  · exact h3_alg_two_sub_p0 (a := a) (b := b) (C := C)
      (pp := pp) (pm := pm) hα h2 h4 h5 h9 h1a h2a
      ha hb hpp hpm hbsum hCsum hP3p hP3m hzero hP3zero
  · exact h3_alg_two_sub_p1 (a := a) (b := b) (C := C)
      (pp := pp) (pm := pm) hα h2 h4 h5 h9 h1a h2a
      ha hb hpp hpm hbsum hCsum hP3p hP3m hzero hP3zero
  · exact h3_alg_two_sub_p1a (a := a) (b := b) (C := C)
      (pp := pp) (pm := pm) hα h2 h4 h5 h9 h1a h2a
      ha hb hpp hpm hbsum hCsum hP3p hP3m hzero hP3zero

private lemma h3_alg_two_p0 {R : Type*} [Field R] {α : R} (hα : α ^ 2 = α + 1)
    (h2 : (2 : R) ≠ 0) (h4 : (4 : R) ≠ 0) (h5 : (5 : R) ≠ 0) (_h9 : (9 : R) ≠ 0)
    (_h1a : 1 + α ≠ 0) (_h2a : 2 - α ≠ 0)
    {a b C pp pm : R}
    (ha : a = 2)
    (_hb : b = 1 ∨ b = 2 ∨ b = 1 + α ∨ b = 2 - α)
    (hpp : pp = 0)
    (hpm : pm = 0 ∨ pm = 1 ∨ pm = 1 + α)
    (_hbsum : b = 2 * (pp + pm) - (1 + α) * a)
    (_hCsum : pp - pm = 2 * (1 + α) * C)
    (hP3p : pp + α * pm - α * a ∈ ({0, 1, 2, 1 + α, 2 - α} : Set R))
    (hP3m : α * pp + pm - α * a ∈ ({0, 1, 2, 1 + α, 2 - α} : Set R))
    (hzero : pp = 0 → pm = 0 → a = 0)
    (_hP3zero : pp = pm → pp + α * pm - α * a = 0 → a = 0) :
    (a = 2 - α ∧ b = 1 ∧ (C = α / 2 - 1 ∨ C = 1 - α / 2)) ∨
    (a = 1 + α ∧ b = 2 - α ∧ (C = (1 - α) / 2 ∨ C = (α - 1) / 2)) ∨
    (a = 1 ∧ b = 1 + α ∧ (C = 1 / 2 ∨ C = -1 / 2)) ∨
    (a = 2 ∧ b = 2) := by
  rcases hpm with hpm | hpm | hpm
  · exact absurd (hzero hpp hpm) (by rw [ha]; exact h2)
  · exfalso
    have hval : pp + α * pm - α * a = -α := by rw [hpp, hpm, ha]; ring
    rw [hval] at hP3p
    exact h3_S3_neg_alpha hα h4 h5 hP3p
  · exfalso
    have hval : α * pp + pm - α * a = 1 - α := by rw [hpp, hpm, ha]; ring
    rw [hval] at hP3m
    exact h3_S3_one_sub_alpha hα h4 hP3m

private lemma h3_alg_two_p1 {R : Type*} [Field R] {α : R} (hα : α ^ 2 = α + 1)
    (_h2 : (2 : R) ≠ 0) (h4 : (4 : R) ≠ 0) (h5 : (5 : R) ≠ 0) (h9 : (9 : R) ≠ 0)
    (_h1a : 1 + α ≠ 0) (_h2a : 2 - α ≠ 0)
    {a b C pp pm : R}
    (ha : a = 2)
    (_hb : b = 1 ∨ b = 2 ∨ b = 1 + α ∨ b = 2 - α)
    (hpp : pp = 1)
    (hpm : pm = 0 ∨ pm = 1 ∨ pm = 1 + α)
    (hbsum : b = 2 * (pp + pm) - (1 + α) * a)
    (_hCsum : pp - pm = 2 * (1 + α) * C)
    (hP3p : pp + α * pm - α * a ∈ ({0, 1, 2, 1 + α, 2 - α} : Set R))
    (_hP3m : α * pp + pm - α * a ∈ ({0, 1, 2, 1 + α, 2 - α} : Set R))
    (_hzero : pp = 0 → pm = 0 → a = 0)
    (_hP3zero : pp = pm → pp + α * pm - α * a = 0 → a = 0) :
    (a = 2 - α ∧ b = 1 ∧ (C = α / 2 - 1 ∨ C = 1 - α / 2)) ∨
    (a = 1 + α ∧ b = 2 - α ∧ (C = (1 - α) / 2 ∨ C = (α - 1) / 2)) ∨
    (a = 1 ∧ b = 1 + α ∧ (C = 1 / 2 ∨ C = -1 / 2)) ∨
    (a = 2 ∧ b = 2) := by
  rcases hpm with hpm | hpm | hpm
  · exfalso
    have hval : pp + α * pm - α * a = 1 - 2 * α := by rw [hpp, hpm, ha]; ring
    rw [hval] at hP3p
    exact h3_S3_one_sub_two_alpha hα h4 h5 h9 hP3p
  · exfalso
    have hval : pp + α * pm - α * a = 1 - α := by rw [hpp, hpm, ha]; ring
    rw [hval] at hP3p
    exact h3_S3_one_sub_alpha hα h4 hP3p
  · refine Or.inr (Or.inr (Or.inr ⟨ha, ?_⟩))
    rw [hbsum, hpp, hpm, ha]; ring

private lemma h3_alg_two_p1a {R : Type*} [Field R] {α : R} (hα : α ^ 2 = α + 1)
    (_h2 : (2 : R) ≠ 0) (h4 : (4 : R) ≠ 0) (h5 : (5 : R) ≠ 0) (_h9 : (9 : R) ≠ 0)
    (_h1a : 1 + α ≠ 0) (_h2a : 2 - α ≠ 0)
    {a b C pp pm : R}
    (ha : a = 2)
    (_hb : b = 1 ∨ b = 2 ∨ b = 1 + α ∨ b = 2 - α)
    (hpp : pp = 1 + α)
    (hpm : pm = 0 ∨ pm = 1 ∨ pm = 1 + α)
    (hbsum : b = 2 * (pp + pm) - (1 + α) * a)
    (_hCsum : pp - pm = 2 * (1 + α) * C)
    (hP3p : pp + α * pm - α * a ∈ ({0, 1, 2, 1 + α, 2 - α} : Set R))
    (_hP3m : α * pp + pm - α * a ∈ ({0, 1, 2, 1 + α, 2 - α} : Set R))
    (_hzero : pp = 0 → pm = 0 → a = 0)
    (_hP3zero : pp = pm → pp + α * pm - α * a = 0 → a = 0) :
    (a = 2 - α ∧ b = 1 ∧ (C = α / 2 - 1 ∨ C = 1 - α / 2)) ∨
    (a = 1 + α ∧ b = 2 - α ∧ (C = (1 - α) / 2 ∨ C = (α - 1) / 2)) ∨
    (a = 1 ∧ b = 1 + α ∧ (C = 1 / 2 ∨ C = -1 / 2)) ∨
    (a = 2 ∧ b = 2) := by
  rcases hpm with hpm | hpm | hpm
  · exfalso
    have hval : pp + α * pm - α * a = 1 - α := by rw [hpp, hpm, ha]; ring
    rw [hval] at hP3p
    exact h3_S3_one_sub_alpha hα h4 hP3p
  · refine Or.inr (Or.inr (Or.inr ⟨ha, ?_⟩))
    rw [hbsum, hpp, hpm, ha]; ring
  · exfalso
    have hval : pp + α * pm - α * a = 2 + α := by rw [hpp, hpm, ha]; linear_combination hα
    rw [hval] at hP3p
    exact h3_S3_two_add_alpha hα h4 h5 hP3p

private lemma h3_alg_two {R : Type*} [Field R] {α : R} (hα : α ^ 2 = α + 1)
    (h2 : (2 : R) ≠ 0) (h4 : (4 : R) ≠ 0) (h5 : (5 : R) ≠ 0) (h9 : (9 : R) ≠ 0)
    (h1a : 1 + α ≠ 0) (h2a : 2 - α ≠ 0)
    {a b C pp pm : R}
    (ha : a = 2)
    (hb : b = 1 ∨ b = 2 ∨ b = 1 + α ∨ b = 2 - α)
    (hpp : pp = 0 ∨ pp = 1 ∨ pp = 1 + α)
    (hpm : pm = 0 ∨ pm = 1 ∨ pm = 1 + α)
    (hbsum : b = 2 * (pp + pm) - (1 + α) * a)
    (hCsum : pp - pm = 2 * (1 + α) * C)
    (hP3p : pp + α * pm - α * a ∈ ({0, 1, 2, 1 + α, 2 - α} : Set R))
    (hP3m : α * pp + pm - α * a ∈ ({0, 1, 2, 1 + α, 2 - α} : Set R))
    (hzero : pp = 0 → pm = 0 → a = 0)
    (hP3zero : pp = pm → pp + α * pm - α * a = 0 → a = 0) :
    (a = 2 - α ∧ b = 1 ∧ (C = α / 2 - 1 ∨ C = 1 - α / 2)) ∨
    (a = 1 + α ∧ b = 2 - α ∧ (C = (1 - α) / 2 ∨ C = (α - 1) / 2)) ∨
    (a = 1 ∧ b = 1 + α ∧ (C = 1 / 2 ∨ C = -1 / 2)) ∨
    (a = 2 ∧ b = 2) := by
  rcases hpp with hpp | hpp | hpp
  · exact h3_alg_two_p0 (a := a) (b := b) (C := C)
      (pp := pp) (pm := pm) hα h2 h4 h5 h9 h1a h2a
      ha hb hpp hpm hbsum hCsum hP3p hP3m hzero hP3zero
  · exact h3_alg_two_p1 (a := a) (b := b) (C := C)
      (pp := pp) (pm := pm) hα h2 h4 h5 h9 h1a h2a
      ha hb hpp hpm hbsum hCsum hP3p hP3m hzero hP3zero
  · exact h3_alg_two_p1a (a := a) (b := b) (C := C)
      (pp := pp) (pm := pm) hα h2 h4 h5 h9 h1a h2a
      ha hb hpp hpm hbsum hCsum hP3p hP3m hzero hP3zero

private lemma h3_classify_alg {R : Type*} [Field R] {α : R} (hα : α ^ 2 = α + 1)
    (h2 : (2 : R) ≠ 0) (h4 : (4 : R) ≠ 0) (h5 : (5 : R) ≠ 0) (h9 : (9 : R) ≠ 0)
    (h1a : 1 + α ≠ 0) (h2a : 2 - α ≠ 0)
    {a b C pp pm : R}
    (ha : a = 1 ∨ a = 1 + α ∨ a = 2 - α ∨ a = 2)
    (hb : b = 1 ∨ b = 2 ∨ b = 1 + α ∨ b = 2 - α)
    (hpp : pp = 0 ∨ pp = 1 ∨ pp = 1 + α)
    (hpm : pm = 0 ∨ pm = 1 ∨ pm = 1 + α)
    (hbsum : b = 2 * (pp + pm) - (1 + α) * a)
    (hCsum : pp - pm = 2 * (1 + α) * C)
    (hP3p : pp + α * pm - α * a ∈ ({0, 1, 2, 1 + α, 2 - α} : Set R))
    (hP3m : α * pp + pm - α * a ∈ ({0, 1, 2, 1 + α, 2 - α} : Set R))
    (hzero : pp = 0 → pm = 0 → a = 0)
    (hP3zero : pp = pm → pp + α * pm - α * a = 0 → a = 0) :
    (a = 2 - α ∧ b = 1 ∧ (C = α / 2 - 1 ∨ C = 1 - α / 2)) ∨
    (a = 1 + α ∧ b = 2 - α ∧ (C = (1 - α) / 2 ∨ C = (α - 1) / 2)) ∨
    (a = 1 ∧ b = 1 + α ∧ (C = 1 / 2 ∨ C = -1 / 2)) ∨
    (a = 2 ∧ b = 2) := by
  rcases ha with ha | ha | ha | ha
  · exact h3_alg_one (a := a) (b := b) (C := C)
      (pp := pp) (pm := pm) hα h2 h4 h5 h9 h1a h2a
      ha hb hpp hpm hbsum hCsum hP3p hP3m hzero hP3zero
  · exact h3_alg_one_add (a := a) (b := b) (C := C)
      (pp := pp) (pm := pm) hα h2 h4 h5 h9 h1a h2a
      ha hb hpp hpm hbsum hCsum hP3p hP3m hzero hP3zero
  · exact h3_alg_two_sub (a := a) (b := b) (C := C)
      (pp := pp) (pm := pm) hα h2 h4 h5 h9 h1a h2a
      ha hb hpp hpm hbsum hCsum hP3p hP3m hzero hP3zero
  · exact h3_alg_two (a := a) (b := b) (C := C)
      (pp := pp) (pm := pm) hα h2 h4 h5 h9 h1a h2a
      ha hb hpp hpm hbsum hCsum hP3p hP3m hzero hP3zero

private lemma h3_one_sub_ne_zero {R : Type*} [CommRing R] [Nontrivial R] {α : R}
    (hα : α ^ 2 = α + 1) : (1 - α : R) ≠ 0 := by
  intro hh
  have hα1 : α = 1 := by linear_combination -hh
  rw [hα1] at hα
  exact one_ne_zero (by linear_combination -hα)

private lemma h3_P3_sub_form {R : Type*} [CommRing R] (α ψ₁ ψ₂ : R) :
    (1 - α) * ψ₁ + (-1) * (1 + α) * ψ₂ = (1 - α) * ψ₁ - (1 + α) * ψ₂ := by ring

private lemma h3_P1_sub_w {R : Type*} [Field R] (h2 : (2 : R) ≠ 0) (α w₁ w₂ : R) :
    (w₁ + (-1) * (2 - α) * w₂) / 2 = (w₁ - (2 - α) * w₂) / 2 := by field_simp; ring

private lemma h3_P1_sub_form {R : Type*} [CommRing R] (α ψ₁ ψ₂ : R) :
    (1 + α) * (ψ₁ + (-1) * ψ₂) = (1 + α) * (ψ₁ - ψ₂) := by ring

private lemma h3_P1_zero_neg {α w₁ w₂ ψ₁ ψ₂ : ZMod p} (hα : α ^ 2 = α + 1)
    (hc : H3EtaConstraints α w₁ w₂ ψ₁ ψ₂)
    (h : ((1 + α) * (ψ₁ * w₁) + ψ₂ * w₂) / 2 + (-1) * (1 + α) * h3Cross α w₁ w₂ ψ₁ ψ₂ = 0) :
    (1 + α) * (ψ₁ - ψ₂) = 0 ∧ (w₁ - (2 - α) * w₂) / 2 = 0 := by
  have h2nz : (2 : ZMod p) ≠ 0 := h3_two_ne_zero_of_sq hα
  have hssm1 : (-1 : ZMod p) * (-1) = 1 := by
    have h2 := neg_mul_neg (1 : ZMod p) (1 : ZMod p); rw [mul_one] at h2; exact h2
  have hz := h3_P1_zero hα hc (Or.inr rfl) hssm1 h
  constructor
  · have h1 := hz.1
    rw [show (1 + α) * (ψ₁ + (-1) * ψ₂) = (1 + α) * (ψ₁ - ψ₂) from
      h3_P1_sub_form α ψ₁ ψ₂] at h1
    exact h1
  · have h2 := hz.2
    rw [show (w₁ + (-1) * (2 - α) * w₂) / 2 = (w₁ - (2 - α) * w₂) / 2 by
      rw [show (w₁ + (-1) * (2 - α) * w₂) / 2 =
        (w₁ - (2 - α) * w₂) / 2 from h3_P1_sub_w h2nz α w₁ w₂]] at h2
    exact h2

private lemma h3_P1_sum {R : Type*} [Field R] (h2 : (2 : R) ≠ 0) (α ψ₁ ψ₂ w₁ w₂ C : R) :
    (((1 + α) * (ψ₁ * w₁) + ψ₂ * w₂) / 2 + (1 : R) * (1 + α) * C) +
      (((1 + α) * (ψ₁ * w₁) + ψ₂ * w₂) / 2 + (-1) * (1 + α) * C) =
      (1 + α) * (ψ₁ * w₁) + ψ₂ * w₂ := by field_simp; ring

private lemma h3_P1_diff {R : Type*} [Field R] (h2 : (2 : R) ≠ 0) (α ψ₁ ψ₂ w₁ w₂ C : R) :
    (((1 + α) * (ψ₁ * w₁) + ψ₂ * w₂) / 2 + (1 : R) * (1 + α) * C) -
      (((1 + α) * (ψ₁ * w₁) + ψ₂ * w₂) / 2 + (-1) * (1 + α) * C) =
      2 * (1 + α) * C := by field_simp; ring

private lemma h3_P3p_form {R : Type*} [Field R] (h2 : (2 : R) ≠ 0) {α : R} (hα : α ^ 2 = α + 1)
    (ψ₁ ψ₂ w₁ w₂ C : R) :
    ((2 - α) * (ψ₁ * w₁) + (1 + α) * (ψ₂ * w₂)) / 2 - (1 : R) * α * C =
      (((1 + α) * (ψ₁ * w₁) + ψ₂ * w₂) / 2 + (1 : R) * (1 + α) * C) +
        α * (((1 + α) * (ψ₁ * w₁) + ψ₂ * w₂) / 2 + (-1) * (1 + α) * C) -
        α * (2 * (ψ₁ * w₁)) := by field_simp; ring_nf; rw [hα]; ring

private lemma h3_P3m_form {R : Type*} [Field R] (h2 : (2 : R) ≠ 0) {α : R} (hα : α ^ 2 = α + 1)
    (ψ₁ ψ₂ w₁ w₂ C : R) :
    ((2 - α) * (ψ₁ * w₁) + (1 + α) * (ψ₂ * w₂)) / 2 - (-1 : R) * α * C =
      α * (((1 + α) * (ψ₁ * w₁) + ψ₂ * w₂) / 2 + (1 : R) * (1 + α) * C) +
        (((1 + α) * (ψ₁ * w₁) + ψ₂ * w₂) / 2 + (-1) * (1 + α) * C) -
        α * (2 * (ψ₁ * w₁)) := by field_simp; ring_nf; rw [hα]; ring

private lemma h3_S3_five_sub_three_alpha {R : Type*} [Field R] {α : R} (hα : α ^ 2 = α + 1)
    (h5 : (5 : R) ≠ 0) (h9 : (9 : R) ≠ 0) (h16 : (16 : R) ≠ 0)
    (h : 5 - 3 * α ∈ ({0, 1, 2, 1 + α, 2 - α} : Set R)) : False := by
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at h
  rcases h with h | h | h | h | h
  · have t := h3_norm_eq_zero hα (show (5 : R) + (-3) * α = 0 by linear_combination h);
    norm_num at t
  · have t := h3_norm_eq_zero hα (show (4 : R) + (-3) * α = 0 by linear_combination h);
    norm_num at t; exact h5 t
  · have t := h3_norm_eq_zero hα (show (3 : R) + (-3) * α = 0 by linear_combination h);
    norm_num at t; exact h9 t
  · have t := h3_norm_eq_zero hα (show (4 : R) + (-4) * α = 0 by linear_combination h);
    norm_num at t; exact h16 t
  · have t := h3_norm_eq_zero hα (show (3 : R) + (-2) * α = 0 by linear_combination h);
    norm_num at t

private lemma h3_v_hv3 (hp5 : p ≠ 5) (hα : α ^ 2 = α + 1)
    (hc : H3EtaConstraints α w₁ w₂ ψ₁ ψ₂) (hψ2 : ψ₂ = 0) (hw2 : w₂ = 0)
    (hC : h3Cross α w₁ w₂ ψ₁ ψ₂ = 0) :
    (ψ₁ * w₁ / 2 ∈ ({0, 1, 2 - α} : Set (ZMod p))) ∧
      ((2 - α) * (ψ₁ * w₁ / 2) ∈ ({0, 1, 2, 1 + α, 2 - α} : Set (ZMod p))) := by
  have h1a := h3_one_add_ne_zero (R := ZMod p) hα
  have hP1 : (1 + α) * (ψ₁ * w₁ / 2) ∈ ({0, 1, 1 + α} : Set (ZMod p)) := by
    have h := family_one_mem hp5 hα hc (s := 1) (Or.inl rfl)
    have hEq : ((1 + α) * (ψ₁ * w₁) + ψ₂ * w₂) / 2 +
        1 * (1 + α) * h3Cross α w₁ w₂ ψ₁ ψ₂ = (1 + α) * (ψ₁ * w₁ / 2) := by
      rw [hC, hψ2, hw2]; ring
    rwa [hEq] at h
  have hP3 : (2 - α) * (ψ₁ * w₁ / 2) ∈ ({0, 1, 2, 1 + α, 2 - α} : Set (ZMod p)) := by
    have h := family_three_mem hα hc (s := 1) (Or.inl rfl)
    have hEq : ((2 - α) * (ψ₁ * w₁) + (1 + α) * (ψ₂ * w₂)) / 2 -
        1 * α * h3Cross α w₁ w₂ ψ₁ ψ₂ = (2 - α) * (ψ₁ * w₁ / 2) := by
      rw [hC, hψ2, hw2]; ring
    rwa [hEq] at h
  constructor
  · have h := hP1
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at h ⊢
    rcases h with h | h | h
    · left; exact (mul_eq_zero.mp h).resolve_left h1a
    · right; right
      calc ψ₁ * w₁ / 2 = ((2 - α) * (1 + α)) * (ψ₁ * w₁ / 2) := by
            rw [h3_two_sub_mul_one_add (R := ZMod p) hα, one_mul]
        _ = (2 - α) * ((1 + α) * (ψ₁ * w₁ / 2)) := by ring
        _ = (2 - α) * 1 := by rw [h]
        _ = 2 - α := by ring
    · right; left; exact mul_left_cancel₀ h1a (by simpa using h)
  · exact hP3

private lemma h3_v_cases (hp5 : p ≠ 5) (hα : α ^ 2 = α + 1)
    (hc : H3EtaConstraints α w₁ w₂ ψ₁ ψ₂) (hw : w₁ ≠ 0 ∨ w₂ ≠ 0)
    (_hψ2 : ψ₂ = 0) (hw2 : w₂ = 0)
    (hP3 : (2 - α) * (ψ₁ * w₁ / 2) ∈ ({0, 1, 2, 1 + α, 2 - α} : Set (ZMod p)))
    (hv3 : ψ₁ * w₁ / 2 ∈ ({0, 1, 2 - α} : Set (ZMod p))) : False := by
  have hp7 : 7 < p := seven_lt_of_sq_eq_add_one hp5 hα
  have h2nz : (2 : ZMod p) ≠ 0 := h3_two_ne_zero hp7
  have h1a := h3_one_add_ne_zero (R := ZMod p) hα
  have h5nz : (5 : ZMod p) ≠ 0 := h3_five_ne_zero hp7
  have h9nz : (9 : ZMod p) ≠ 0 := h3_nine_ne_zero hp7
  have h16nz : (16 : ZMod p) ≠ 0 := h3_sixteen_ne_zero hp7
  have h0S : (0 : ZMod p) ∉ ({1, 2, 1 + α, 2 - α} : Set (ZMod p)) := by
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or]
    exact ⟨fun hh => one_ne_zero hh.symm, fun hh => h3_two_ne_zero_of_sq hα hh.symm,
      fun hh => h1a hh.symm, fun hh => h3_two_sub_ne_zero (R := ZMod p) hα hh.symm⟩
  have h4S : (4 : ZMod p) ∉ ({1, 2, 1 + α, 2 - α} : Set (ZMod p)) := by
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or]
    refine ⟨?_, ?_, ?_, ?_⟩
    · intro hh; exact h3_three_ne_zero hp7 (by linear_combination hh)
    · intro hh; exact h2nz (by linear_combination hh)
    · intro hh; exact h5nz (h3_c3m1 hα (by linear_combination hh))
    · intro hh; exact h5nz (h3_c21p hα (by linear_combination hh))
  rcases hv3 with hv3 | hv3 | hv3
  · have h2 : ψ₁ * w₁ = 0 := by
      have := mul_div_cancel₀ (ψ₁ * w₁) h2nz
      rw [hv3, mul_zero] at this; exact this.symm
    have hz1 : ψ₁ = 0 ∧ w₁ = 0 := by
      rcases (two_mul_mem hα hc).1 with hz | hmem
      · exact hz
      · have h2v : 2 * (ψ₁ * w₁) = 0 := by rw [h2, mul_zero]
        rw [h2v] at hmem
        exact absurd hmem h0S
    exact hw.elim (fun h1 => h1 hz1.2) (fun h2' => h2' hw2)
  · have h2 : ψ₁ * w₁ = 2 := by
      have := mul_div_cancel₀ (ψ₁ * w₁) h2nz
      rw [hv3, mul_one] at this; exact this.symm
    have haS : 2 * (ψ₁ * w₁) ∈ ({1, 2, 1 + α, 2 - α} : Set (ZMod p)) := by
      have hne := coord_mul_ne_zero hp5 hα hc hw
      rcases (two_mul_mem hα hc).1 with hz | hmem
      · exact absurd (by rw [hz.1, hz.2, mul_zero]) hne
      · exact hmem
    have h4 : 2 * (ψ₁ * w₁) = 4 := by rw [h2]; ring
    rw [h4] at haS
    exact absurd haS h4S
  · have hP3' : 5 - 3 * α ∈ ({0, 1, 2, 1 + α, 2 - α} : Set (ZMod p)) := by
      rw [hv3] at hP3
      rwa [show (2 - α) * (2 - α) = 5 - 3 * α by linear_combination hα] at hP3
    exact h3_S3_five_sub_three_alpha hα h5nz h9nz h16nz hP3'

private lemma h3_v_ne_zero (hp5 : p ≠ 5) (hα : α ^ 2 = α + 1)
    (hc : H3EtaConstraints α w₁ w₂ ψ₁ ψ₂) (hw : w₁ ≠ 0 ∨ w₂ ≠ 0) : ψ₂ * w₂ ≠ 0 := by
  have hp7 : 7 < p := seven_lt_of_sq_eq_add_one hp5 hα
  have h1a := h3_one_add_ne_zero (R := ZMod p) hα
  have h0S : (0 : ZMod p) ∉ ({1, 2, 1 + α, 2 - α} : Set (ZMod p)) := by
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or]
    exact ⟨fun hh => one_ne_zero hh.symm, fun hh => h3_two_ne_zero_of_sq hα hh.symm,
      fun hh => h1a hh.symm, fun hh => h3_two_sub_ne_zero (R := ZMod p) hα hh.symm⟩
  intro hv
  have hz : ψ₂ = 0 ∧ w₂ = 0 := by
    rcases (two_mul_mem hα hc).2 with hz | hmem
    · exact hz
    · have h2v : 2 * (ψ₂ * w₂) = 0 := by rw [hv, mul_zero]
      rw [h2v] at hmem
      exact absurd hmem h0S
  obtain ⟨hψ2, hw2⟩ := hz
  have hC : h3Cross α w₁ w₂ ψ₁ ψ₂ = 0 := by simp only [h3Cross]; rw [hψ2, hw2]; ring
  obtain ⟨hv3, hP3⟩ := h3_v_hv3 hp5 hα hc hψ2 hw2 hC
  exact h3_v_cases hp5 hα hc hw hψ2 hw2 hP3 hv3
private lemma h3_neg_one_div_two {R : Type*} [Field R] (h2 : (2 : R) ≠ 0) :
    (-1 : R) / 2 = -(1 / 2) := by field_simp

private lemma h3_zmod_zero_pair (hα : α ^ 2 = α + 1) (hc : H3EtaConstraints α w₁ w₂ ψ₁ ψ₂) :
    (((1 + α) * (ψ₁ * w₁) + ψ₂ * w₂) / 2 +
        1 * (1 + α) * h3Cross α w₁ w₂ ψ₁ ψ₂) = 0 →
      (((1 + α) * (ψ₁ * w₁) + ψ₂ * w₂) / 2 +
        (-1) * (1 + α) * h3Cross α w₁ w₂ ψ₁ ψ₂) = 0 → 2 * (ψ₁ * w₁) = 0 := by
  intro hp hm
  have h2nz : (2 : ZMod p) ≠ 0 := h3_two_ne_zero_of_sq hα
  have h1a := h3_one_add_ne_zero (R := ZMod p) hα
  have h1 := h3_P1_zero hα hc (Or.inl rfl) (by ring) hp
  have h2 := h3_P1_zero_neg hα hc hm
  have hσ1 : ψ₁ + ψ₂ = 0 := by
    have := (mul_eq_zero.mp h1.1).resolve_left h1a; simpa using this
  have hσ2 : ψ₁ - ψ₂ = 0 := (mul_eq_zero.mp h2.1).resolve_left h1a
  have h2ψ : (2 : ZMod p) * ψ₁ = 0 := by linear_combination hσ1 + hσ2
  have hψ1 : ψ₁ = 0 := (mul_eq_zero.mp h2ψ).resolve_left h2nz
  rw [hψ1, zero_mul, mul_zero]

private lemma h3_zmod_P3_zero_pair (hα : α ^ 2 = α + 1)
    (hc : H3EtaConstraints α w₁ w₂ ψ₁ ψ₂) :
    (((1 + α) * (ψ₁ * w₁) + ψ₂ * w₂) / 2 +
        1 * (1 + α) * h3Cross α w₁ w₂ ψ₁ ψ₂) =
        (((1 + α) * (ψ₁ * w₁) + ψ₂ * w₂) / 2 +
        (-1) * (1 + α) * h3Cross α w₁ w₂ ψ₁ ψ₂) →
      (((1 + α) * (ψ₁ * w₁) + ψ₂ * w₂) / 2 +
        1 * (1 + α) * h3Cross α w₁ w₂ ψ₁ ψ₂) +
        α * (((1 + α) * (ψ₁ * w₁) + ψ₂ * w₂) / 2 +
        (-1) * (1 + α) * h3Cross α w₁ w₂ ψ₁ ψ₂) - α * (2 * (ψ₁ * w₁)) = 0 →
      2 * (ψ₁ * w₁) = 0 := by
  intro hppeq h
  have h2nz : (2 : ZMod p) ≠ 0 := h3_two_ne_zero_of_sq hα
  have hssm1 : (-1 : ZMod p) * (-1) = 1 := by
    have h2 := neg_mul_neg (1 : ZMod p) (1 : ZMod p); rw [mul_one] at h2; exact h2
  have h1 := h3_P3_zero hα hc (Or.inl rfl) (by ring)
    ((h3_P3p_form h2nz hα ψ₁ ψ₂ w₁ w₂ (h3Cross α w₁ w₂ ψ₁ ψ₂)).trans h)
  have h2hyp : ((2 - α) * (ψ₁ * w₁) + (1 + α) * (ψ₂ * w₂)) / 2 -
      (-1) * α * h3Cross α w₁ w₂ ψ₁ ψ₂ = 0 := by
    rw [show ((2 - α) * (ψ₁ * w₁) + (1 + α) * (ψ₂ * w₂)) / 2 -
        (-1) * α * h3Cross α w₁ w₂ ψ₁ ψ₂ =
        α * (((1 + α) * (ψ₁ * w₁) + ψ₂ * w₂) / 2 +
          1 * (1 + α) * h3Cross α w₁ w₂ ψ₁ ψ₂) +
          (((1 + α) * (ψ₁ * w₁) + ψ₂ * w₂) / 2 +
          (-1) * (1 + α) * h3Cross α w₁ w₂ ψ₁ ψ₂) - α * (2 * (ψ₁ * w₁)) from
      h3_P3m_form h2nz hα ψ₁ ψ₂ w₁ w₂ (h3Cross α w₁ w₂ ψ₁ ψ₂)]
    rw [show α * (((1 + α) * (ψ₁ * w₁) + ψ₂ * w₂) / 2 +
          1 * (1 + α) * h3Cross α w₁ w₂ ψ₁ ψ₂) +
          (((1 + α) * (ψ₁ * w₁) + ψ₂ * w₂) / 2 +
          (-1) * (1 + α) * h3Cross α w₁ w₂ ψ₁ ψ₂) - α * (2 * (ψ₁ * w₁)) =
          (((1 + α) * (ψ₁ * w₁) + ψ₂ * w₂) / 2 +
          1 * (1 + α) * h3Cross α w₁ w₂ ψ₁ ψ₂) +
          α * (((1 + α) * (ψ₁ * w₁) + ψ₂ * w₂) / 2 +
          (-1) * (1 + α) * h3Cross α w₁ w₂ ψ₁ ψ₂) - α * (2 * (ψ₁ * w₁)) by
      rw [hppeq]; ring]
    exact h
  have h2 := h3_P3_zero hα hc (Or.inr rfl) hssm1 h2hyp
  have h1' : (1 - α) * ψ₁ + (1 + α) * ψ₂ = 0 := by
    have := h1.1; simpa using this
  have h2' : (1 - α) * ψ₁ - (1 + α) * ψ₂ = 0 := by
    have := h2.1
    rw [show (1 - α) * ψ₁ + (-1) * (1 + α) * ψ₂ = (1 - α) * ψ₁ - (1 + α) * ψ₂ from
      h3_P3_sub_form α ψ₁ ψ₂] at this
    exact this
  have h2ψ : (2 : ZMod p) * ((1 - α) * ψ₁) = 0 := by linear_combination h1' + h2'
  have h1ψ : (1 - α) * ψ₁ = 0 := (mul_eq_zero.mp h2ψ).resolve_left h2nz
  have h1m : (1 - α : ZMod p) ≠ 0 := h3_one_sub_ne_zero (R := ZMod p) hα
  have hψ1 : ψ₁ = 0 := (mul_eq_zero.mp h1ψ).resolve_left h1m
  rw [hψ1]; ring

private lemma h3_zmod_ha (hp5 : p ≠ 5) (hα : α ^ 2 = α + 1)
    (hc : H3EtaConstraints α w₁ w₂ ψ₁ ψ₂) (hw : w₁ ≠ 0 ∨ w₂ ≠ 0) :
    2 * (ψ₁ * w₁) = 1 ∨ 2 * (ψ₁ * w₁) = 1 + α ∨ 2 * (ψ₁ * w₁) = 2 - α ∨
      2 * (ψ₁ * w₁) = 2 := by
  have h1a := h3_one_add_ne_zero (R := ZMod p) hα
  have h2a := h3_two_sub_ne_zero (R := ZMod p) hα
  have h0S : (0 : ZMod p) ∉ ({1, 2, 1 + α, 2 - α} : Set (ZMod p)) := by
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or]
    exact ⟨fun hh => one_ne_zero hh.symm, fun hh => h3_two_ne_zero_of_sq hα hh.symm,
      fun hh => h1a hh.symm, fun hh => h2a hh.symm⟩
  have hne := coord_mul_ne_zero hp5 hα hc hw
  have hmem : 2 * (ψ₁ * w₁) ∈ ({1, 2, 1 + α, 2 - α} : Set (ZMod p)) := by
    rcases (two_mul_mem hα hc).1 with hz | hmem
    · exact absurd (by rw [hz.1, hz.2, mul_zero]) hne
    · exact hmem
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hmem
  rcases hmem with h | h | h | h
  · exact Or.inl h
  · exact Or.inr (Or.inr (Or.inr h))
  · exact Or.inr (Or.inl h)
  · exact Or.inr (Or.inr (Or.inl h))

private lemma h3_zmod_hb (hp5 : p ≠ 5) (hα : α ^ 2 = α + 1)
    (hc : H3EtaConstraints α w₁ w₂ ψ₁ ψ₂) (hw : w₁ ≠ 0 ∨ w₂ ≠ 0) :
    2 * (ψ₂ * w₂) = 1 ∨ 2 * (ψ₂ * w₂) = 2 ∨ 2 * (ψ₂ * w₂) = 1 + α ∨
      2 * (ψ₂ * w₂) = 2 - α := by
  have h1a := h3_one_add_ne_zero (R := ZMod p) hα
  have h2a := h3_two_sub_ne_zero (R := ZMod p) hα
  have h0S : (0 : ZMod p) ∉ ({1, 2, 1 + α, 2 - α} : Set (ZMod p)) := by
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or]
    exact ⟨fun hh => one_ne_zero hh.symm, fun hh => h3_two_ne_zero_of_sq hα hh.symm,
      fun hh => h1a hh.symm, fun hh => h2a hh.symm⟩
  have hne := h3_v_ne_zero hp5 hα hc hw
  have hmem : 2 * (ψ₂ * w₂) ∈ ({1, 2, 1 + α, 2 - α} : Set (ZMod p)) := by
    rcases (two_mul_mem hα hc).2 with hz | hmem
    · exact absurd (by rw [hz.1, hz.2, mul_zero]) hne
    · exact hmem
  simpa only [Set.mem_insert_iff, Set.mem_singleton_iff] using hmem

private lemma h3_zmod_hP1 (hp5 : p ≠ 5) (hα : α ^ 2 = α + 1)
    (hc : H3EtaConstraints α w₁ w₂ ψ₁ ψ₂) :
    (((1 + α) * (ψ₁ * w₁) + ψ₂ * w₂) / 2 +
        1 * (1 + α) * h3Cross α w₁ w₂ ψ₁ ψ₂ = 0 ∨
      ((1 + α) * (ψ₁ * w₁) + ψ₂ * w₂) / 2 +
        1 * (1 + α) * h3Cross α w₁ w₂ ψ₁ ψ₂ = 1 ∨
      ((1 + α) * (ψ₁ * w₁) + ψ₂ * w₂) / 2 +
        1 * (1 + α) * h3Cross α w₁ w₂ ψ₁ ψ₂ = 1 + α) ∧
    (((1 + α) * (ψ₁ * w₁) + ψ₂ * w₂) / 2 +
        (-1) * (1 + α) * h3Cross α w₁ w₂ ψ₁ ψ₂ = 0 ∨
      ((1 + α) * (ψ₁ * w₁) + ψ₂ * w₂) / 2 +
        (-1) * (1 + α) * h3Cross α w₁ w₂ ψ₁ ψ₂ = 1 ∨
      ((1 + α) * (ψ₁ * w₁) + ψ₂ * w₂) / 2 +
        (-1) * (1 + α) * h3Cross α w₁ w₂ ψ₁ ψ₂ = 1 + α) := by
  constructor
  · have h := family_one_mem hp5 hα hc (s := 1) (Or.inl rfl)
    simpa only [Set.mem_insert_iff, Set.mem_singleton_iff] using h
  · have h := family_one_mem hp5 hα hc (s := -1) (Or.inr rfl)
    simpa only [Set.mem_insert_iff, Set.mem_singleton_iff] using h

private lemma h3_zmod_rel (hα : α ^ 2 = α + 1) :
    (2 * (ψ₂ * w₂) =
        2 * ((((1 + α) * (ψ₁ * w₁) + ψ₂ * w₂) / 2 +
          1 * (1 + α) * h3Cross α w₁ w₂ ψ₁ ψ₂) +
          (((1 + α) * (ψ₁ * w₁) + ψ₂ * w₂) / 2 +
          (-1) * (1 + α) * h3Cross α w₁ w₂ ψ₁ ψ₂)) -
        (1 + α) * (2 * (ψ₁ * w₁))) ∧
    ((((1 + α) * (ψ₁ * w₁) + ψ₂ * w₂) / 2 +
        1 * (1 + α) * h3Cross α w₁ w₂ ψ₁ ψ₂) -
        (((1 + α) * (ψ₁ * w₁) + ψ₂ * w₂) / 2 +
        (-1) * (1 + α) * h3Cross α w₁ w₂ ψ₁ ψ₂) =
      2 * (1 + α) * h3Cross α w₁ w₂ ψ₁ ψ₂) := by
  have h2nz : (2 : ZMod p) ≠ 0 := h3_two_ne_zero_of_sq hα
  constructor
  · have hsum := h3_P1_sum h2nz α ψ₁ ψ₂ w₁ w₂ (h3Cross α w₁ w₂ ψ₁ ψ₂)
    rw [show (((1 + α) * (ψ₁ * w₁) + ψ₂ * w₂) / 2 +
          1 * (1 + α) * h3Cross α w₁ w₂ ψ₁ ψ₂) +
        (((1 + α) * (ψ₁ * w₁) + ψ₂ * w₂) / 2 +
        (-1) * (1 + α) * h3Cross α w₁ w₂ ψ₁ ψ₂) =
        (1 + α) * (ψ₁ * w₁) + ψ₂ * w₂ from hsum]
    ring
  · exact h3_P1_diff h2nz α ψ₁ ψ₂ w₁ w₂ (h3Cross α w₁ w₂ ψ₁ ψ₂)

private lemma h3_zmod_hP3p (hα : α ^ 2 = α + 1) (hc : H3EtaConstraints α w₁ w₂ ψ₁ ψ₂) :
    ((((1 + α) * (ψ₁ * w₁) + ψ₂ * w₂) / 2 +
        1 * (1 + α) * h3Cross α w₁ w₂ ψ₁ ψ₂) +
        α * (((1 + α) * (ψ₁ * w₁) + ψ₂ * w₂) / 2 +
        (-1) * (1 + α) * h3Cross α w₁ w₂ ψ₁ ψ₂) - α * (2 * (ψ₁ * w₁)) ∈
      ({0, 1, 2, 1 + α, 2 - α} : Set (ZMod p))) := by
  have h2nz : (2 : ZMod p) ≠ 0 := h3_two_ne_zero_of_sq hα
  have h := family_three_mem hα hc (s := 1) (Or.inl rfl)
  rwa [h3_P3p_form h2nz hα ψ₁ ψ₂ w₁ w₂ (h3Cross α w₁ w₂ ψ₁ ψ₂)] at h

private lemma h3_zmod_hP3m (hα : α ^ 2 = α + 1) (hc : H3EtaConstraints α w₁ w₂ ψ₁ ψ₂) :
    (α * (((1 + α) * (ψ₁ * w₁) + ψ₂ * w₂) / 2 +
        1 * (1 + α) * h3Cross α w₁ w₂ ψ₁ ψ₂) +
        (((1 + α) * (ψ₁ * w₁) + ψ₂ * w₂) / 2 +
        (-1) * (1 + α) * h3Cross α w₁ w₂ ψ₁ ψ₂) - α * (2 * (ψ₁ * w₁)) ∈
      ({0, 1, 2, 1 + α, 2 - α} : Set (ZMod p))) := by
  have h2nz : (2 : ZMod p) ≠ 0 := h3_two_ne_zero_of_sq hα
  have h := family_three_mem hα hc (s := -1) (Or.inr rfl)
  rw [show ((2 - α) * (ψ₁ * w₁) + (1 + α) * (ψ₂ * w₂)) / 2 -
      (-1) * α * h3Cross α w₁ w₂ ψ₁ ψ₂ =
      α * (((1 + α) * (ψ₁ * w₁) + ψ₂ * w₂) / 2 +
        1 * (1 + α) * h3Cross α w₁ w₂ ψ₁ ψ₂) +
        (((1 + α) * (ψ₁ * w₁) + ψ₂ * w₂) / 2 +
        (-1) * (1 + α) * h3Cross α w₁ w₂ ψ₁ ψ₂) - α * (2 * (ψ₁ * w₁)) from
    h3_P3m_form h2nz hα ψ₁ ψ₂ w₁ w₂ (h3Cross α w₁ w₂ ψ₁ ψ₂)] at h
  exact h

private lemma h3_zmod_hconv (hα : α ^ 2 = α + 1) :
    (h3Cross α w₁ w₂ ψ₁ ψ₂ = 1 / 2 ∨ h3Cross α w₁ w₂ ψ₁ ψ₂ = -1 / 2) →
      (h3Cross α w₁ w₂ ψ₁ ψ₂ = 1 / 2 ∨ h3Cross α w₁ w₂ ψ₁ ψ₂ = -(1 / 2)) := by
  have h2nz : (2 : ZMod p) ≠ 0 := h3_two_ne_zero_of_sq hα
  rintro (h | h)
  · exact Or.inl h
  · exact Or.inr (by rw [h]; exact h3_neg_one_div_two h2nz)

private lemma h3_classify_zmod (hp5 : p ≠ 5) (hα : α ^ 2 = α + 1)
    (hc : H3EtaConstraints α w₁ w₂ ψ₁ ψ₂) (hw : w₁ ≠ 0 ∨ w₂ ≠ 0) :
    (2 * (ψ₁ * w₁) = 2 - α ∧ 2 * (ψ₂ * w₂) = 1 ∧
        (h3Cross α w₁ w₂ ψ₁ ψ₂ = α / 2 - 1 ∨ h3Cross α w₁ w₂ ψ₁ ψ₂ = 1 - α / 2)) ∨
      (2 * (ψ₁ * w₁) = 1 + α ∧ 2 * (ψ₂ * w₂) = 2 - α ∧
        (h3Cross α w₁ w₂ ψ₁ ψ₂ = (1 - α) / 2 ∨ h3Cross α w₁ w₂ ψ₁ ψ₂ = (α - 1) / 2)) ∨
      (2 * (ψ₁ * w₁) = 1 ∧ 2 * (ψ₂ * w₂) = 1 + α ∧
        (h3Cross α w₁ w₂ ψ₁ ψ₂ = 1 / 2 ∨ h3Cross α w₁ w₂ ψ₁ ψ₂ = -(1 / 2))) ∨
      (2 * (ψ₁ * w₁) = 2 ∧ 2 * (ψ₂ * w₂) = 2)
:= by
  have hp7 : 7 < p := seven_lt_of_sq_eq_add_one hp5 hα
  have h2nz : (2 : ZMod p) ≠ 0 := h3_two_ne_zero hp7
  have h4nz : (4 : ZMod p) ≠ 0 := h3_four_ne_zero hp7
  have h5nz : (5 : ZMod p) ≠ 0 := h3_five_ne_zero hp7
  have h9nz : (9 : ZMod p) ≠ 0 := h3_nine_ne_zero hp7
  have h1a := h3_one_add_ne_zero (R := ZMod p) hα
  have h2a := h3_two_sub_ne_zero (R := ZMod p) hα
  obtain ⟨hpp, hpm⟩ := h3_zmod_hP1 (α := α) (w₁ := w₁) (w₂ := w₂) (ψ₁ := ψ₁) (ψ₂ := ψ₂) hp5 hα hc
  obtain ⟨hbsum, hCsum⟩ := h3_zmod_rel (α := α) (w₁ := w₁) (w₂ := w₂) (ψ₁ := ψ₁) (ψ₂ := ψ₂) hα
  have hP3p := h3_zmod_hP3p (α := α) (w₁ := w₁) (w₂ := w₂) (ψ₁ := ψ₁) (ψ₂ := ψ₂) hα hc
  have hP3m := h3_zmod_hP3m (α := α) (w₁ := w₁) (w₂ := w₂) (ψ₁ := ψ₁) (ψ₂ := ψ₂) hα hc
  have ha := h3_zmod_ha (α := α) (w₁ := w₁) (w₂ := w₂) (ψ₁ := ψ₁) (ψ₂ := ψ₂) hp5 hα hc hw
  have hb := h3_zmod_hb (α := α) (w₁ := w₁) (w₂ := w₂) (ψ₁ := ψ₁) (ψ₂ := ψ₂) hp5 hα hc hw
  have hzero := h3_zmod_zero_pair (α := α) (w₁ := w₁) (w₂ := w₂) (ψ₁ := ψ₁) (ψ₂ := ψ₂) hα hc
  have hP3zero := h3_zmod_P3_zero_pair (α := α) (w₁ := w₁) (w₂ := w₂) (ψ₁ := ψ₁) (ψ₂ := ψ₂) hα hc
  have hconv := h3_zmod_hconv (α := α) (w₁ := w₁) (w₂ := w₂) (ψ₁ := ψ₁) (ψ₂ := ψ₂) hα
  rcases h3_classify_alg hα h2nz h4nz h5nz h9nz h1a h2a ha hb hpp hpm hbsum hCsum hP3p hP3m
      hzero hP3zero with hA | hB | hC | hD
  · exact Or.inl hA
  · exact Or.inr (Or.inl hB)
  · exact Or.inr (Or.inr (Or.inl ⟨hC.1, hC.2.1, hconv hC.2.2⟩))
  · exact Or.inr (Or.inr (Or.inr hD))

theorem classify (hp5 : p ≠ 5) (hα : α ^ 2 = α + 1) (hc : H3EtaConstraints α w₁ w₂ ψ₁ ψ₂)
    (hw : w₁ ≠ 0 ∨ w₂ ≠ 0) (h2 : ψ₁ * w₁ + ψ₂ * w₂ ≠ 2) :
    (2 * (ψ₁ * w₁) = 2 - α ∧ 2 * (ψ₂ * w₂) = 1 ∧
        (h3Cross α w₁ w₂ ψ₁ ψ₂ = α / 2 - 1 ∨ h3Cross α w₁ w₂ ψ₁ ψ₂ = 1 - α / 2)) ∨
      (2 * (ψ₁ * w₁) = 1 + α ∧ 2 * (ψ₂ * w₂) = 2 - α ∧
        (h3Cross α w₁ w₂ ψ₁ ψ₂ = (1 - α) / 2 ∨ h3Cross α w₁ w₂ ψ₁ ψ₂ = (α - 1) / 2)) ∨
      (2 * (ψ₁ * w₁) = 1 ∧ 2 * (ψ₂ * w₂) = 1 + α ∧
        (h3Cross α w₁ w₂ ψ₁ ψ₂ = 1 / 2 ∨ h3Cross α w₁ w₂ ψ₁ ψ₂ = -(1 / 2))) := by
  have hp7 : 7 < p := seven_lt_of_sq_eq_add_one hp5 hα
  rcases h3_classify_zmod hp5 hα hc hw with
    ⟨h1, h2', h3⟩ | ⟨h1, h2', h3⟩ | ⟨h1, h2', h3⟩ | ⟨h1, h2'⟩
  · exact Or.inl ⟨h1, h2', h3⟩
  · exact Or.inr (Or.inl ⟨h1, h2', h3⟩)
  · exact Or.inr (Or.inr ⟨h1, h2', h3⟩)
  · exfalso
    have hsum : 2 * (ψ₁ * w₁ + ψ₂ * w₂) = 4 := by
      rw [show 2 * (ψ₁ * w₁ + ψ₂ * w₂) = 2 * (ψ₁ * w₁) + 2 * (ψ₂ * w₂) by ring, h1, h2']
      ring
    exact h2 (mul_left_cancel₀ (h3_two_ne_zero hp7) (by rw [hsum]; ring))

end H3EtaConstraints

variable {α w₁ w₂ ψ₁ ψ₂ : ZMod p}

theorem h3Cross_eq (hα : α ^ 2 = α + 1)
    (h : ψ₁ * w₁ * (ψ₂ * w₂) = (1 + α) * h3Cross α w₁ w₂ ψ₁ ψ₂ ^ 2) :
    ψ₁ * w₂ = (1 + α) * h3Cross α w₁ w₂ ψ₁ ψ₂ ∧ ψ₂ * w₁ = h3Cross α w₁ w₂ ψ₁ ψ₂ := by
  have h1a := h3_one_add_ne_zero (R := ZMod p) hα
  have h2nz := h3_two_ne_zero_of_sq hα
  have hD : 2 * h3Cross α w₁ w₂ ψ₁ ψ₂ = (2 - α) * (ψ₁ * w₂) + ψ₂ * w₁ := by
    simp only [h3Cross]
    rw [mul_div_cancel₀ _ h2nz]
    ring
  have h4 : 4 * (ψ₁ * w₂) * (ψ₂ * w₁) =
      (1 + α) * (2 * h3Cross α w₁ w₂ ψ₁ ψ₂) ^ 2 := by
    rw [show 4 * (ψ₁ * w₂) * (ψ₂ * w₁) = 4 * (ψ₁ * w₁ * (ψ₂ * w₂)) by ring, h]
    ring
  exact h3Cross_eq_alg hα h1a h2nz hD h4

end CFSG.StandardType.ZS

end
