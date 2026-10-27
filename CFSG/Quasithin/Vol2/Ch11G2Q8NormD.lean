module

public import CFSG.Quasithin.Vol2.Ch11G2Q8Borel

public section

namespace CFSG.Quasithin.Vol2.Ch11.G2Q8

open CFSG.Open CFSG.Quasithin CFSG.Quasithin.Explicit CFSG.Quasithin.JonesParshall
  CFSG.Quasithin.Vol2.KGNat Matrix

variable {F : Type} [Field F] [CharP F 2]

theorem exists_cgE_zI (γ : ↥(cayleyGroup F)) {w : Ix3 → F} {a b c d e f : F}
    (h : g2Act γ w = q6 a b c d e f) : ∃ r : F, cgE γ (zI w) = zmk r a b c d e f r := by
  refine ⟨(cgE γ (zI w)).1, ?_⟩
  conv_lhs => rw [g2_zI_eq γ w]
  rw [h, zI_q6, cayleyOne_eq, zmk_smul, zmk_add]
  apply zmk_congr <;> ring

omit [CharP F 2] in
theorem zI_mul_u1_u2 :
    cayleyMul (zI (q6 (0 : F) 1 0 0 0 0)) (zI (q6 0 0 1 0 0 0)) = zI (q6 0 0 0 1 0 0) := by
  rw [zI_q6, zI_q6, zI_q6, cayleyMul_zmk]
  apply zmk_congr <;> ring

omit [CharP F 2] in
theorem zI_mul_u2_u0 :
    cayleyMul (zI (q6 (0 : F) 0 1 0 0 0)) (zI (q6 1 0 0 0 0 0)) = zI (q6 0 0 0 0 1 0) := by
  rw [zI_q6, zI_q6, zI_q6, cayleyMul_zmk]
  apply zmk_congr <;> ring

theorem shape_x0 {γ : ↥(cayleyGroup F)} {l m n : F}
    (h : ∀ a b c d e f : F,
      g2Act γ (q6 a b c d e f) = q6 (a + l * d) b c d (e + m * c) (f + n * b)) :
    l = m * m ∧ m = n := by
  have h2 : (2 : F) = 0 := CharTwo.two_eq_zero
  obtain ⟨r₁, e1⟩ := exists_cgE_zI γ (h 0 1 0 0 0 0)
  obtain ⟨r₂, e2⟩ := exists_cgE_zI γ (h 0 0 1 0 0 0)
  obtain ⟨r₃, e3⟩ := exists_cgE_zI γ (h 0 0 0 1 0 0)
  have hm := cg_mul γ (zI (q6 0 1 0 0 0 0)) (zI (q6 0 0 1 0 0 0))
  rw [zI_mul_u1_u2, e1, e2, e3, cayleyMul_zmk] at hm
  obtain ⟨k1, k2, -, -, -, -, -, k8⟩ := zmk_inj hm
  have hmn : m = n := by linear_combination k8 - k1
  exact ⟨by linear_combination k2 + m * hmn - m * m * h2, hmn⟩

theorem shape_x1 {γ : ↥(cayleyGroup F)} {l m n : F}
    (h : ∀ a b c d e f : F,
      g2Act γ (q6 a b c d e f) = q6 a (b + l * e) c (d + n * c) e (f + m * a)) :
    l = m * m ∧ m = n := by
  have h2 : (2 : F) = 0 := CharTwo.two_eq_zero
  obtain ⟨r₁, e1⟩ := exists_cgE_zI γ (h 0 0 1 0 0 0)
  obtain ⟨r₂, e2⟩ := exists_cgE_zI γ (h 1 0 0 0 0 0)
  obtain ⟨r₃, e3⟩ := exists_cgE_zI γ (h 0 0 0 0 1 0)
  have hm := cg_mul γ (zI (q6 0 0 1 0 0 0)) (zI (q6 1 0 0 0 0 0))
  rw [zI_mul_u2_u0, e1, e2, e3, cayleyMul_zmk] at hm
  obtain ⟨k1, -, k3, -, -, -, -, k8⟩ := zmk_inj hm
  have hmn : m = n := by linear_combination k8 - k1
  exact ⟨by linear_combination k3 + m * hmn - m * m * h2, hmn⟩

theorem g2Act_g2T_q6 (s : Fˣ × Fˣ) (a b c d e f : F) :
    g2Act (g2T s) (q6 a b c d e f) = q6 ((s.1 : F) * a) ((s.2 : F) * b)
      (((s.1 : F) * s.2)⁻¹ * c) ((s.1 : F)⁻¹ * d) ((s.2 : F)⁻¹ * e) ((s.1 : F) * s.2 * f) := by
  rw [g2Act_g2T]
  rfl

omit [CharP F 2] in
theorem smul_q6 (t a b c d e f : F) :
    t • q6 a b c d e f = q6 (t * a) (t * b) (t * c) (t * d) (t * e) (t * f) := by
  funext j
  rcases j with j | j <;> fin_cases j <;> rfl

@[expose] def diagQ (δ : Ix3 → F) (w : Ix3 → F) : Ix3 → F := fun j => δ j * w j

omit [CharP F 2] in
theorem diagQ_q6 (δ : Ix3 → F) (a b c d e f : F) :
    diagQ δ (q6 a b c d e f) = q6 (δ (.inl 0) * a) (δ (.inl 1) * b) (δ (.inl 2) * c)
      (δ (.inr 0) * d) (δ (.inr 1) * e) (δ (.inr 2) * f) := by
  funext j
  rcases j with j | j <;> fin_cases j <;> rfl

omit [CharP F 2] in
theorem diagQ_inv_q6 {δ : Ix3 → F} (hδ : ∀ j, δ j ≠ 0) (a b c d e f : F) :
    diagQ δ (q6 (a / δ (.inl 0)) (b / δ (.inl 1)) (c / δ (.inl 2)) (d / δ (.inr 0))
      (e / δ (.inr 1)) (f / δ (.inr 2))) = q6 a b c d e f := by
  rw [diagQ_q6]
  refine q6_congr ?_ ?_ ?_ ?_ ?_ ?_ <;> field_simp [hδ]

theorem exists_eq_smul_g2T_of_diag [Finite F] {δ : Ix3 → F} (hδ : ∀ j, δ j ≠ 0)
    {γ₀ γ₁ : ↥(cayleyGroup F)}
    (h0 : ∀ w, diagQ δ (g2Act (g2X ![1, 0, 0]) w) = g2Act γ₀ (diagQ δ w))
    (h1 : ∀ w, diagQ δ (g2Act (g2X ![0, 1, 0]) w) = g2Act γ₁ (diagQ δ w)) :
    ∃ (c : F) (s : Fˣ × Fˣ), c ≠ 0 ∧ ∀ w, diagQ δ w = c • g2Act (g2T s) w := by
  have h2 : (2 : F) = 0 := CharTwo.two_eq_zero
  have ha0 := hδ (.inl 0)
  have ha1 := hδ (.inl 1)
  have ha2 := hδ (.inl 2)
  have hb0 := hδ (.inr 0)
  have hb1 := hδ (.inr 1)
  have hb2 := hδ (.inr 2)
  have hγ₀ : ∀ a b c d e f : F, g2Act γ₀ (q6 a b c d e f) =
      q6 (a + δ (.inl 0) / δ (.inr 0) * d) b c d (e + δ (.inr 1) / δ (.inl 2) * c)
        (f + δ (.inr 2) / δ (.inl 1) * b) := by
    intro a b c d e f
    have he := h0 (q6 (a / δ (.inl 0)) (b / δ (.inl 1)) (c / δ (.inl 2)) (d / δ (.inr 0))
      (e / δ (.inr 1)) (f / δ (.inr 2)))
    rw [diagQ_inv_q6 hδ, g2Act_x0q, diagQ_q6] at he
    rw [← he]
    refine q6_congr ?_ ?_ ?_ ?_ ?_ ?_ <;> field_simp
  have hγ₁ : ∀ a b c d e f : F, g2Act γ₁ (q6 a b c d e f) =
      q6 a (b + δ (.inl 1) / δ (.inr 1) * e) c (d + δ (.inr 0) / δ (.inl 2) * c) e
        (f + δ (.inr 2) / δ (.inl 0) * a) := by
    intro a b c d e f
    have he := h1 (q6 (a / δ (.inl 0)) (b / δ (.inl 1)) (c / δ (.inl 2)) (d / δ (.inr 0))
      (e / δ (.inr 1)) (f / δ (.inr 2)))
    rw [diagQ_inv_q6 hδ, g2Act_x1q, diagQ_q6] at he
    rw [← he]
    refine q6_congr ?_ ?_ ?_ ?_ ?_ ?_ <;> field_simp
  obtain ⟨e1, e2⟩ := shape_x0 hγ₀
  obtain ⟨-, e4⟩ := shape_x1 hγ₁
  have R1 : δ (.inl 0) * δ (.inl 2) ^ 2 = δ (.inr 0) * δ (.inr 1) ^ 2 := by
    field_simp at e1
    linear_combination e1
  have R2 : δ (.inl 1) * δ (.inr 1) = δ (.inl 2) * δ (.inr 2) := by
    field_simp at e2
    linear_combination e2
  have R4 : δ (.inl 2) * δ (.inr 2) = δ (.inl 0) * δ (.inr 0) := by
    field_simp at e4
    linear_combination e4
  obtain ⟨c, hc⟩ := isSquare_of_charTwo' (δ (.inl 0) * δ (.inr 0))
  have hc0 : c ≠ 0 := by
    rintro rfl
    rw [mul_zero] at hc
    exact mul_ne_zero ha0 hb0 hc
  have hsq : (δ (.inl 0) * δ (.inl 1) * δ (.inl 2)) ^ 2 * δ (.inr 1) ^ 2 =
      (c ^ 3) ^ 2 * δ (.inr 1) ^ 2 := by
    have hc6 : (c ^ 3) ^ 2 = (δ (.inl 0) * δ (.inr 0)) ^ 3 := by rw [hc]; ring
    rw [hc6]
    linear_combination δ (.inl 0) ^ 2 * δ (.inl 2) ^ 2 *
        (δ (.inl 1) * δ (.inr 1) + δ (.inl 2) * δ (.inr 2)) * R2 +
      δ (.inl 0) ^ 2 * δ (.inl 2) ^ 2 * (δ (.inl 2) * δ (.inr 2) + δ (.inl 0) * δ (.inr 0)) * R4 +
      δ (.inl 0) ^ 3 * δ (.inr 0) ^ 2 * R1
  have hsq' := mul_right_cancel₀ (pow_ne_zero 2 hb1) hsq
  have h3 : δ (.inl 0) * δ (.inl 1) * δ (.inl 2) = c ^ 3 := by
    have hz : (δ (.inl 0) * δ (.inl 1) * δ (.inl 2) - c ^ 3) ^ 2 = 0 := by
      linear_combination hsq' + ((c ^ 3) ^ 2 - δ (.inl 0) * δ (.inl 1) * δ (.inl 2) * c ^ 3) * h2
    exact sub_eq_zero.mp (pow_eq_zero_iff two_ne_zero |>.mp hz)
  have h5 : c * δ (.inr 2) = δ (.inl 0) * δ (.inl 1) := by
    have h6 : δ (.inl 2) * (c * δ (.inr 2)) = δ (.inl 2) * (δ (.inl 0) * δ (.inl 1)) := by
      linear_combination c * R4 + c * hc - h3
    exact mul_left_cancel₀ ha2 h6
  have k2 : c * (δ (.inl 0) / c * (δ (.inl 1) / c))⁻¹ = δ (.inl 2) := by
    field_simp
    linear_combination -h3
  have k3 : c * (δ (.inl 0) / c)⁻¹ = δ (.inr 0) := by
    field_simp
    linear_combination -hc
  have k4 : c * (δ (.inl 1) / c)⁻¹ = δ (.inr 1) := by
    field_simp
    linear_combination -(hc + R2 + R4)
  have k5 : c * (δ (.inl 0) / c * (δ (.inl 1) / c)) = δ (.inr 2) := by
    field_simp
    linear_combination -h5
  refine ⟨c, (Units.mk0 (δ (.inl 0) / c) (div_ne_zero ha0 hc0),
    Units.mk0 (δ (.inl 1) / c) (div_ne_zero ha1 hc0)), hc0, fun w => ?_⟩
  rw [q6_eta w, diagQ_q6, g2Act_g2T_q6, smul_q6]
  simp only [Units.val_mk0]
  refine q6_congr ?_ ?_ ?_ ?_ ?_ ?_
  · field_simp
  · field_simp
  · rw [← mul_assoc, k2]
  · rw [← mul_assoc, k3]
  · rw [← mul_assoc, k4]
  · rw [← mul_assoc, k5]

end CFSG.Quasithin.Vol2.Ch11.G2Q8
