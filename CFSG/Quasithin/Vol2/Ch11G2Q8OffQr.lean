module

public import CFSG.Quasithin.Vol2.Ch11G2Q8InvLong

public section

namespace CFSG.Quasithin.Vol2.Ch11.G2Q8

open CFSG.Open CFSG.Quasithin CFSG.Quasithin.Explicit CFSG.Quasithin.JonesParshall
  CFSG.Quasithin.Vol2.KGNat Matrix
open CFSG.ClassicalInvolution.ModelFacts.OddCover (uSL)

variable {F : Type} [Field F] [CharP F 2]

omit [CharP F 2] in
theorem polarQ_symm (x y : Ix3 → F) : polarQ x y = polarQ y x := by
  simp only [polarQ]
  ring

omit [CharP F 2] in
theorem polarQ_add_left (x x' y : Ix3 → F) : polarQ (x + x') y = polarQ x y + polarQ x' y := by
  simp only [polarQ, Pi.add_apply]
  ring

omit [CharP F 2] in
theorem polarQ_add_right (x y y' : Ix3 → F) : polarQ x (y + y') = polarQ x y + polarQ x y' := by
  simp only [polarQ, Pi.add_apply]
  ring

omit [CharP F 2] in
theorem polarQ_smul_left (c : F) (x y : Ix3 → F) : polarQ (c • x) y = c * polarQ x y := by
  simp only [polarQ, Pi.smul_apply, smul_eq_mul]
  ring

omit [CharP F 2] in
theorem polarQ_smul_right (c : F) (x y : Ix3 → F) : polarQ x (c • y) = c * polarQ x y := by
  simp only [polarQ, Pi.smul_apply, smul_eq_mul]
  ring

omit [CharP F 2] in
theorem polarQ_eu0 (x : Ix3 → F) : polarQ (eu 0 1) x = x (.inr 0) := by
  simp [polarQ]

theorem mul_self_add_charTwo (a b : F) : (a + b) * (a + b) = a * a + b * b := by
  have h2 : (2 : F) = 0 := CharTwo.two_eq_zero
  linear_combination a * b * h2

theorem eq_of_mul_self_eq_charTwo {a b : F} (h : a * a = b * b) : a = b := by
  have h1 : (a + b) * (a + b) = 0 := by rw [mul_self_add_charTwo, h, CharTwo.add_self_eq_zero]
  rw [mul_self_eq_zero] at h1
  exact (CharTwo.add_eq_zero).mp h1

omit [CharP F 2] in
theorem q6_eq_sum (a b c d e f : F) :
    q6 a b c d e f = a • q6 1 0 0 0 0 0 + b • q6 0 1 0 0 0 0 + c • q6 0 0 1 0 0 0 +
      d • q6 0 0 0 1 0 0 + e • q6 0 0 0 0 1 0 + f • q6 0 0 0 0 0 1 := by
  funext j
  rcases j with j | j <;> fin_cases j <;> simp [q6]

@[expose] def qr (r : ↥(cayleyGroup F)) (x : Ix3 → F) : F := polarQ x (g2Act r x)

theorem qr_add {r : ↥(cayleyGroup F)} (hr : r * r = 1) (x y : Ix3 → F) :
    qr r (x + y) = qr r x + qr r y := by
  have h2 : (2 : F) = 0 := CharTwo.two_eq_zero
  have hxy : polarQ y (g2Act r x) = polarQ x (g2Act r y) := by
    rw [← polarQ_g2Act r y (g2Act r x), ← g2Act_mul_apply, hr, map_one, polarQ_symm]
    rfl
  simp only [qr]
  rw [map_add, polarQ_add_left, polarQ_add_right, polarQ_add_right, hxy]
  linear_combination polarQ x (g2Act r y) * h2

theorem qr_smul (r : ↥(cayleyGroup F)) (c : F) (x : Ix3 → F) :
    qr r (c • x) = c * c * qr r x := by
  simp only [qr]
  rw [g2Act_smul, polarQ_smul_left, polarQ_smul_right]
  ring

theorem qr_q6 {r : ↥(cayleyGroup F)} (hr : r * r = 1) (a b c d e f : F) :
    qr r (q6 a b c d e f) = a * a * qr r (q6 1 0 0 0 0 0) + b * b * qr r (q6 0 1 0 0 0 0) +
      c * c * qr r (q6 0 0 1 0 0 0) + d * d * qr r (q6 0 0 0 1 0 0) +
      e * e * qr r (q6 0 0 0 0 1 0) + f * f * qr r (q6 0 0 0 0 0 1) := by
  rw [q6_eq_sum]
  simp only [qr_add hr, qr_smul]

theorem qr_conj (g r : ↥(cayleyGroup F)) (x : Ix3 → F) :
    qr (g * r * g⁻¹) (g2Act g x) = qr r x := by
  simp only [qr]
  rw [g2Act_mul_apply, g2Act_mul_apply, g2Act_inv_apply, polarQ_g2Act]

theorem qr_of_comm {r s : ↥(cayleyGroup F)} (hs : s * r = r * s) (x : Ix3 → F) :
    qr r (g2Act s x) = qr r x := by
  simp only [qr]
  rw [← g2Act_mul_apply, ← hs, g2Act_mul_apply, polarQ_g2Act]

theorem exists_qr_eq_sq [Finite F] {r : ↥(cayleyGroup F)} (hr : r * r = 1) :
    ∃ p : Ix3 → F, ∀ x, qr r x = polarQ p x * polarQ p x := by
  have h2 : (2 : F) = 0 := CharTwo.two_eq_zero
  obtain ⟨s₀, h₀⟩ := isSquare_of_charTwo' (qr r (q6 1 0 0 0 0 0))
  obtain ⟨s₁, h₁⟩ := isSquare_of_charTwo' (qr r (q6 0 1 0 0 0 0))
  obtain ⟨s₂, h₂⟩ := isSquare_of_charTwo' (qr r (q6 0 0 1 0 0 0))
  obtain ⟨s₃, h₃⟩ := isSquare_of_charTwo' (qr r (q6 0 0 0 1 0 0))
  obtain ⟨s₄, h₄⟩ := isSquare_of_charTwo' (qr r (q6 0 0 0 0 1 0))
  obtain ⟨s₅, h₅⟩ := isSquare_of_charTwo' (qr r (q6 0 0 0 0 0 1))
  refine ⟨q6 s₃ s₄ s₅ s₀ s₁ s₂, fun x => ?_⟩
  rw [q6_eta x, qr_q6 hr, h₀, h₁, h₂, h₃, h₄, h₅]
  simp only [polarQ, q6_apply_inl0, q6_apply_inl1, q6_apply_inl2, q6_apply_inr0, q6_apply_inr1,
    q6_apply_inr2]
  linear_combination (-(s₃ * x (.inr 0) * (x (.inl 0) * s₀) + s₃ * x (.inr 0) * (s₄ * x (.inr 1)) +
    s₃ * x (.inr 0) * (x (.inl 1) * s₁) + s₃ * x (.inr 0) * (s₅ * x (.inr 2)) +
    s₃ * x (.inr 0) * (x (.inl 2) * s₂) + x (.inl 0) * s₀ * (s₄ * x (.inr 1)) +
    x (.inl 0) * s₀ * (x (.inl 1) * s₁) + x (.inl 0) * s₀ * (s₅ * x (.inr 2)) +
    x (.inl 0) * s₀ * (x (.inl 2) * s₂) + s₄ * x (.inr 1) * (x (.inl 1) * s₁) +
    s₄ * x (.inr 1) * (s₅ * x (.inr 2)) + s₄ * x (.inr 1) * (x (.inl 2) * s₂) +
    x (.inl 1) * s₁ * (s₅ * x (.inr 2)) + x (.inl 1) * s₁ * (x (.inl 2) * s₂) +
    s₅ * x (.inr 2) * (x (.inl 2) * s₂))) * h2

theorem fix_of_qr_sq {r s : ↥(cayleyGroup F)} {p : Ix3 → F}
    (hp : ∀ x, qr r x = polarQ p x * polarQ p x) (hs : s * r = r * s) : g2Act s p = p := by
  have h1 : ∀ x, polarQ p (g2Act s x) = polarQ p x := fun x =>
    eq_of_mul_self_eq_charTwo (by rw [← hp, ← hp, qr_of_comm hs])
  have h3 : g2Act s p - p = 0 := eq_zero_of_polarQ fun y => by
    rw [polarQ_sub_left, ← polarQ_g2Act s⁻¹, g2Act_inv_apply, ← h1 (g2Act s⁻¹ y),
      g2Act_apply_inv, sub_self]
  exact sub_eq_zero.mp h3

theorem g2Act_g2A_e0 {A : SL3 F} (hA : (A : Matrix (Fin 3) (Fin 3) F) *ᵥ ![1, 0, 0] = ![1, 0, 0])
    (a b c d e f : F) :
    g2Act (g2A A) (q6 a b c d e f) =
      q6 (a + (A : Matrix (Fin 3) (Fin 3) F) 0 1 * b + (A : Matrix (Fin 3) (Fin 3) F) 0 2 * c)
        ((A : Matrix (Fin 3) (Fin 3) F) 1 1 * b + (A : Matrix (Fin 3) (Fin 3) F) 1 2 * c)
        ((A : Matrix (Fin 3) (Fin 3) F) 2 1 * b + (A : Matrix (Fin 3) (Fin 3) F) 2 2 * c) d
        (((A : Matrix (Fin 3) (Fin 3) F) 0 1 * (A : Matrix (Fin 3) (Fin 3) F) 2 2 +
            (A : Matrix (Fin 3) (Fin 3) F) 0 2 * (A : Matrix (Fin 3) (Fin 3) F) 2 1) * d +
          (A : Matrix (Fin 3) (Fin 3) F) 2 2 * e + (A : Matrix (Fin 3) (Fin 3) F) 2 1 * f)
        (((A : Matrix (Fin 3) (Fin 3) F) 0 1 * (A : Matrix (Fin 3) (Fin 3) F) 1 2 +
            (A : Matrix (Fin 3) (Fin 3) F) 0 2 * (A : Matrix (Fin 3) (Fin 3) F) 1 1) * d +
          (A : Matrix (Fin 3) (Fin 3) F) 1 2 * e + (A : Matrix (Fin 3) (Fin 3) F) 1 1 * f) := by
  obtain ⟨a0, a1, a2⟩ := adj_col0 hA
  have hdet := det_block_of_fix hA
  rw [g2Act_g2A]
  refine q6_congr ?_ ?_ ?_ ?_ ?_ ?_ <;> simp [adjugate_fin_three, a0, a1, a2, CharTwo.neg_eq]
  · rw [hdet, one_mul]
  · exact Or.inl (CharTwo.sub_eq_add _ _)

theorem eq_kerElt_of_qr {r : ↥(cayleyGroup F)} (hr : r * r = 1)
    (hq : ∀ x, qr r x = x (.inr 0) * x (.inr 0)) :
    ∃ a b : F, r = g2X ![1, 0, 0] * g2Y ![0, 0, 0] * g2A (uSL a b 0) := by
  have h2 : (2 : F) = 0 := CharTwo.two_eq_zero
  have hS : r ∈ stabV0 F :=
    fix_of_qr_sq (p := eu 0 1) (fun x => by rw [hq, polarQ_eu0]) rfl
  obtain ⟨α, β, γ, A, hA, rfl⟩ := exists_eq_of_mem_stabV0 hS
  have hrr : ∀ w, g2Act (g2X ![α, 0, 0] * g2Y ![0, β, γ] * g2A A)
      (g2Act (g2X ![α, 0, 0] * g2Y ![0, β, γ] * g2A A) w) = w := fun w => by
    rw [← g2Act_mul_apply, hr, map_one]
    rfl
  obtain ⟨a0, a1, a2⟩ := adj_col0 hA
  have hdet := det_block_of_fix hA
  have hgA := g2Act_g2A_e0 hA
  obtain ⟨A01, h01⟩ : ∃ t, (A : Matrix (Fin 3) (Fin 3) F) 0 1 = t := ⟨_, rfl⟩
  obtain ⟨A02, h02⟩ : ∃ t, (A : Matrix (Fin 3) (Fin 3) F) 0 2 = t := ⟨_, rfl⟩
  obtain ⟨A11, h11⟩ : ∃ t, (A : Matrix (Fin 3) (Fin 3) F) 1 1 = t := ⟨_, rfl⟩
  obtain ⟨A12, h12⟩ : ∃ t, (A : Matrix (Fin 3) (Fin 3) F) 1 2 = t := ⟨_, rfl⟩
  obtain ⟨A21, h21⟩ : ∃ t, (A : Matrix (Fin 3) (Fin 3) F) 2 1 = t := ⟨_, rfl⟩
  obtain ⟨A22, h22⟩ : ∃ t, (A : Matrix (Fin 3) (Fin 3) F) 2 2 = t := ⟨_, rfl⟩
  simp only [h01, h02, h11, h12, h21, h22] at hgA hdet
  have hact : ∀ a b c d e f : F, g2Act (g2X ![α, 0, 0] * g2Y ![0, β, γ] * g2A A)
      (q6 a b c d e f) = q6
        ((a + A01 * b + A02 * c) + β * ((A01 * A12 + A02 * A11) * d + A12 * e + A11 * f) +
          γ * ((A01 * A22 + A02 * A21) * d + A22 * e + A21 * f) + α * α * d)
        ((A11 * b + A12 * c) + γ * d) ((A21 * b + A22 * c) + β * d) d
        (((A01 * A22 + A02 * A21) * d + A22 * e + A21 * f) +
          (β * (A11 * b + A12 * c) + γ * (A21 * b + A22 * c)) * β +
          α * ((A21 * b + A22 * c) + β * d))
        (((A01 * A12 + A02 * A11) * d + A12 * e + A11 * f) +
          (β * (A11 * b + A12 * c) + γ * (A21 * b + A22 * c)) * γ +
          α * ((A11 * b + A12 * c) + γ * d)) := by
    intro a b c d e f
    rw [g2Act_mul_apply, g2Act_mul_apply, hgA, g2Act_y12q, g2Act_x0q]
  have q1 : (β * A11 + γ * A21) * β + α * A21 = 0 := by
    have := hq (q6 0 1 0 0 0 0)
    simp only [qr, hact, polarQ, q6_apply_inl0, q6_apply_inl1, q6_apply_inl2, q6_apply_inr0,
      q6_apply_inr1, q6_apply_inr2] at this
    linear_combination this
  have q2 : (β * A12 + γ * A22) * γ + α * A12 = 0 := by
    have := hq (q6 0 0 1 0 0 0)
    simp only [qr, hact, polarQ, q6_apply_inl0, q6_apply_inl1, q6_apply_inl2, q6_apply_inr0,
      q6_apply_inr1, q6_apply_inr2] at this
    linear_combination this
  have q3 : β * (A01 * A12 + A02 * A11) + γ * (A01 * A22 + A02 * A21) + α * α = 1 := by
    have := hq (q6 0 0 0 1 0 0)
    simp only [qr, hact, polarQ, q6_apply_inl0, q6_apply_inl1, q6_apply_inl2, q6_apply_inr0,
      q6_apply_inr1, q6_apply_inr2] at this
    linear_combination this
  have rv0 := hrr (q6 0 0 0 1 0 0)
  rw [hact, hact] at rv0
  obtain ⟨-, r1, r2, -, -, -⟩ := q6_inj rv0
  have ru1 := hrr (q6 0 1 0 0 0 0)
  rw [hact, hact] at ru1
  obtain ⟨r3, r4, -, -, -, -⟩ := q6_inj ru1
  have ru2 := hrr (q6 0 0 1 0 0 0)
  rw [hact, hact] at ru2
  obtain ⟨r5, -, r6, -, -, -⟩ := q6_inj ru2
  clear hact hrr rv0 ru1 ru2 hgA hq
  have r1' : A11 * γ + A12 * β + γ = 0 := by linear_combination r1
  have r2' : A21 * γ + A22 * β + β = 0 := by linear_combination r2
  have r4' : A11 * A11 + A12 * A21 = 1 := by linear_combination r4
  have r6' : A21 * A12 + A22 * A22 = 1 := by linear_combination r6
  have r3' : A01 + A01 * A11 + A02 * A21 +
      β * (A12 * ((β * A11 + γ * A21) * β + α * A21) +
        A11 * ((β * A11 + γ * A21) * γ + α * A11)) +
      γ * (A22 * ((β * A11 + γ * A21) * β + α * A21) +
        A21 * ((β * A11 + γ * A21) * γ + α * A11)) = 0 := by linear_combination r3
  have r5' : A02 + A01 * A12 + A02 * A22 +
      β * (A12 * ((β * A12 + γ * A22) * β + α * A22) +
        A11 * ((β * A12 + γ * A22) * γ + α * A12)) +
      γ * (A22 * ((β * A12 + γ * A22) * β + α * A22) +
        A21 * ((β * A12 + γ * A22) * γ + α * A12)) = 0 := by linear_combination r5
  clear r1 r2 r3 r4 r5 r6
  have hm : A11 = A22 := eq_of_mul_self_eq_charTwo (by linear_combination r4' - r6')
  have hs1 : β * A11 + γ * A21 = β := by linear_combination r2' + β * hm - β * h2
  have hs2 : β * A12 + γ * A22 = γ := by linear_combination r1' - γ * hm - γ * h2
  have hq1' : β * β + α * A21 = 0 := by linear_combination q1 - β * hs1
  have hq2' : γ * γ + α * A12 = 0 := by linear_combination q2 - γ * hs2
  have hq3' : A01 * γ + A02 * β + α * α = 1 := by linear_combination q3 - A01 * hs2 - A02 * hs1
  have r3'' : A01 * (1 + A11) + A02 * A21 + β * (β * γ + α * A11) = 0 := by
    linear_combination r3' - (β * A12 + γ * A22) * q1 -
      (γ * (β * A11 + γ * A21 + β) + α * A11) * hs1
  have r5'' : A02 * (1 + A11) + A01 * A12 + γ * (β * γ + α * A11) = 0 := by
    linear_combination r5' - (β * (β * A12 + γ * A22 + γ) + α * A22) * hs2 -
      (β * A11 + γ * A21) * q2 + (A02 + α * γ) * hm
  have hΔβ : β * (α * (1 + A11) + β * γ) = 0 := by
    linear_combination α * r2' + γ * hq1' + α * β * hm - α * A21 * γ * h2
  have hΔγ : γ * (α * (1 + A11) + β * γ) = 0 := by
    linear_combination α * r1' + β * hq2' - α * A12 * β * h2
  have hβ : β = 0 := mul_self_eq_zero.mp (by
    linear_combination -(α * β) * r3'' + (A01 + α * β) * hΔβ + β * A02 * hq1' - β * β * hq3')
  have hγ : γ = 0 := mul_self_eq_zero.mp (by
    linear_combination -(α * γ) * r5'' + (A02 + α * γ) * hΔγ + γ * A01 * hq2' - γ * γ * hq3')
  subst hβ hγ
  have hα : α = 1 := eq_of_mul_self_eq_charTwo (by linear_combination hq3')
  subst hα
  have hA21 : A21 = 0 := by linear_combination hq1'
  have hA12 : A12 = 0 := by linear_combination hq2'
  have hA11 : A11 = 1 := eq_of_mul_self_eq_charTwo (by linear_combination r4' - A12 * hA21)
  have hAeq : A = uSL A01 A02 0 := by
    refine Matrix.SpecialLinearGroup.ext _ _ fun i j => ?_
    fin_cases i <;> fin_cases j <;>
      simp [CFSG.ClassicalInvolution.ModelFacts.OddCover.coe_uSL,
        CFSG.ClassicalInvolution.ModelFacts.OddCover.uMat, a0, a1, a2, h01, h02, h11, h12,
        h21, h22, hA21, hA12, hA11, ← hm]
  exact ⟨A01, A02, by rw [hAeq]⟩

theorem qr_kerElt_u1 (α β γ p q' : F) :
    qr (g2X ![α, 0, 0] * g2Y ![0, β, γ] * g2A (uSL p q' 0)) (q6 0 1 0 0 0 0) = β * β := by
  simp only [qr, g2Act_kerElt, polarQ, q6_apply_inl0, q6_apply_inl1, q6_apply_inl2,
    q6_apply_inr0, q6_apply_inr1, q6_apply_inr2]
  ring

theorem qr_kerElt_u2 (α β γ p q' : F) :
    qr (g2X ![α, 0, 0] * g2Y ![0, β, γ] * g2A (uSL p q' 0)) (q6 0 0 1 0 0 0) = γ * γ := by
  simp only [qr, g2Act_kerElt, polarQ, q6_apply_inl0, q6_apply_inl1, q6_apply_inl2,
    q6_apply_inr0, q6_apply_inr1, q6_apply_inr2]
  ring

theorem qr_kerElt_v0 (α β γ p q' : F) :
    qr (g2X ![α, 0, 0] * g2Y ![0, β, γ] * g2A (uSL p q' 0)) (q6 0 0 0 1 0 0) =
      β * q' + γ * p + α * α := by
  simp only [qr, g2Act_kerElt, polarQ, q6_apply_inl0, q6_apply_inl1, q6_apply_inl2,
    q6_apply_inr0, q6_apply_inr1, q6_apply_inr2]
  ring

theorem kerElt_eq_of_qr_zero {α β γ p q' : F}
    (h : ∀ x, qr (g2X ![α, 0, 0] * g2Y ![0, β, γ] * g2A (uSL p q' 0)) x = 0) :
    α = 0 ∧ β = 0 ∧ γ = 0 := by
  have hβ : β = 0 := mul_self_eq_zero.mp (by rw [← qr_kerElt_u1 α β γ p q' , h])
  have hγ : γ = 0 := mul_self_eq_zero.mp (by rw [← qr_kerElt_u2 α β γ p q', h])
  subst hβ hγ
  refine ⟨mul_self_eq_zero.mp ?_, rfl, rfl⟩
  have := qr_kerElt_v0 α 0 0 p q'
  rw [h] at this
  linear_combination -this

theorem kerElt_eq_of_comm {α β γ p q' a b : F}
    (hc : g2X ![α, 0, 0] * g2Y ![0, β, γ] * g2A (uSL p q' 0) *
        (g2X ![1, 0, 0] * g2Y ![0, 0, 0] * g2A (uSL a b 0)) =
      g2X ![1, 0, 0] * g2Y ![0, 0, 0] * g2A (uSL a b 0) *
        (g2X ![α, 0, 0] * g2Y ![0, β, γ] * g2A (uSL p q' 0))) :
    β = 0 ∧ γ = 0 := by
  have h1 := congrArg (fun y => g2Act y (q6 (0 : F) 0 0 1 0 0)) hc
  simp only [g2Act_mul_apply (g2X ![α, 0, 0] * g2Y ![0, β, γ] * g2A (uSL p q' 0)),
    g2Act_mul_apply (g2X ![1, 0, 0] * g2Y ![0, 0, 0] * g2A (uSL a b 0)), g2Act_kerElt] at h1
  obtain ⟨-, -, -, -, e4, e5⟩ := q6_inj h1
  exact ⟨by linear_combination -e4, by linear_combination -e5⟩

end CFSG.Quasithin.Vol2.Ch11.G2Q8
