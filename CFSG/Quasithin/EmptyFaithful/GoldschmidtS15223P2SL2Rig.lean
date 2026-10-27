module

public import CFSG.Quasithin.EmptyFaithful.GoldschmidtS15223P2SL2
import Mathlib.Tactic.LinearCombination

public section

namespace CFSG.Quasithin.S15223

open Matrix

variable {F : Type*} [Field F]

theorem sl2U_inv [CharP F 2] (a : F) : (sl2U a)⁻¹ = sl2U a :=
  inv_eq_of_mul_eq_one_right (sl2U_mul_self a)

theorem coe_sl2U (a : F) : (sl2U a : Matrix (Fin 2) (Fin 2) F) = !![1, a; 0, 1] := rfl

theorem eq_id_of_fixes_sl2U [CharP F 2]
    (φ : SpecialLinearGroup (Fin 2) F →* SpecialLinearGroup (Fin 2) F)
    (hinj : Function.Injective φ) (hu : ∀ a : F, φ (sl2U a) = sl2U a)
    {κ : SpecialLinearGroup (Fin 2) F} (hκ3 : κ ^ 3 = 1) (hκ1 : κ ≠ 1) (hκ : φ κ = κ) :
    ∀ g, φ g = g := by
  have h2 : (2 : F) = 0 := CharTwo.two_eq_zero
  set W := φ (sl2W : SpecialLinearGroup (Fin 2) F) with hW
  have hW2 : W * W = 1 := by rw [hW, ← map_mul, sl2W_mul_self, map_one]
  have hl1 : φ (sl2L 1) = W * sl2U 1 * W := by
    rw [← sl2W_mul_sl2U_mul_sl2W (1 : F), map_mul, map_mul, hu]
  have hW3 : W = sl2U 1 * (W * sl2U 1 * W) * sl2U 1 := by
    conv_lhs => rw [hW, ← sl2U_mul_sl2L_mul_sl2U (F := F)]
    rw [map_mul, map_mul, hu, hl1]
  obtain ⟨p, q, r, s, hM⟩ : ∃ p q r s : F, (W : Matrix (Fin 2) (Fin 2) F) = !![p, q; r, s] :=
    ⟨_, _, _, _, Matrix.eta_fin_two _⟩
  have hdet : p * s - q * r = 1 := by
    have := W.det_coe
    rwa [hM, Matrix.det_fin_two_of] at this
  have e1 := congrArg (fun A : SpecialLinearGroup (Fin 2) F => (A : Matrix (Fin 2) (Fin 2) F)) hW2
  have e3 := congrArg (fun A : SpecialLinearGroup (Fin 2) F => (A : Matrix (Fin 2) (Fin 2) F)) hW3
  simp only [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_one, hM,
    coe_sl2U] at e1 e3
  have E100 : p * p + q * r = 1 := by
    have := congrFun (congrFun e1 0) 0
    simp [Matrix.mul_apply, Fin.sum_univ_two] at this
    linear_combination this
  have E111 : r * q + s * s = 1 := by
    have := congrFun (congrFun e1 1) 1
    simp [Matrix.mul_apply, Fin.sum_univ_two] at this
    linear_combination this
  have E300 : p = (p * p + (p + q) * r) + (r * p + (r + s) * r) := by
    have := congrFun (congrFun e3 0) 0
    simp [Matrix.mul_apply, Fin.sum_univ_two] at this
    linear_combination this
  have E301 : q = ((p * p + (p + q) * r) + (r * p + (r + s) * r)) +
      ((p * q + (p + q) * s) + (r * q + (r + s) * s)) := by
    have := congrFun (congrFun e3 0) 1
    simp [Matrix.mul_apply, Fin.sum_univ_two] at this
    linear_combination this
  have E310 : r = r * p + (r + s) * r := by
    have := congrFun (congrFun e3 1) 0
    simp [Matrix.mul_apply, Fin.sum_univ_two] at this
    linear_combination this
  have hps : s = p := by
    have h : (p - s) ^ 2 = 0 := by
      linear_combination E100 + E111 - 2 * hdet - 2 * q * r * h2
    exact (sub_eq_zero.mp ((pow_eq_zero_iff two_ne_zero).mp h)).symm
  have hr : r * r = r := by
    linear_combination (-1 : F) * E310 + (-(p * r)) * h2 + (-r) * hps
  have hp : p = 1 + p * r + r * r := by
    linear_combination E300 + E100 + (p * r) * h2 + r * hps
  have hr01 : r = 0 ∨ r = 1 := by
    have h : r * (r - 1) = 0 := by linear_combination hr
    rcases mul_eq_zero.mp h with h | h
    · exact Or.inl h
    · exact Or.inr (by linear_combination h)
  rcases hr01 with hr0 | hr1
  ·
    exfalso
    subst hr0
    have hp1 : p = 1 := by linear_combination hp
    subst hp1
    subst hps
    have hq : q = 1 := by linear_combination (-1 : F) * E301 + (-2 : F) * h2
    have hWe : W = sl2U 1 := by
      apply Subtype.ext
      rw [hM, coe_sl2U, hq]
    have h1 : sl2U (1 : F) = sl2W := by
      apply hinj
      rw [hu, ← hW, hWe]
    have := congrArg (fun A : SpecialLinearGroup (Fin 2) F => (A : Matrix (Fin 2) (Fin 2) F) 0 0) h1
    simp [sl2U, sl2W] at this
  · subst hr1
    have hq : q = 1 + p * p := by linear_combination E100 + (-(p * p)) * h2
    have hψ : ∀ g : SpecialLinearGroup (Fin 2) F, (MulAut.conj (sl2U p)).toMonoidHom g =
        sl2U p * g * sl2U p := fun g => by
      show sl2U p * g * (sl2U p)⁻¹ = _
      rw [sl2U_inv]
    have hφψ : φ = (MulAut.conj (sl2U p)).toMonoidHom := by
      refine MonoidHom.eq_of_eqOn_dense closure_sl2U_sl2W ?_
      intro g hg
      rcases hg with ⟨a, rfl⟩ | hg
      · show φ (sl2U a) = (MulAut.conj (sl2U p)).toMonoidHom (sl2U a)
        rw [hu, hψ, sl2U_mul, sl2U_mul]
        congr 1
        linear_combination (-p) * h2
      · have hgw : g = sl2W := hg
        subst hgw
        show φ sl2W = (MulAut.conj (sl2U p)).toMonoidHom sl2W
        rw [hψ, ← hW]
        apply Subtype.ext
        simp only [Matrix.SpecialLinearGroup.coe_mul, hM, coe_sl2U]
        ext i j
        fin_cases i <;> fin_cases j <;>
          simp [sl2W, Matrix.mul_apply, Fin.sum_univ_two, hps, hq]
        all_goals ring
    have hκψ : sl2U p * κ * sl2U p = κ := by
      have := hκ
      rw [hφψ, hψ] at this
      exact this
    have hp0 : p = 0 := by
      by_contra hp0
      obtain ⟨a, b, c, d, hκM⟩ : ∃ a b c d : F, (κ : Matrix (Fin 2) (Fin 2) F) = !![a, b; c, d] :=
        ⟨_, _, _, _, Matrix.eta_fin_two _⟩
      have hdk : a * d - b * c = 1 := by
        have := κ.det_coe
        rwa [hκM, Matrix.det_fin_two_of] at this
      have ek := congrArg (fun A : SpecialLinearGroup (Fin 2) F => (A : Matrix (Fin 2) (Fin 2) F))
        hκψ
      simp only [Matrix.SpecialLinearGroup.coe_mul, hκM, coe_sl2U] at ek
      have k00 := congrFun (congrFun ek 0) 0
      have k01 := congrFun (congrFun ek 0) 1
      simp [Matrix.mul_apply, Fin.sum_univ_two] at k00 k01
      have hc0 : c = 0 := k00.resolve_left hp0
      have had : d = a := by
        have : p * (a + d) = 0 := by
          subst hc0
          linear_combination k01
        have h' : a + d = 0 := (mul_eq_zero.mp this).resolve_left hp0
        linear_combination h' - a * h2
      have ha1 : a = 1 := by
        subst hc0
        subst had
        have : (d - 1) ^ 2 = 0 := by linear_combination hdk + (1 - d) * h2
        exact sub_eq_zero.mp ((pow_eq_zero_iff two_ne_zero).mp this)
      have hκu : κ = sl2U b := by
        apply Subtype.ext
        rw [hκM, coe_sl2U, ha1, hc0, had, ha1]
      apply hκ1
      have h3 : κ ^ 3 = κ := by
        rw [hκu, pow_succ, pow_two, sl2U_mul_self, one_mul]
      rw [← h3, hκ3]
    intro g
    rw [hφψ, hψ, hp0, sl2U_zero]
    simp

end CFSG.Quasithin.S15223
