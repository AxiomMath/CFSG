module

public import CFSG.LocalAnalysis.StandardType.GGHalfFiveTraceForm
public import CFSG.LocalAnalysis.StandardType.GGHalfFiveLevi

public section

namespace CFSG.StandardType.GGHalf

open CFSG.LieType.Universal.SpecialLinear Matrix

private lemma f4Omega_sq_sq : (f4Omega ^ 2) ^ 2 = f4Omega := by
  have h4 : f4Omega ^ 4 = f4Omega := by
    rw [show (4 : ℕ) = 3 + 1 by norm_num, pow_add, f4Omega_pow_three, one_mul, pow_one]
  rw [← pow_mul, show (2 * 2 : ℕ) = 4 by norm_num, h4]

private lemma trace_low5_adj :
    Matrix.trace ((low5 : Matrix (Fin 3) (Fin 3) F4).adjugate) = f4Omega ^ 2 := by
  rw [← Matrix.SpecialLinearGroup.coe_inv]
  exact trace_low5_inv

private lemma trace_up5_adj :
    Matrix.trace ((up5 : Matrix (Fin 3) (Fin 3) F4).adjugate) = f4Omega ^ 2 := by
  rw [← Matrix.SpecialLinearGroup.coe_inv]
  exact trace_up5_inv

private lemma trace_conj_sl (Y A : SpecialLinearGroup (Fin 4) F4) :
    Matrix.trace ((Y * A * Y⁻¹ : SpecialLinearGroup (Fin 4) F4) : Matrix (Fin 4) (Fin 4) F4)
      = Matrix.trace (A : Matrix (Fin 4) (Fin 4) F4) := by
  rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul,
      Matrix.SpecialLinearGroup.coe_inv]
  rw [Matrix.trace_mul_comm, ← mul_assoc, Matrix.adjugate_mul, Y.2]
  simp

theorem no_graph_case
    (R₁ R₂ : SpecialLinearGroup (Fin 3) F4 →* SpecialLinearGroup (Fin 4) F4)
    (h₁ : Function.Injective R₁) (h₂ : Function.Injective R₂)
    (Y : SpecialLinearGroup (Fin 4) F4)
    (α'' : SpecialLinearGroup (Fin 3) F4 →* SpecialLinearGroup (Fin 3) F4)
    (htr : ∀ s, Matrix.trace (α'' s : Matrix (Fin 3) (Fin 3) F4) =
      (Matrix.trace ((s⁻¹ : SpecialLinearGroup (Fin 3) F4) : Matrix (Fin 3) (Fin 3) F4)) ^ 2)
    (hconj : ∀ s, Y * R₁ (α'' s) * Y⁻¹ = R₂ s)
    (hagree : R₁ low5 = R₂ up5) : False := by
  obtain ⟨σ₁, δ₁, h1⟩ := exists_trace_form R₁ h₁
  obtain ⟨σ₂, δ₂, h2⟩ := exists_trace_form R₂ h₂
  have hx : Matrix.trace (α'' up5 : Matrix (Fin 3) (Fin 3) F4) = f4Omega := by
    rw [htr up5, trace_up5_inv]
    exact f4Omega_sq_sq
  have hxinv : Matrix.trace (((α'' up5)⁻¹ : SpecialLinearGroup (Fin 3) F4) :
      Matrix (Fin 3) (Fin 3) F4) = f4Omega := by
    rw [← map_inv, htr (up5⁻¹), inv_inv, trace_up5]
    exact f4Omega_sq_sq
  have hxinv_adj : Matrix.trace (((α'' up5 : SpecialLinearGroup (Fin 3) F4) :
      Matrix (Fin 3) (Fin 3) F4).adjugate) = f4Omega := by
    rw [← Matrix.SpecialLinearGroup.coe_inv]
    exact hxinv
  have hE2 : σ₁ (f4Omega ^ 2) = σ₂ (f4Omega ^ 2) := by
    have ht := congrArg (fun g : SpecialLinearGroup (Fin 4) F4 =>
      Matrix.trace (g : Matrix (Fin 4) (Fin 4) F4)) hagree
    rw [h1 low5, h2 up5] at ht
    cases δ₁ <;> cases δ₂ <;>
      simpa [trace_low5, trace_low5_adj, trace_up5, trace_up5_adj] using ht
  have hE1 : σ₁ f4Omega = σ₂ (f4Omega ^ 2) := by
    have ht := congrArg (fun g : SpecialLinearGroup (Fin 4) F4 =>
      Matrix.trace (g : Matrix (Fin 4) (Fin 4) F4)) (hconj up5)
    rw [trace_conj_sl Y (R₁ (α'' up5))] at ht
    rw [h1 (α'' up5), h2 up5] at ht
    cases δ₁ <;> cases δ₂ <;>
      simpa [hx, hxinv_adj, trace_up5, trace_up5_adj] using ht
  have hσ : σ₁ f4Omega = σ₁ (f4Omega ^ 2) := by rw [hE1, ← hE2]
  have hω : f4Omega = f4Omega ^ 2 := σ₁.injective hσ
  have hmul : f4Omega * 1 = f4Omega * f4Omega := by
    rw [mul_one, ← pow_two]
    exact hω
  have h1ω : (1 : F4) = f4Omega := mul_left_cancel₀ f4Omega_ne_zero hmul
  exact f4Omega_ne_one h1ω.symm

end CFSG.StandardType.GGHalf

end
