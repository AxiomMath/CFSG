module

public import CFSG.LocalAnalysis.StandardType.GGSecFiveZSInputs

public section

namespace CFSG.StandardType.ZS

variable {p : ℕ} [Fact p.Prime] {U : Type} [AddCommGroup U] [Module (ZMod p) U]

theorem isIsom_smul_iff {Q : QuadraticForm (ZMod p) U} {μ : ZMod p} (hμ : μ ≠ 0)
    (g : U ≃ₗ[ZMod p] U) : IsIsom p (μ • Q) g ↔ IsIsom p Q g := by
  constructor
  · intro h v
    have := h v
    simp only [QuadraticMap.smul_apply, smul_eq_mul] at this
    exact mul_left_cancel₀ hμ this
  · intro h v
    simp only [QuadraticMap.smul_apply, smul_eq_mul]
    exact congrArg (fun z : ZMod p => μ * z) (h v)

theorem classRefl_smul {Q : QuadraticForm (ZMod p) U} {c μ : ZMod p} (hμ : μ ≠ 0) :
    ClassRefl p (μ • Q) (μ * c) = ClassRefl p Q c := by
  ext t
  constructor
  · rintro ⟨htr, htiso, a, ha, hta⟩
    refine ⟨htr, (isIsom_smul_iff hμ t).mp htiso, a, ?_, hta⟩
    simp only [QuadraticMap.smul_apply, smul_eq_mul] at ha
    exact mul_left_cancel₀ hμ ha
  · rintro ⟨htr, htiso, a, ha, hta⟩
    refine ⟨htr, (isIsom_smul_iff hμ t).mpr htiso, a, ?_, hta⟩
    simp only [QuadraticMap.smul_apply, smul_eq_mul, ha]

theorem classRefl_sq_mul {Q : QuadraticForm (ZMod p) U} {c s : ZMod p} (hs : s ≠ 0) :
    ClassRefl p Q (s ^ 2 * c) = ClassRefl p Q c := by
  ext t
  constructor
  · rintro ⟨htr, htiso, a, ha, hta⟩
    refine ⟨htr, htiso, s⁻¹ • a, ?_, ?_⟩
    · rw [QuadraticMap.map_smul, smul_eq_mul, ha]
      field_simp
    · rw [map_smul, hta, smul_neg]
  · rintro ⟨htr, htiso, a, ha, hta⟩
    refine ⟨htr, htiso, s • a, ?_, ?_⟩
    · rw [QuadraticMap.map_smul, smul_eq_mul, ha]
      ring
    · rw [map_smul, hta, smul_neg]

end CFSG.StandardType.ZS

end
