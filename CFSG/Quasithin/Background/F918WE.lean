module

public import CFSG.Quasithin.Background.F918WD

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.Quasithin.D35ValChk

open Matrix

private def mat (g : G0) : Matrix (Fin 6) (Fin 6) (ZMod 2) :=
  ((g : Matrix.GeneralLinearGroup (Fin 6) (ZMod 2)) : Matrix (Fin 6) (Fin 6) (ZMod 2))

private theorem mat_mul (g h : G0) : mat (g * h) = mat g * mat h := rfl

private theorem mat_one : mat (1 : G0) = 1 := rfl

theorem core0_of_facts (hF : D35Facts) :
    ∀ (α : (G0 ⧸ Subgroup.center G0) ≃* (G0 ⧸ Subgroup.center G0)) (E F : Subgroup G0), OffF2 E → OffF2 F →
      (E.map (QuotientGroup.mk' (Subgroup.center G0))).map α.toMonoidHom =
        F.map (QuotientGroup.mk' (Subgroup.center G0)) →
      ∃ (β : G0 ≃* G0) (P Q : Matrix (Fin 6) (Fin 6) (ZMod 2)), P * Q = 1 ∧ Q * P = 1 ∧
        (∀ g : G0, QuotientGroup.mk' (Subgroup.center G0) (β g) = α (QuotientGroup.mk' (Subgroup.center G0) g)) ∧
        ∀ g : G0,
          P * (((g : G0) : Matrix.GeneralLinearGroup (Fin 6) (ZMod 2)) : Matrix (Fin 6) (Fin 6) (ZMod 2)) =
            (((β g : G0) : Matrix.GeneralLinearGroup (Fin 6) (ZMod 2)) : Matrix (Fin 6) (Fin 6) (ZMod 2)) * P := by
  intro α E F hE hF' hα
  obtain ⟨a, b, hab, hEab⟩ := offender_classification hF hE
  obtain ⟨g, hg⟩ := V4set_conj hF hab
  let c : G0 ≃* G0 := MulAut.conj g⁻¹
  have hc : ∀ h, c h = g⁻¹ * h * g := fun h => by simp [c]
  let E₁ : Subgroup G0 := E.map c.toMonoidHom
  have hE₁ : ∀ h' : G0, h' ∈ E₁ ↔ h' ∈ V4set e1 e2 := by
    intro h'
    constructor
    · rintro ⟨h, hh, rfl⟩
      rw [MulEquiv.coe_toMonoidHom, hc]
      exact (hg h).mp ((hEab h).mp hh)
    · intro hh'
      refine ⟨g * h' * g⁻¹, (hEab _).mpr ((hg _).mpr ?_), ?_⟩
      · simpa [mul_assoc] using hh'
      · rw [MulEquiv.coe_toMonoidHom, hc]
        group
  let α₁ : (G0 ⧸ Subgroup.center G0) ≃* (G0 ⧸ Subgroup.center G0) :=
    (MulAut.conj (QuotientGroup.mk g)).trans α
  have hα₁ : ∀ h : G0, α₁ (QuotientGroup.mk (c h)) = α (QuotientGroup.mk h) := by
    intro h
    show α (QuotientGroup.mk g * QuotientGroup.mk (c h) * (QuotientGroup.mk g)⁻¹) = _
    rw [hc]
    congr 1
    simp only [QuotientGroup.mk_mul, QuotientGroup.mk_inv]
    group
  have hcomp : (α₁.toMonoidHom.comp (QuotientGroup.mk' (Subgroup.center G0))).comp c.toMonoidHom =
      α.toMonoidHom.comp (QuotientGroup.mk' (Subgroup.center G0)) :=
    MonoidHom.ext fun h => hα₁ h
  have hαE : (E₁.map (QuotientGroup.mk' (Subgroup.center G0))).map α₁.toMonoidHom =
      F.map (QuotientGroup.mk' (Subgroup.center G0)) := by
    rw [← hα]
    show ((E.map c.toMonoidHom).map (QuotientGroup.mk' (Subgroup.center G0))).map α₁.toMonoidHom = _
    rw [Subgroup.map_map, Subgroup.map_map, hcomp, ← Subgroup.map_map]
  obtain ⟨β₁, P, Q, hPQ, hQP, hβmk, hβP⟩ := core0_ref hF α₁ E₁ F hE₁ hF' hαE
  have hgg : mat g⁻¹ * mat g = 1 := by rw [← mat_mul, inv_mul_cancel, mat_one]
  have hgg' : mat g * mat g⁻¹ = 1 := by rw [← mat_mul, mul_inv_cancel, mat_one]
  refine ⟨c.trans β₁, P * mat g⁻¹, mat g * Q, ?_, ?_, ?_, ?_⟩
  · calc P * mat g⁻¹ * (mat g * Q) = P * (mat g⁻¹ * mat g) * Q := by simp only [Matrix.mul_assoc]
      _ = 1 := by rw [hgg, Matrix.mul_one, hPQ]
  · calc mat g * Q * (P * mat g⁻¹) = mat g * (Q * P) * mat g⁻¹ := by simp only [Matrix.mul_assoc]
      _ = 1 := by rw [hQP, Matrix.mul_one, hgg']
  · intro h
    show QuotientGroup.mk (β₁ (c h)) = α (QuotientGroup.mk h)
    rw [← hα₁ h]
    exact hβmk (c h)
  · intro h
    show P * mat g⁻¹ * mat h = mat (β₁ (c h)) * (P * mat g⁻¹)
    have h1 := hβP (c h)
    have h2 : mat (c h) = mat g⁻¹ * mat h * mat g := by rw [hc, mat_mul, mat_mul]
    have h1' : P * (mat g⁻¹ * mat h * mat g) = mat (β₁ (c h)) * P := by
      rw [← h2]
      exact h1
    calc P * mat g⁻¹ * mat h = P * mat g⁻¹ * mat h * (mat g * mat g⁻¹) := by rw [hgg', Matrix.mul_one]
      _ = P * (mat g⁻¹ * mat h * mat g) * mat g⁻¹ := by simp only [Matrix.mul_assoc]
      _ = mat (β₁ (c h)) * (P * mat g⁻¹) := by rw [h1', Matrix.mul_assoc]

end CFSG.Quasithin.D35ValChk
