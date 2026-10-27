module

public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs

public section

namespace CFSG.RankThree.PartOne.NF7H

open Matrix

variable {K : Type*} [Field K]

@[expose] def KUMat (X Lm : Subgroup (GL (Fin 3) K)) (c : Fin 3 → K) : Prop :=
  ∀ y ∈ X, ∀ u ∈ Lm, u * u = 1 →
    (∀ w : Fin 3 → K, (u : Matrix (Fin 3) (Fin 3) K) *ᵥ w + w ∈ Submodule.span K {c}) →
    (∃ μ : K, ((y * u * y⁻¹ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) *ᵥ c = μ • c) →
    ∀ l ∈ Lm, ∀ lam : K,
      (∀ w : Fin 3 → K, ((y * u * y⁻¹ * l⁻¹ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) *ᵥ w -
        lam • w ∈ Submodule.span K {c}) → lam * lam = 1

theorem mem_span_conj_symm {P : GL (Fin 3) K} {c : Fin 3 → K} {z : Fin 3 → K}
    (hz : (P : Matrix (Fin 3) (Fin 3) K) *ᵥ z ∈
      Submodule.span K {(P : Matrix (Fin 3) (Fin 3) K) *ᵥ c}) : z ∈ Submodule.span K {c} := by
  obtain ⟨a, ha⟩ := Submodule.mem_span_singleton.1 hz
  have h1 : (((P⁻¹ : GL (Fin 3) K)) : Matrix (Fin 3) (Fin 3) K) *ᵥ
      ((P : Matrix (Fin 3) (Fin 3) K) *ᵥ z) = z := by
    rw [Matrix.mulVec_mulVec, Units.inv_mul, Matrix.one_mulVec]
  have h2 : (((P⁻¹ : GL (Fin 3) K)) : Matrix (Fin 3) (Fin 3) K) *ᵥ
      ((P : Matrix (Fin 3) (Fin 3) K) *ᵥ c) = c := by
    rw [Matrix.mulVec_mulVec, Units.inv_mul, Matrix.one_mulVec]
  rw [← h1, ← ha, Matrix.mulVec_smul, h2]
  exact Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self _)

theorem conj_mulVec' (P A : GL (Fin 3) K) (w : Fin 3 → K) :
    ((P * A * P⁻¹ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) *ᵥ ((P : Matrix (Fin 3) (Fin 3) K) *ᵥ w) =
      (P : Matrix (Fin 3) (Fin 3) K) *ᵥ ((A : Matrix (Fin 3) (Fin 3) K) *ᵥ w) := by
  have h1 : (((P⁻¹ : GL (Fin 3) K)) : Matrix (Fin 3) (Fin 3) K) *ᵥ
      ((P : Matrix (Fin 3) (Fin 3) K) *ᵥ w) = w := by
    rw [Matrix.mulVec_mulVec, Units.inv_mul, Matrix.one_mulVec]
  rw [Units.val_mul, Units.val_mul, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, h1]

theorem KUMat.conj {X Lm : Subgroup (GL (Fin 3) K)} {c : Fin 3 → K} (h : KUMat X Lm c)
    (P : GL (Fin 3) K) :
    KUMat (X.map (MulAut.conj P).toMonoidHom) (Lm.map (MulAut.conj P).toMonoidHom)
      ((P : Matrix (Fin 3) (Fin 3) K) *ᵥ c) := by
  intro y' hy' u' hu' hsq hmod hstab l' hl' lam hlam
  obtain ⟨y, hy, rfl⟩ := Subgroup.mem_map.1 hy'
  obtain ⟨u, hu, rfl⟩ := Subgroup.mem_map.1 hu'
  obtain ⟨l, hl, rfl⟩ := Subgroup.mem_map.1 hl'
  simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply] at hsq hmod hstab hlam
  refine h y hy u hu ?_ ?_ ?_ l hl lam ?_
  · calc u * u = P⁻¹ * (P * u * P⁻¹ * (P * u * P⁻¹)) * P := by group
      _ = 1 := by rw [hsq]; group
  · intro w
    apply mem_span_conj_symm (P := P)
    have h1 := hmod ((P : Matrix (Fin 3) (Fin 3) K) *ᵥ w)
    rw [conj_mulVec' P u w, ← Matrix.mulVec_add] at h1
    exact h1
  · obtain ⟨μ, hμ⟩ := hstab
    refine ⟨μ, ?_⟩
    have e : P * y * P⁻¹ * (P * u * P⁻¹) * (P * y * P⁻¹)⁻¹ = P * (y * u * y⁻¹) * P⁻¹ := by group
    rw [e, conj_mulVec' P _ c, ← Matrix.mulVec_smul] at hμ
    have h2 := congrArg (fun z => (((P⁻¹ : GL (Fin 3) K)) : Matrix (Fin 3) (Fin 3) K) *ᵥ z) hμ
    simpa [Matrix.mulVec_mulVec] using h2
  · intro w
    apply mem_span_conj_symm (P := P)
    have h1 := hlam ((P : Matrix (Fin 3) (Fin 3) K) *ᵥ w)
    have e : P * y * P⁻¹ * (P * u * P⁻¹) * (P * y * P⁻¹)⁻¹ * (P * l * P⁻¹)⁻¹ =
        P * (y * u * y⁻¹ * l⁻¹) * P⁻¹ := by group
    rw [e, conj_mulVec' P _ w, ← Matrix.mulVec_smul] at h1
    rw [Matrix.mulVec_sub, Matrix.mulVec_smul]
    simpa [Matrix.mulVec_smul] using h1

end CFSG.RankThree.PartOne.NF7H
