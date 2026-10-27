
module

public import CFSG.Monster.B.TwoA.Sp8.Orth8PairsBase

public import CFSG.Monster.B.TwoA.Sp8.Orth8Image

public noncomputable section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.Monster.B.TwoA.Sp8

open CFSG.Monster CFSG.Monster.Code CFSG.Monster.B CFSG.Monster.B.TwoA

theorem orbit_two_transitive
    {v₁ v₂ w₁ w₂ : V8} (h1 : qPoly v₁ = 0) (h2 : qPoly v₂ = 0)
    (h12 : v₁ ≠ v₂) (h3 : qPoly w₁ = 0) (h4 : qPoly w₂ = 0) (h34 : w₁ ≠ w₂) :
    ∃ x ∈ Xgrp, x * (cQ * Psi v₁) * x⁻¹ = cQ * Psi w₁ ∧
      x * (cQ * Psi v₂) * x⁻¹ = cQ * Psi w₂ := by
  obtain ⟨x, hx, hx1, hx2⟩ := reach_of_vec h1 h2 h12
  obtain ⟨y, hy, hy1, hy2⟩ := reach_of_vec h3 h4 h34
  refine ⟨y * x⁻¹, Xgrp.mul_mem hy (Xgrp.inv_mem hx), ?_, ?_⟩
  · have e : cQ * Psi v₁ = x * cQ * x⁻¹ := hx1.symm
    rw [e, show y * x⁻¹ * (x * cQ * x⁻¹) * (y * x⁻¹)⁻¹ = y * cQ * y⁻¹ by group, hy1]
  · have e : cQ * Psi v₂ = x * (cQ * xhat) * x⁻¹ := hx2.symm
    rw [e, show y * x⁻¹ * (x * (cQ * xhat) * x⁻¹) * (y * x⁻¹)⁻¹ = y * (cQ * xhat) * y⁻¹ by group,
      hy2]

theorem fix_orbit_iff
    (x : Xgrp) :
    (∀ v : V8, qPoly v = 0 → (x : Dfull) * (cQ * Psi v) * (x : Dfull)⁻¹ = cQ * Psi v) ↔
      (x : Dfull) ∈ Lgrp := by
  constructor
  · intro h
    obtain ⟨t, ht⟩ := exists_conj_cQ x
    have hc : (x : Dfull) * cQ * (x : Dfull)⁻¹ = cQ := by
      have := h 0 qPoly_zero
      rwa [Psi_zero', mul_one] at this
    have ht0 : t = 0 := by
      have e : cQ * Psi t = cQ * Psi 0 := by rw [← ht, hc, Psi_zero', mul_one]
      exact congrArg Multiplicative.toAdd
        (PsiHom_injective (a₁ := Multiplicative.ofAdd t) (a₂ := 1) (mul_left_cancel e))
    have hfix : ∀ v : V8, qPoly v = 0 → rhoX x v = v := by
      intro v hv
      have e := (h v hv).symm.trans (conj_cPsi_rhoX x ht v)
      rw [ht0, zero_add] at e
      have e2 : Psi v = Psi (rhoX x v) := mul_left_cancel e
      exact (congrArg Multiplicative.toAdd (PsiHom_injective
        (a₁ := Multiplicative.ofAdd v) (a₂ := Multiplicative.ofAdd (rhoX x v)) e2)).symm
    have hone : rhoX x = 1 := by
      apply LinearEquiv.toLinearMap_injective
      apply (Pi.basisFun (ZMod 2) (Fin 8)).ext
      intro k
      obtain ⟨a, b, ha, hb, hab⟩ := zeros_span k
      change rhoX x (Pi.basisFun (ZMod 2) (Fin 8) k) = Pi.basisFun (ZMod 2) (Fin 8) k
      rw [Pi.basisFun_apply, ← hab, map_add, hfix a ha, hfix b hb]
    exact (rhoX_eq_one_iff x).1 hone
  · intro hl v _
    have h1 := Lgrp_conj_cQ hl
    have h2 := Lgrp_conj_Psi hl v
    rw [show (x : Dfull) * (cQ * Psi v) * (x : Dfull)⁻¹ =
      ((x : Dfull) * cQ * (x : Dfull)⁻¹) * ((x : Dfull) * Psi v * (x : Dfull)⁻¹) by group, h1, h2]

end CFSG.Monster.B.TwoA.Sp8
