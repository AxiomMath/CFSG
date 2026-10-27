
module

public import CFSG.Monster.B.TwoA.Sp8.Orth8FormsBase

public import Certificates.Certificate3112
public import CFSG.Monster.B.TwoA.Sp8.Orth8Image

public noncomputable section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.Monster.B.TwoA.Sp8

open CFSG.Monster CFSG.Monster.Code CFSG.Monster.B CFSG.Monster.B.TwoA

theorem card_zeros_one : ∀ v : V8, qPoly v = 1 →
    (Finset.univ.filter fun w : V8 => qPoly (w + v) + 1 = 0).card = 136 :=
  Certificates.certificate3112

theorem qv_mem_minusForms
    {v : V8} (hv : qPoly v = 0) : qv v ∈ minusForms := by
  refine ⟨polarBilin_qv v, ?_⟩
  obtain ⟨x, hx, hxv⟩ := (orbit_cQ ▸ (show cQ * Psi v ∈ (fun v => cQ * Psi v) ''
    {v : V8 | qPoly v = 0} from ⟨v, hv, rfl⟩) : cQ * Psi v ∈
      {y : Dfull | ∃ x ∈ Xgrp, x * cQ * x⁻¹ = y})
  let e : QuadraticMap.IsometryEquiv qForm (qv v) :=
    ⟨rhoX ⟨x, hx⟩, fun w => by
      change qv v (rhoX ⟨x, hx⟩ w) = qForm w
      rw [qv_apply', hv, add_zero, add_comm, qForm_apply]
      exact qPoly_affine ⟨x, hx⟩ hxv w⟩
  exact ⟨e.symm.trans isometryEquivQuadMinus⟩

theorem not_mem_minusForms {v : V8} (hv : qPoly v = 1) : qv v ∉
    minusForms := by
  rintro ⟨-, ⟨e⟩⟩
  have h1 := card_zeros_of_equivalent (e.trans isometryEquivQuadMinus.symm)
  rw [card_zeros_qForm] at h1
  have h2 := card_zeros_one v hv
  simp only [qv_apply', hv] at h1
  omega

theorem minusForms_eq :
    minusForms = qv '' {v : V8 | qPoly v = 0} :=
    by
  ext Q
  constructor
  · intro hQ
    obtain ⟨v, rfl⟩ := exists_qv_eq Q hQ.1
    refine ⟨v, ?_, rfl⟩
    rcases zmod2_cases (qPoly v) with h | h
    · exact h
    · exact absurd hQ (not_mem_minusForms h)
  · rintro ⟨v, hv, rfl⟩
    exact qv_mem_minusForms hv

theorem ncard_minusForms :
    minusForms.ncard = 120 := by
  rw [minusForms_eq, Set.ncard_image_of_injective _ qv_injective, ← card_qPoly_zero,
    ← Set.ncard_coe_finset]
  congr 1
  ext v
  simp

theorem qv_conj
    (x : Xgrp) {v w : V8}
    (hv : qPoly v = 0)
    (h : (x : Dfull) * (cQ * Psi v) * (x : Dfull)⁻¹ = cQ * Psi w) :
    qv w = (qv v).comp (rhoX x).symm.toLinearMap := by
  obtain ⟨t, ht⟩ := exists_conj_cQ x
  have hw : w = t + rhoX x v := by
    have e := h.symm.trans (conj_cPsi_rhoX x ht v)
    exact congrArg Multiplicative.toAdd (PsiHom_injective
      (a₁ := Multiplicative.ofAdd w) (a₂ := Multiplicative.ofAdd (t + rhoX x v))
      (mul_left_cancel e))
  ext u
  rw [QuadraticMap.comp_apply, qv_apply', qv_apply', hw, hv, add_zero, qPoly_affine x ht v, hv,
    add_zero]
  obtain ⟨u', rfl⟩ := (rhoX x).surjective u
  rw [LinearEquiv.coe_toLinearMap, LinearEquiv.symm_apply_apply,
    show rhoX x u' + (t + rhoX x v) = t + rhoX x (u' + v) by rw [map_add]; abel,
    qPoly_affine x ht]

end CFSG.Monster.B.TwoA.Sp8
