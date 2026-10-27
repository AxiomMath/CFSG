
module

public import CFSG.Monster.B.TwoA.Sp8.QuadCosetBase

public import CFSG.Monster.B.TwoA.Sp8.QuadCosetC
public import CFSG.Monster.B.TwoA.Sp8.Normalizer

public noncomputable section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.Monster.B.TwoA.Sp8

open CFSG.Monster CFSG.Monster.Code CFSG.Monster.Spin CFSG.Monster.SpinLattice
  CFSG.Monster.Griess CFSG.Monster.Visible CFSG.Monster.Generated CFSG.Monster.B.Short
  CFSG.Monster.B CFSG.Monster.B.TwoA CFSG.Monster.B.Rep4371

theorem Lgrp_conj_Psi
    {l : Dfull} (hl : l ∈ Lgrp) (v : Fin 8 → ZMod 2) :
    l * Psi v * l⁻¹ = Psi v := by
  have h : Psi v * l = l * Psi v := Subgroup.mem_centralizer_iff.1 hl (Psi v) (Psi_mem_A8 v)
  rw [← h, mul_inv_cancel_right]

theorem Lgrp_conj_cQ
    {l : Dfull} (hl : l ∈ Lgrp) : l * cQ * l⁻¹ = cQ := by
  have hX := Lgrp_le_Xgrp hl
  obtain ⟨t, ht, -⟩ := (Xgrp_le_qPresGrp hX).2 0
  rw [Psi_zero', mul_one] at ht
  have hq : ∀ v, qPoly (t + v) = qPoly v := by
    intro v
    have e : l * (cQ * Psi v) * l⁻¹ = cQ * Psi (t + v) := by
      rw [show l * (cQ * Psi v) * l⁻¹ = (l * cQ * l⁻¹) * (l * Psi v * l⁻¹) by group, ht,
        Lgrp_conj_Psi hl, mul_assoc, ← Psi_add]
    exact qPoly_conj hX e
  have hqt : qPoly t = 0 := by
    have h := hq 0
    rwa [add_zero, qPoly_zero] at h
  have h0 : t = 0 := nondegenerate_b0.1 t fun v => by
    rw [b0_eq_qPoly, hq v, hqt, sub_zero, sub_self]
  rw [ht, h0, Psi_zero', mul_one]

theorem Lgrp_le_centralizer_T9 :
    Lgrp ≤ Subgroup.centralizer (T9 : Set Dfull) := by
  intro l hl
  rw [T9, Subgroup.centralizer_closure, Subgroup.mem_centralizer_iff]
  rintro x (rfl | hx)
  · have h := Lgrp_conj_cQ hl
    calc cQ * l = l * cQ * l⁻¹ * l := by rw [h]
      _ = l * cQ := by group
  · exact Subgroup.mem_centralizer_iff.1 hl x hx

theorem T9_le_Lgrp :
    T9 ≤ Lgrp := by
  rw [T9, Subgroup.closure_le]
  rintro x (rfl | hx)
  · exact cQ_mem_centralizer_A8
  · exact A8_le_Lgrp hx

theorem T9_le_center_Lgrp :
    T9.subgroupOf Lgrp ≤ Subgroup.center Lgrp := by
  intro t ht
  rw [Subgroup.mem_subgroupOf] at ht
  rw [Subgroup.mem_center_iff]
  intro l
  exact Subtype.ext ((Subgroup.mem_centralizer_iff.1 (Lgrp_le_centralizer_T9 l.2)) t ht).symm

theorem Xgrp_inf_centralizer_A8 :
    Xgrp ⊓ Subgroup.centralizer (A8 : Set Dfull) = Lgrp :=
  inf_eq_right.2 Lgrp_le_Xgrp

theorem Xgrp_inf_centralizer_T9 :
    Xgrp ⊓ Subgroup.centralizer (T9 : Set Dfull) = Lgrp := by
  apply le_antisymm
  · intro x hx
    show x ∈ Subgroup.centralizer (A8 : Set Dfull)
    exact Subgroup.centralizer_le (show (A8 : Set Dfull) ⊆ T9 from fun _ h => A8_le_T9 h) hx.2
  · exact le_inf Lgrp_le_Xgrp Lgrp_le_centralizer_T9

theorem short_quadratic_coset_action :
    cQ = iotaD (kappa ⟨rhoEquiv (pauliQ (false, 0, 127)), rhoEquiv_mem_Cgen cP_mem⟩) ∧
    CFSG.IsElementaryAbelian 2 T9 ∧ Nat.card T9 = 2 ^ 9 ∧
    (∀ k : Fin 9, (tEquiv (Multiplicative.ofAdd (Pi.single k 1)) : Dfull) = tT k) ∧
    tT = ![xhat, yhat, dhat 2 3, dhat 2 4, dhat 2 5, dhat 2 6, uhat, ghat8, cQ] ∧
    Xgrp ≤ Subgroup.normalizer (T9 : Set Dfull) ∧
    (∀ x ∈ Xgrp, ∀ a ∈ A8, x * a * x⁻¹ ∈ A8) ∧
    (∀ x ∈ Xgrp, ∀ y : Dfull, cQ * y ∈ A8 → cQ * (x * y * x⁻¹) ∈ A8) ∧
    (∀ v : Fin 8 → ZMod 2, (aEquiv (Multiplicative.ofAdd v) : Dfull) = Psi v) ∧
    (∀ x ∈ Xgrp, ∀ v w : Fin 8 → ZMod 2,
      x * (cQ * Psi v) * x⁻¹ = cQ * Psi w → qPoly w = qPoly v) ∧
    (∀ v, qForm v = qPoly v) ∧ QuadraticMap.polarBilin qForm = b0 ∧ b0.Nondegenerate ∧
    QuadraticMap.Equivalent qForm (CFSG.LieType.Universal.Spin.quadMinus 4 (ZMod 2) 1 1) ∧
    (Finset.univ.filter fun v : Fin 8 → ZMod 2 => qPoly v = 0).card = 120 ∧
    {y : Dfull | ∃ x ∈ Xgrp, x * cQ * x⁻¹ = y} =
      (fun v => cQ * Psi v) '' {v : Fin 8 → ZMod 2 | qPoly v = 0} ∧
    {y : Dfull | ∃ x ∈ Xgrp, x * cQ * x⁻¹ = y}.ncard = 120 ∧
    T9 ≤ Lgrp ∧ T9.subgroupOf Lgrp ≤ Subgroup.center Lgrp ∧
    Xgrp ⊓ Subgroup.centralizer (A8 : Set Dfull) = Lgrp ∧
    Xgrp ⊓ Subgroup.centralizer (T9 : Set Dfull) = Lgrp :=
  ⟨cQ_eq, isElementaryAbelian_T9, natCard_T9, tEquiv_single, rfl, Xgrp_le_normalizer_T9,
    fun _ hx _ ha => (Xgrp_le_qPresGrp hx).conj_mem_A8 ha,
    fun _ hx _ hy => (Xgrp_le_qPresGrp hx).conj_mem_coset hy, fun _ => coe_aEquiv _,
    fun _ hx _ _ h => qPoly_conj hx h, qForm_apply, polarBilin_qForm, nondegenerate_b0,
    equivalent_quadMinus, card_qPoly_zero, orbit_cQ, ncard_orbit_cQ, T9_le_Lgrp,
    T9_le_center_Lgrp, Xgrp_inf_centralizer_A8, Xgrp_inf_centralizer_T9⟩

end CFSG.Monster.B.TwoA.Sp8
