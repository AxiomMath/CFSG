
module

public import CFSG.Monster.B.TwoA.Sp8.Orth8ImageBase

public import CFSG.Monster.B.TwoA.Sp8.QuadCoset

public noncomputable section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.Monster.B.TwoA.Sp8

open CFSG.Monster CFSG.Monster.Code CFSG.Monster.B CFSG.Monster.B.TwoA

@[expose, instance_reducible] def xConj :
    MulAction Xgrp Dfull :=
  MulAction.compHom Dfull ((MulAut.conj (G := Dfull)).comp Xgrp.subtype)

theorem P4_le_Xgrp' :
    P4 ≤ Xgrp := P4_le_Xgrp

theorem Psi_rhoX
    (x : Xgrp) (v : V8) : Psi (rhoX x v) = x * Psi v * (x : Dfull)⁻¹ := by
  have h := aEquiv_rhoX x v
  rwa [coe_aEquiv, coe_aEquiv, toAdd_ofAdd, toAdd_ofAdd] at h

theorem exists_conj_cQ
    (x : Xgrp) : ∃ t : V8, (x : Dfull) * cQ * (x : Dfull)⁻¹ = cQ * Psi t := by
  obtain ⟨t, ht, -⟩ := (Xgrp_le_qPresGrp x.2).2 0
  exact ⟨t, by rw [← ht, Psi_zero', mul_one]⟩

theorem conj_cPsi_rhoX
    (x : Xgrp) {t : V8} (ht : (x : Dfull) * cQ * (x : Dfull)⁻¹ = cQ * Psi t)
    (v : V8) : (x : Dfull) * (cQ * Psi v) * (x : Dfull)⁻¹ = cQ * Psi (t + rhoX x v) := by
  rw [show (x : Dfull) * (cQ * Psi v) * (x : Dfull)⁻¹ =
      ((x : Dfull) * cQ * (x : Dfull)⁻¹) * ((x : Dfull) * Psi v * (x : Dfull)⁻¹) by group, ht,
    ← Psi_rhoX, mul_assoc, ← Psi_add]

theorem qPoly_affine
    (x : Xgrp) {t : V8} (ht : (x : Dfull) * cQ * (x : Dfull)⁻¹ = cQ * Psi t)
    (v : V8) : qPoly (t + rhoX x v) = qPoly v :=
  qPoly_conj x.2 (conj_cPsi_rhoX x ht v)

theorem mem_P4_iff
    (x : Xgrp) :
    (x : Dfull) ∈ P4 ↔ rhoX x ∈ TauCeti.QuadraticMap.orthogonalGroup qForm := by
  obtain ⟨t, ht⟩ := exists_conj_cQ x
  rw [TauCeti.QuadraticMap.mem_orthogonalGroup_iff]
  constructor
  · intro hx v
    have hc : (x : Dfull) * cQ * (x : Dfull)⁻¹ = cQ := by
      rw [Subgroup.mem_centralizer_singleton_iff.1 hx.2, mul_inv_cancel_right]
    have ht0 : t = 0 := by
      have e : cQ * Psi t = cQ * Psi 0 := by rw [← ht, hc, Psi_zero', mul_one]
      exact congrArg Multiplicative.toAdd
        (PsiHom_injective (a₁ := Multiplicative.ofAdd t) (a₂ := 1) (mul_left_cancel e))
    have h := qPoly_affine x ht v
    rw [ht0, zero_add] at h
    rw [qForm_apply, qForm_apply]
    exact h
  · intro hM
    have hq : ∀ w, qPoly (t + w) = qPoly w := by
      intro w
      obtain ⟨v, rfl⟩ := (rhoX x).surjective w
      rw [qPoly_affine x ht v, ← qForm_apply, ← qForm_apply, hM]
    have ht0 := eq_zero_of_qPoly_add hq
    refine ⟨x.2, Subgroup.mem_centralizer_singleton_iff.2 ?_⟩
    rw [ht0, Psi_zero', mul_one] at ht
    calc (x : Dfull) * cQ = (x : Dfull) * cQ * (x : Dfull)⁻¹ * x := by group
      _ = cQ * x := by rw [ht]

theorem map_P4 :

    (P4.subgroupOf Xgrp).map rhoX = TauCeti.QuadraticMap.orthogonalGroup qForm := by
  apply le_antisymm
  · rintro _ ⟨x, hx, rfl⟩
    exact (mem_P4_iff x).1 hx
  · intro M hM
    obtain ⟨x, hx⟩ := rhoXSp_surjective ⟨M, orthogonalGroup_le_isometryGroup hM⟩
    have hxM : rhoX x = M := congrArg Subtype.val hx
    refine ⟨x, ?_, hxM⟩
    show (x : Dfull) ∈ P4
    rw [mem_P4_iff, hxM]
    exact hM

theorem Lgrp_le_P4 :
    Lgrp ≤ P4 := fun l hl =>
  ⟨Lgrp_le_Xgrp hl, Subgroup.mem_centralizer_singleton_iff.2 (by
    have h := Lgrp_conj_cQ hl
    calc l * cQ = l * cQ * l⁻¹ * l := by group
      _ = cQ * l := by rw [h])⟩

@[expose] def p4Proj :
    P4 →* TauCeti.QuadraticMap.orthogonalGroup qForm :=
  (rhoX.comp (Subgroup.inclusion P4_le_Xgrp)).codRestrict _
    fun x => (mem_P4_iff (Subgroup.inclusion P4_le_Xgrp x)).1 x.2

theorem coe_p4Proj
    (x : P4) :
    (p4Proj x : V8 ≃ₗ[ZMod 2] V8) = rhoX (Subgroup.inclusion P4_le_Xgrp x) := rfl

theorem p4Proj_surjective :
    Function.Surjective p4Proj := by
  rintro ⟨M, hM⟩
  rw [← map_P4] at hM
  obtain ⟨x, hx, rfl⟩ := hM
  exact ⟨⟨(x : Dfull), hx⟩, Subtype.ext rfl⟩

theorem ker_p4Proj :
    p4Proj.ker = Lgrp.subgroupOf P4 := by
  ext x
  rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf]
  constructor
  · intro h
    have h1 : rhoX ⟨x, P4_le_Xgrp x.2⟩ = 1 := congrArg Subtype.val h
    exact (rhoX_eq_one_iff _).1 h1
  · intro h
    exact Subtype.ext ((rhoX_eq_one_iff ⟨x, P4_le_Xgrp x.2⟩).2 h)

instance Lgrp_subgroupOf_P4_normal :
    (Lgrp.subgroupOf P4).Normal :=
  ker_p4Proj ▸ p4Proj.normal_ker

@[expose] def p4QuotEquiv :

    P4 ⧸ Lgrp.subgroupOf P4 ≃* TauCeti.QuadraticMap.orthogonalGroup qForm :=
  (QuotientGroup.quotientMulEquivOfEq ker_p4Proj.symm).trans
    (QuotientGroup.quotientKerEquivOfSurjective p4Proj p4Proj_surjective)

theorem index_P4 :
    (P4.subgroupOf Xgrp).index = 120 := by
  let _ := xConj
  have hset : {y : Dfull | ∃ x ∈ Xgrp, x * cQ * x⁻¹ = y} = MulAction.orbit Xgrp cQ := by
    ext y
    constructor
    · rintro ⟨x, hx, rfl⟩
      exact ⟨⟨x, hx⟩, rfl⟩
    · rintro ⟨x, rfl⟩
      exact ⟨x, x.2, rfl⟩
  have hstab : MulAction.stabilizer Xgrp cQ = P4.subgroupOf Xgrp := by
    ext x
    rw [MulAction.mem_stabilizer_iff, Subgroup.mem_subgroupOf, P4, Subgroup.mem_inf,
      Subgroup.mem_centralizer_singleton_iff]
    change (x : Dfull) * cQ * (x : Dfull)⁻¹ = cQ ↔ _
    rw [mul_inv_eq_iff_eq_mul]
    exact ⟨fun h => ⟨x.2, h⟩, fun h => h.2⟩
  rw [← hstab, MulAction.index_stabilizer, ← hset, ncard_orbit_cQ]

theorem natCard_P4 :
    Nat.card P4 = 13247740725166080 := by
  have h := Subgroup.card_mul_index (P4.subgroupOf Xgrp)
  rw [index_P4, natCard_Xgrp, Nat.card_congr (Subgroup.subgroupOfEquivOfLe P4_le_Xgrp).toEquiv]
    at h
  omega

theorem natCard_orthogonalGroup_qForm :
    Nat.card (TauCeti.QuadraticMap.orthogonalGroup qForm) = 394813440 := by
  rw [← Nat.card_congr p4QuotEquiv.toEquiv]
  have h := Subgroup.card_eq_card_quotient_mul_card_subgroup (Lgrp.subgroupOf P4)
  rw [natCard_P4, Nat.card_congr (Subgroup.subgroupOfEquivOfLe Lgrp_le_P4).toEquiv,
    natCard_Lgrp] at h
  omega

theorem natCard_orthMinus :
    Nat.card (TauCeti.QuadraticMap.orthogonalGroup
    (CFSG.LieType.Universal.Spin.quadMinus 4 (ZMod 2) 1 1)) = 394813440 := by
  rw [← Nat.card_congr orthMinusEquiv.toEquiv, natCard_orthogonalGroup_qForm]

end CFSG.Monster.B.TwoA.Sp8
