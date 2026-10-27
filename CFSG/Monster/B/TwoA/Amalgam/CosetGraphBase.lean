
module

public import CFSG.Monster.B.TwoA.Amalgam.Data

@[expose] public noncomputable section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.Monster.B.TwoA.Amalgam

open CFSG.Monster CFSG.Monster.B CFSG.Monster.B.TwoA CFSG.Monster.B.TwoA.Sp8
open scoped Pointwise

abbrev CVert :
    Type := Quotient (QuotientGroup.rightRel (Eam.subgroupOf Shat))

@[expose] def cvOf
    (g : Shat) : CVert := Quotient.mk _ g

theorem cvOf_surjective :
    Function.Surjective cvOf := Quotient.mk_surjective

theorem cvOf_eq_iff
    {g h : Shat} : cvOf g = cvOf h ↔ ((h * g⁻¹ : Shat) : Dfull) ∈ Eam :=
  Quotient.eq.trans ((QuotientGroup.rightRel_apply (s := Eam.subgroupOf Shat)).trans
    Subgroup.mem_subgroupOf)

theorem rel_iff {g h : Shat} :
    QuotientGroup.rightRel (Eam.subgroupOf Shat) g h ↔ ((h * g⁻¹ : Shat) : Dfull) ∈ Eam :=
  (QuotientGroup.rightRel_apply (s := Eam.subgroupOf Shat)).trans Subgroup.mem_subgroupOf

theorem conj_cQ_congr
    {g h : Shat} (hgh : ((h * g⁻¹ : Shat) : Dfull) ∈ Eam) :
    ((g⁻¹ : Shat) : Dfull) * cQ * g = ((h⁻¹ : Shat) : Dfull) * cQ * h := by
  have hc : ((h * g⁻¹ : Shat) : Dfull) * cQ = cQ * ((h * g⁻¹ : Shat) : Dfull) :=
    Subgroup.mem_centralizer_singleton_iff.1 (Eam_le_centralizer hgh)
  simp only [Subgroup.coe_mul, Subgroup.coe_inv] at hc ⊢
  calc (g : Dfull)⁻¹ * cQ * g = (h : Dfull)⁻¹ * ((h * (g : Dfull)⁻¹) * cQ) * g := by group
    _ = (h : Dfull)⁻¹ * (cQ * (h * (g : Dfull)⁻¹)) * g := by rw [hc]
    _ = (h : Dfull)⁻¹ * cQ * h := by group

@[expose] def clabel :
    CVert → Dfull :=
  Quotient.lift (fun g : Shat => ((g⁻¹ : Shat) : Dfull) * cQ * g) fun _ _ h =>
    conj_cQ_congr (rel_iff.1 h)

theorem clabel_cvOf
    (g : Shat) : clabel (cvOf g) = ((g : Dfull))⁻¹ * cQ * g := rfl

@[expose] def cvMul
    (v : CVert) (s : Shat) : CVert :=
  Quotient.map' (· * s) (fun a b hab => by
    rw [rel_iff] at hab ⊢
    rwa [mul_inv_rev, mul_assoc, mul_inv_cancel_left]) v

theorem cvMul_cvOf
    (g s : Shat) : cvMul (cvOf g) s = cvOf (g * s) := rfl

theorem cvMul_one
    (v : CVert) : cvMul v 1 = v := by
  obtain ⟨g, rfl⟩ := cvOf_surjective v
  rw [cvMul_cvOf, mul_one]

theorem cvMul_mul
    (v : CVert) (s t : Shat) : cvMul v (s * t) = cvMul (cvMul v s) t := by
  obtain ⟨g, rfl⟩ := cvOf_surjective v
  rw [cvMul_cvOf, cvMul_cvOf, cvMul_cvOf, mul_assoc]

theorem cvMul_injective
    (s : Shat) : Function.Injective fun v => cvMul v s := by
  intro v w h
  have h' := congrArg (fun u => cvMul u s⁻¹) h
  simpa only [← cvMul_mul, mul_inv_cancel, cvMul_one] using h'

theorem clabel_cvMul
    (v : CVert) (s : Shat) :
    clabel (cvMul v s) = ((s : Dfull))⁻¹ * clabel v * s := by
  obtain ⟨g, rfl⟩ := cvOf_surjective v
  rw [cvMul_cvOf, clabel_cvOf, clabel_cvOf]
  simp only [Subgroup.coe_mul]
  group

@[expose] def cv0 : CVert := cvOf 1

theorem clabel_cv0 :
    clabel cv0 = cQ := by
  rw [cv0, clabel_cvOf]
  simp

end CFSG.Monster.B.TwoA.Amalgam
