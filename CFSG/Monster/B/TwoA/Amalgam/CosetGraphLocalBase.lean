
module

public import CFSG.Monster.B.TwoA.Amalgam.CosetGraph

@[expose] public noncomputable section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.Monster.B.TwoA.Amalgam

open CFSG.Monster CFSG.Monster.B CFSG.Monster.B.TwoA CFSG.Monster.B.TwoA.Sp8
open scoped Pointwise

def elS {a : Dfull} (ha : a ∈ Ehat) : Shat := ⟨a, Ehat_le_Shat ha⟩

theorem coe_elS {a : Dfull} (ha : a ∈ Ehat) : (elS ha : Dfull) = a := rfl

theorem not_mem_Eam_of
    {a : Dfull} (ha : a ∈ Ehat) (hn : a ∉ N1) : a ∉ Eam := fun h =>
  hn ⟨ha, Eam_le_centralizer h⟩

theorem cvOf_eq_cv0_iff
    (g : Shat) : cvOf g = cv0 ↔ (g : Dfull) ∈ Eam := by
  rw [cv0, cvOf_eq_iff]
  simp only [Subgroup.coe_inv, one_mul]
  exact ⟨fun h => by simpa using Eam.inv_mem h, fun h => Eam.inv_mem h⟩

theorem mem_stepSet_iff
    {a : Dfull} (ha : a ∈ Ehat) (hn : a ∉ N1) {d : Dfull} :
    d ∈ stepSet ↔ ∃ x ∈ Eam, ∃ y ∈ Eam, d = x * a * y := by
  rw [stepSet_eq_doubleCoset ha hn, DoubleCoset.mem_doubleCoset]
  simp only [SetLike.mem_coe]

abbrev P1Cos
    : Type := Quotient (QuotientGroup.rightRel ((Pc 0).subgroupOf Eam))

theorem p1rel_iff {e f : Eam} :
    QuotientGroup.rightRel ((Pc 0).subgroupOf Eam) e f ↔ ((f * e⁻¹ : Eam) : Dfull) ∈ Pc 0 :=
  (QuotientGroup.rightRel_apply (s := (Pc 0).subgroupOf Eam)).trans Subgroup.mem_subgroupOf

theorem conj_mem_Pc_zero
    {a : Dfull} (ha : a ∈ Ehat) (hn : a ∉ N1) {p : Dfull} (hp : p ∈ Pc 0) :
    a * p * a⁻¹ ∈ Pc 0 := by
  have h := conj_mem_P1 (Ehat.inv_mem ha) (not_mem_N1_inv hn) hp
  rwa [inv_inv] at h

theorem cvMul_transitive
    (v w : CVert) : ∃ s : Shat, cvMul v s = w := by
  obtain ⟨g, rfl⟩ := cvOf_surjective v
  obtain ⟨h, rfl⟩ := cvOf_surjective w
  exact ⟨g⁻¹ * h, by rw [cvMul_cvOf, mul_inv_cancel_left]⟩

theorem cvMul_cv0_iff
    (s : Shat) : cvMul cv0 s = cv0 ↔ (s : Dfull) ∈ Eam := by
  rw [cv0, cvMul_cvOf, one_mul, ← cv0, cvOf_eq_cv0_iff]

theorem cvMul_inv_cancel
    (v : CVert) (s : Shat) : cvMul (cvMul v s) s⁻¹ = v := by
  rw [← cvMul_mul, mul_inv_cancel, cvMul_one]

theorem cvMul_inv_cancel'
    (v : CVert) (s : Shat) : cvMul (cvMul v s⁻¹) s = v := by
  rw [← cvMul_mul, inv_mul_cancel, cvMul_one]

theorem conj_inv_cQ
    {e : Dfull} (he : e ∈ Eam) : e⁻¹ * cQ = cQ * e⁻¹ := by
  have hc : e * cQ = cQ * e := Subgroup.mem_centralizer_singleton_iff.1 (Eam_le_centralizer he)
  rw [inv_mul_eq_iff_eq_mul, ← mul_assoc, hc, mul_inv_cancel_right]

theorem Eam_inf_centralizer_xhat :
    Eam ⊓ Subgroup.centralizer {xhat} = Pc 0 := by
  apply le_antisymm
  · rintro x ⟨hxE, hx⟩
    refine ⟨?_, Eam_le_centralizer hxE⟩
    rw [← centralizer_xhat]
    exact hx
  · intro x hx
    refine ⟨Pc_le_Eam 0 hx, ?_⟩
    rw [centralizer_xhat]
    exact hx.1

theorem range_clabel
    : Set.range clabel = {y | ∃ s : Shat, ((s : Dfull))⁻¹ * cQ * s = y} := by
  ext y
  constructor
  · rintro ⟨v, rfl⟩
    obtain ⟨g, rfl⟩ := cvOf_surjective v
    exact ⟨g, rfl⟩
  · rintro ⟨s, rfl⟩
    exact ⟨cvOf s, rfl⟩

def CSc : Subgroup Shat := (Subgroup.centralizer {cQ}).comap Shat.subtype

theorem mem_CSc {g : Shat} : g ∈ CSc ↔ (g : Dfull) ∈ Subgroup.centralizer {cQ} := Iff.rfl

theorem clabel_eq_cQ_iff
    (g : Shat) : clabel (cvOf g) = cQ ↔ g ∈ CSc := by
  rw [clabel_cvOf, mem_CSc, Subgroup.mem_centralizer_singleton_iff]
  constructor
  · intro h
    have h2 : (g : Dfull) * ((g : Dfull)⁻¹ * cQ * g) = g * cQ := by rw [h]
    rw [show (g : Dfull) * ((g : Dfull)⁻¹ * cQ * g) = cQ * g by group] at h2
    exact h2.symm
  · intro h
    rw [mul_assoc, ← h, inv_mul_cancel_left]

abbrev EinC :
    Subgroup CSc := (Eam.subgroupOf Shat).subgroupOf CSc

theorem fiber_rel_iff {g h : CSc} :
    QuotientGroup.rightRel EinC g h ↔ (((h * g⁻¹ : CSc) : Shat) : Dfull) ∈ Eam :=
  (QuotientGroup.rightRel_apply (s := EinC)).trans
    (Subgroup.mem_subgroupOf.trans Subgroup.mem_subgroupOf)

def fiberMap :
    Quotient (QuotientGroup.rightRel EinC) → clabel ⁻¹' {cQ} :=
  Quotient.lift (fun g : CSc => ⟨cvOf g, (clabel_eq_cQ_iff g).2 g.2⟩) fun _ _ hgh =>
    Subtype.ext (cvOf_eq_iff.2 (fiber_rel_iff.1 hgh))

theorem fiberMap_bijective :
    Function.Bijective fiberMap := by
  constructor
  · intro u w h
    obtain ⟨g, rfl⟩ := Quotient.mk_surjective u
    obtain ⟨k, rfl⟩ := Quotient.mk_surjective w
    exact Quotient.sound (fiber_rel_iff.2 (cvOf_eq_iff.1 (congrArg Subtype.val h)))
  · rintro ⟨v, hv⟩
    obtain ⟨g, rfl⟩ := cvOf_surjective v
    exact ⟨Quotient.mk _ ⟨g, (clabel_eq_cQ_iff g).1 hv⟩, rfl⟩

theorem natCard_fiber_cQ :
    Nat.card (clabel ⁻¹' {cQ}) = EinC.index := by
  rw [← Nat.card_congr (Equiv.ofBijective _ fiberMap_bijective), Subgroup.index,
    Nat.card_congr (QuotientGroup.quotientRightRelEquivQuotientLeftRel _)]

theorem cvOf_eq_iff_of_X
    {x₁ x₂ : Shat} (h₁ : (x₁ : Dfull) ∈ Xgrp) (h₂ : (x₂ : Dfull) ∈ Xgrp) :
    cvOf x₁ = cvOf x₂ ↔ (x₁ : Dfull)⁻¹ * cQ * x₁ = (x₂ : Dfull)⁻¹ * cQ * x₂ := by
  rw [cvOf_eq_iff]
  constructor
  · intro h
    have hc : ((x₂ * x₁⁻¹ : Shat) : Dfull) * cQ = cQ * ((x₂ * x₁⁻¹ : Shat) : Dfull) :=
      Subgroup.mem_centralizer_singleton_iff.1 (Eam_le_centralizer h)
    simp only [Subgroup.coe_mul, Subgroup.coe_inv] at hc
    calc (x₁ : Dfull)⁻¹ * cQ * x₁ = (x₂ : Dfull)⁻¹ * ((x₂ * (x₁ : Dfull)⁻¹) * cQ) * x₁ := by
          group
      _ = (x₂ : Dfull)⁻¹ * (cQ * (x₂ * (x₁ : Dfull)⁻¹)) * x₁ := by rw [hc]
      _ = (x₂ : Dfull)⁻¹ * cQ * x₂ := by group
  · intro h
    have hX : ((x₂ * x₁⁻¹ : Shat) : Dfull) ∈ Xgrp := by
      simp only [Subgroup.coe_mul, Subgroup.coe_inv]
      exact Xgrp.mul_mem h₂ (Xgrp.inv_mem h₁)
    have hc : ((x₂ * x₁⁻¹ : Shat) : Dfull) * cQ = cQ * ((x₂ * x₁⁻¹ : Shat) : Dfull) := by
      simp only [Subgroup.coe_mul, Subgroup.coe_inv]
      calc (x₂ : Dfull) * (x₁ : Dfull)⁻¹ * cQ =
            x₂ * ((x₁ : Dfull)⁻¹ * cQ * x₁) * (x₁ : Dfull)⁻¹ := by group
        _ = x₂ * ((x₂ : Dfull)⁻¹ * cQ * x₂) * (x₁ : Dfull)⁻¹ := by rw [h]
        _ = cQ * (x₂ * (x₁ : Dfull)⁻¹) := by group
    exact Pc_le_Eam 3 ⟨hX, Subgroup.mem_centralizer_singleton_iff.2 hc⟩

theorem mem_cSigma_one {v : CVert} :
    v ∈ cSigma 1 ↔ ∃ x : Shat, (x : Dfull) ∈ Xgrp ∧ v = cvOf x := by
  show (∃ x : Shat, (x : Dfull) ∈ Xgrp ∧ v = cvOf (x * 1)) ↔ _
  simp only [mul_one]

theorem mem_cOrbit_conj
    {x : Dfull} (hx : x ∈ Xgrp) : x⁻¹ * cQ * x ∈ cOrbit :=
  ⟨x⁻¹, Xgrp.inv_mem hx, by rw [inv_inv]⟩

theorem cQ_ne_conj
    {a : Dfull} (ha : a ∈ Ehat) (hn : a ∉ N1) : cQ ≠ a⁻¹ * cQ * a := by
  intro h
  rw [conj_cQ_of_not_mem ha hn] at h
  have h' : cQ * 1 = cQ * xhat := by rw [mul_one]; exact h
  exact xhat_ne_one (mul_left_cancel h').symm

end CFSG.Monster.B.TwoA.Amalgam
