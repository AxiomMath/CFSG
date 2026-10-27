
module

public import CFSG.Monster.B.TwoA.Amalgam.CosetGraphBase

public import CFSG.Monster.B.TwoA.Amalgam.CosetStep

public noncomputable section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.Monster.B.TwoA.Amalgam

open CFSG.Monster CFSG.Monster.B CFSG.Monster.B.TwoA CFSG.Monster.B.TwoA.Sp8
open scoped Pointwise

@[expose] def stepSet : Set Dfull :=
  {d | ∃ x ∈ Eam, ∃ a ∈ Ehat, a ∉ N1 ∧ ∃ y ∈ Eam, d = x * a * y}

theorem stepSet_eq_doubleCoset
    {a : Dfull} (ha : a ∈ Ehat) (hn : a ∉ N1) :
    stepSet = DoubleCoset.doubleCoset a (Eam : Set Dfull) Eam := by
  ext d
  constructor
  · rintro ⟨x, hx, a', ha', hn', y, hy, rfl⟩
    rw [← doubleCoset_eq ha hn ha' hn']
    exact DoubleCoset.mem_doubleCoset.2 ⟨x, hx, y, hy, rfl⟩
  · intro hd
    obtain ⟨x, hx, y, hy, rfl⟩ := DoubleCoset.mem_doubleCoset.1 hd
    exact ⟨x, hx, a, ha, hn, y, hy, rfl⟩

theorem mul_mem_stepSet
    {e d e' : Dfull} (he : e ∈ Eam) (hd : d ∈ stepSet) (he' : e' ∈ Eam) :
    e * d * e' ∈ stepSet := by
  obtain ⟨x, hx, a, ha, hn, y, hy, rfl⟩ := hd
  exact ⟨e * x, Eam.mul_mem he hx, a, ha, hn, y * e', Eam.mul_mem hy he', by group⟩

theorem stepRel_congr
    {g₁ h₁ g₂ h₂ : Shat} (hg : ((g₂ * g₁⁻¹ : Shat) : Dfull) ∈ Eam)
    (hh : ((h₂ * h₁⁻¹ : Shat) : Dfull) ∈ Eam) :
    ((h₁ * g₁⁻¹ : Shat) : Dfull) ∈ stepSet ↔ ((h₂ * g₂⁻¹ : Shat) : Dfull) ∈ stepSet := by
  have e1 : ((h₂ * g₂⁻¹ : Shat) : Dfull) = ((h₂ * h₁⁻¹ : Shat) : Dfull) *
      ((h₁ * g₁⁻¹ : Shat) : Dfull) * ((g₂ * g₁⁻¹ : Shat) : Dfull)⁻¹ := by
    simp only [Subgroup.coe_mul, Subgroup.coe_inv]
    group
  have e2 : ((h₁ * g₁⁻¹ : Shat) : Dfull) = ((h₂ * h₁⁻¹ : Shat) : Dfull)⁻¹ *
      ((h₂ * g₂⁻¹ : Shat) : Dfull) * ((g₂ * g₁⁻¹ : Shat) : Dfull) := by
    simp only [Subgroup.coe_mul, Subgroup.coe_inv]
    group
  constructor
  · intro h
    rw [e1]
    exact mul_mem_stepSet hh h (Eam.inv_mem hg)
  · intro h
    rw [e2]
    exact mul_mem_stepSet (Eam.inv_mem hh) h hg

@[expose] def stepRel :
    CVert → CVert → Prop :=
  Quotient.lift₂ (fun g h : Shat => ((h * g⁻¹ : Shat) : Dfull) ∈ stepSet) fun _ _ _ _ hg hh =>
    propext (stepRel_congr (rel_iff.1 hg) (rel_iff.1 hh))

theorem stepRel_iff (g h : Shat) :
    stepRel (cvOf g) (cvOf h) ↔ ((h * g⁻¹ : Shat) : Dfull) ∈ stepSet := Iff.rfl

@[expose] def cSigma
    (s : Shat) : Set CVert :=
  {v | ∃ x : Shat, (x : Dfull) ∈ Xgrp ∧ v = cvOf (x * s)}

theorem inv_mem_stepSet
    {d : Dfull} (hd : d ∈ stepSet) : d⁻¹ ∈ stepSet := by
  obtain ⟨a, ha, hn⟩ := exists_mem_Ehat_not_mem_N1
  rw [stepSet_eq_doubleCoset ha hn] at hd ⊢
  rw [← doubleCoset_inv ha]
  exact Set.inv_mem_inv.2 hd

theorem stepSet_subset_Shat :
    stepSet ⊆ Shat := by
  rintro _ ⟨x, hx, a, ha, -, y, hy, rfl⟩
  exact Shat.mul_mem (Shat.mul_mem (Eam_le_Shat hx) (Ehat_le_Shat ha)) (Eam_le_Shat hy)

theorem stepRel_symm
    {v w : CVert} (h : stepRel v w) : stepRel w v := by
  obtain ⟨g, rfl⟩ := cvOf_surjective v
  obtain ⟨k, rfl⟩ := cvOf_surjective w
  rw [stepRel_iff] at h ⊢
  have := inv_mem_stepSet h
  rwa [← Subgroup.coe_inv, mul_inv_rev, inv_inv] at this

@[expose] def cgraph :
    SimpleGraph CVert where
  Adj v w := v ≠ w ∧ stepRel v w
  symm := ⟨fun _ _ h => ⟨Ne.symm h.1, stepRel_symm h.2⟩⟩
  loopless := ⟨fun _ h => h.1 rfl⟩

theorem cgraph_adj_iff
    (g h : Shat) :
    cgraph.Adj (cvOf g) (cvOf h) ↔ cvOf g ≠ cvOf h ∧ ((h * g⁻¹ : Shat) : Dfull) ∈ stepSet :=
  Iff.rfl

theorem cgraph_adj_cvMul
    (v w : CVert) (s : Shat) :
    cgraph.Adj (cvMul v s) (cvMul w s) ↔ cgraph.Adj v w := by
  obtain ⟨g, rfl⟩ := cvOf_surjective v
  obtain ⟨h, rfl⟩ := cvOf_surjective w
  rw [cvMul_cvOf, cvMul_cvOf, cgraph_adj_iff, cgraph_adj_iff, mul_inv_rev, mul_assoc,
    mul_inv_cancel_left]
  constructor
  · rintro ⟨hne, hs⟩
    exact ⟨fun e => hne (by rw [← cvMul_cvOf, ← cvMul_cvOf, e]), hs⟩
  · rintro ⟨hne, hs⟩
    exact ⟨fun e => hne (cvMul_injective s (by simpa only [cvMul_cvOf] using e)), hs⟩

theorem short_F4_involution_coset_graph_data :
    Finite CVert ∧ Function.Surjective cvOf ∧
    (∀ g h : Shat, cvOf g = cvOf h ↔ ((h * g⁻¹ : Shat) : Dfull) ∈ Eam) ∧
    stepSet = {d | ∃ x ∈ Eam, ∃ a ∈ Ehat, a ∉ N1 ∧ ∃ y ∈ Eam, d = x * a * y} ∧
    (∀ a ∈ Ehat, a ∉ N1 → stepSet = DoubleCoset.doubleCoset a (Eam : Set Dfull) Eam) ∧
    (∀ g h : Shat, cgraph.Adj (cvOf g) (cvOf h) ↔
      cvOf g ≠ cvOf h ∧ ((h * g⁻¹ : Shat) : Dfull) ∈ stepSet) ∧
    (∀ g : Shat, clabel (cvOf g) = ((g : Dfull))⁻¹ * cQ * g) ∧
    (∀ g s : Shat, cvMul (cvOf g) s = cvOf (g * s)) ∧ (∀ v, cvMul v 1 = v) ∧
    (∀ v s t, cvMul v (s * t) = cvMul (cvMul v s) t) ∧
    (∀ v w s, cgraph.Adj (cvMul v s) (cvMul w s) ↔ cgraph.Adj v w) ∧
    (∀ v s, clabel (cvMul v s) = ((s : Dfull))⁻¹ * clabel v * s) ∧
    cv0 = cvOf 1 ∧ clabel cv0 = cQ ∧
    (∀ s : Shat, cSigma s = {v | ∃ x : Shat, (x : Dfull) ∈ Xgrp ∧ v = cvOf (x * s)}) :=
  ⟨inferInstance, cvOf_surjective, fun _ _ => cvOf_eq_iff, rfl,
    fun _ ha hn => stepSet_eq_doubleCoset ha hn, cgraph_adj_iff, clabel_cvOf, cvMul_cvOf,
    cvMul_one, cvMul_mul, cgraph_adj_cvMul, clabel_cvMul, rfl, clabel_cv0, fun _ => rfl⟩

end CFSG.Monster.B.TwoA.Amalgam
