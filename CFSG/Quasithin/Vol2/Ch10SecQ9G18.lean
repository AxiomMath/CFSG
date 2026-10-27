module

public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBGraphAction
public import CFSG.Quasithin.Vol2.Ch10SecDL3
public import CFSG.Quasithin.Vol2.Ch10SecKGA318

public section

namespace CFSG.Quasithin.Vol2.Ch10.SecC.C10P4F

open CFSG.Quasithin CFSG.ComponentClassification

abbrev τ3 : MulAut L3.Γ := CatalogueBGraphForm.slGraphAut 3 (ZMod 2)

abbrev e0' : L3.Vec := ![1, 0, 0]

abbrev e2' : L3.Vec := ![0, 0, 1]

theorem flag_fact : ∀ x y : L3.Vec,
    (∃ γ : L3.Γ, γ ^ 3 = 1 ∧ γ ≠ 1 ∧ L3.act γ x = x ∧ L3.act (τ3 γ) y = y) ∨
    (∃ h : L3.Γ, L3.act h x = e0' ∧ L3.act (τ3 h) y = e2') := by
  unfold L3.act
  decide +kernel

theorem P0_fix_e0 : ∀ p : L3.Γ, p ∈ SecD.L3.P0 → L3.act p e0' = e0' := by
  unfold L3.act
  decide +kernel

theorem tau_P0_fix_e2 : ∀ p : L3.Γ, p ∈ SecD.L3.P0 → L3.act (τ3 p) e2' = e2' := by
  unfold L3.act
  decide +kernel

theorem act_pow_fix {γ : L3.Γ} {x : L3.Vec} (h : L3.act γ x = x) (n : ℕ) :
    L3.act (γ ^ n) x = x := by
  induction n with
  | zero => exact L3.act_one x
  | succ n ih => rw [pow_succ, L3.act_mul, h, ih]

theorem act_injective (γ : L3.Γ) : Function.Injective (L3.act γ) := by
  intro x y h
  have := congrArg (L3.act γ⁻¹) h
  rwa [← L3.act_mul, ← L3.act_mul, inv_mul_cancel, L3.act_one, L3.act_one] at this

end CFSG.Quasithin.Vol2.Ch10.SecC.C10P4F
