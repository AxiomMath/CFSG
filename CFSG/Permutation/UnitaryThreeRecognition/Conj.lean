module

public import Mathlib.Tactic.Group
public import Mathlib.Data.Finset.Attr
public import Mathlib.GroupTheory.GroupAction.Defs

public section

namespace CFSG.UnitaryThreeRecognition

open MulAction

variable {G : Type*} [Group G]

@[expose, reducible] def conjAction (H : Subgroup G) (X : Set G)
    (hX : ∀ h ∈ H, ∀ x ∈ X, h * x * h⁻¹ ∈ X) : MulAction H X where
  smul h x := ⟨(h : G) * x * (h : G)⁻¹, hX h h.2 x x.2⟩
  one_smul x := Subtype.ext (by
    change ((1 : H) : G) * x * ((1 : H) : G)⁻¹ = x
    simp)
  mul_smul h₁ h₂ x := Subtype.ext (by
    change ((h₁ * h₂ : H) : G) * x * ((h₁ * h₂ : H) : G)⁻¹ =
      (h₁ : G) * ((h₂ : G) * x * (h₂ : G)⁻¹) * (h₁ : G)⁻¹
    simp only [Subgroup.coe_mul]
    group)

theorem conjAction_smul_val {H : Subgroup G} {X : Set G}
    {hX : ∀ h ∈ H, ∀ x ∈ X, h * x * h⁻¹ ∈ X} (h : H) (x : X) :
    ((@HSMul.hSMul H X X (@instHSMul H X (conjAction H X hX).toSMul) h x : X) : G) =
      (h : G) * x * (h : G)⁻¹ := rfl

theorem mem_stabilizer_conjAction_iff {H : Subgroup G} {X : Set G}
    {hX : ∀ h ∈ H, ∀ x ∈ X, h * x * h⁻¹ ∈ X} (h : H) (x : X) :
    h ∈ @stabilizer H X _ (conjAction H X hX) x ↔ (h : G) * x = x * h := by
  rw [@mem_stabilizer_iff]
  constructor
  · intro e
    have e' : (h : G) * x * (h : G)⁻¹ = x := congrArg Subtype.val e
    calc (h : G) * x = (h : G) * x * (h : G)⁻¹ * h := by group
      _ = x * h := by rw [e']
  · intro e
    apply Subtype.ext
    change (h : G) * x * (h : G)⁻¹ = x
    rw [e, mul_inv_cancel_right]

end CFSG.UnitaryThreeRecognition
