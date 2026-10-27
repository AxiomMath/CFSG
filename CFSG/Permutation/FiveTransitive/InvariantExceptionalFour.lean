module

public import CFSG.Permutation.FiveTransitive.PowerTwoExceptionalFour

public section

namespace CFSG

namespace FiveTransitive.InvariantExceptionalFour

open MulAction

theorem ncard_eq_four
    {H X : Type*} [Group H] [Finite H] [Finite X] [MulAction H X]
    (hH : 8 ∣ Nat.card H)
    (O E : Set X) (hOE : E ⊆ O)
    (hO : ∀ (h : H) (x : X), x ∈ O → h • x ∈ O)
    (hE : ∀ (h : H) (x : X), x ∈ E → h • x ∈ E)
    (hEcard : E.ncard = 4) (k : ℕ) (hOcard : O.ncard = 2 ^ k)
    (hfree : ∀ (h : H) (x : X), x ∈ O → x ∉ E → h • x = x → h = 1) :
    O.ncard = 4 := by
  let Y : SubMulAction H X := { carrier := O, smul_mem' := hO }
  let F : Set Y := {y | y.val ∈ E}
  have hF : F.ncard = 4 := by
    let e : F ≃ E :=
      { toFun := fun y => ⟨y.val.val, y.property⟩
        invFun := fun y => ⟨⟨y.val, hOE y.property⟩, y.property⟩
        left_inv := fun _ => rfl
        right_inv := fun _ => rfl }
    rw [← Nat.card_coe_set_eq, Nat.card_congr e, Nat.card_coe_set_eq, hEcard]
  have hY : Nat.card Y = 2 ^ k := by
    change Nat.card O = _
    rwa [Nat.card_coe_set_eq]
  have hstable : ∀ (h : H) (y : Y), y ∈ F → h • y ∈ F := by
    intro h y hy
    exact hE h y.val hy
  have hfreeY : ∀ (h : H) (y : Y), y ∉ F → h • y = y → h = 1 := by
    intro h y hy he
    exact hfree h y.val y.property hy (congrArg Subtype.val he)
  have hc := PowerTwoExceptionalFour.card_eq_four hH k hY F hF hstable hfreeY
  change Nat.card O = 4 at hc
  rwa [Nat.card_coe_set_eq] at hc

end FiveTransitive.InvariantExceptionalFour

end CFSG
