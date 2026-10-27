module

public import Mathlib.GroupTheory.PGroup

public section

namespace CFSG

namespace FiveTransitive.CentralizingFixedPointCongruence

open MulAction

theorem card_modEq
    {X : Type*} [Finite X]
    {p : ℕ} [Fact p.Prime]
    (P : Subgroup (Equiv.Perm X)) (Q : Subgroup P) (hQ : IsPGroup p Q)
    (z : P) (hcomm : ∀ q : Q, z * q.val = q.val * z) :
    Nat.card (Function.fixedPoints z.val) ≡
      Nat.card {x : fixedPoints Q X // z.val x.val = x.val} [MOD p] := by
  let C : SubMulAction Q X :=
    { carrier := Function.fixedPoints z.val
      smul_mem' := by
        intro q x hx
        change z.val (q.val.val x) = q.val.val x
        have he := congrArg (fun a : P => a.val x) (hcomm q)
        change z.val (q.val.val x) = q.val.val (z.val x) at he
        exact he.trans (congrArg q.val.val hx) }
  let e : fixedPoints Q C ≃ {x : fixedPoints Q X // z.val x.val = x.val} :=
    { toFun := fun x => ⟨⟨x.val.val,fun q => congrArg Subtype.val (x.property q)⟩,x.val.property⟩
      invFun := fun x => ⟨⟨x.val.val,x.property⟩,fun q => Subtype.ext (x.val.property q)⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  have hm := hQ.card_modEq_card_fixedPoints C
  rw [Nat.card_congr e] at hm
  exact hm

end FiveTransitive.CentralizingFixedPointCongruence

end CFSG
