module

public import CFSG.Permutation.FiveTransitive.FixedNormalizerAction
public import CFSG.Permutation.FiveTransitive.CentralizingFixedPointCongruence

public section

namespace CFSG

namespace FiveTransitive.Degree68ThirteenThreeObstruction
open MulAction Subgroup FixedNormalizerAction

theorem false_of_fixed_counts
    {X : Type} [Fintype X] [DecidableEq X]
    (P : Subgroup (Equiv.Perm X)) (hX : Fintype.card X = 68)
    (Q : Subgroup P) (hQ : IsPGroup 13 Q)
    (hF : Nat.card (fixedPoints Q X) = 3)
    (g : Normalizer Q) (hg : orderOf g = 3)
    (hcomm : ∀ q : Q, g.val * q.val = q.val * g.val)
    (hsmall : Nat.card (Function.fixedPoints g.val.val) ≤ 5) : False := by
  classical
  let _ : Fact (Nat.Prime 3) := ⟨by decide⟩
  let _ : Fact (Nat.Prime 13) := ⟨by decide⟩
  let F := Fixed (X := X) Q
  let _ : Fintype F := Fintype.ofFinite F
  let rho := toPermHom (Normalizer Q) F
  have hfixeq : (F : Set X) = fixedPoints Q X := fixed_eq Q
  have hFc : Nat.card F = 3 := by rw [hfixeq]; exact hF
  have hm11 := CentralizingFixedPointCongruence.card_modEq P Q hQ g.val hcomm
  rw [← hfixeq] at hm11
  let e : Function.fixedPoints (rho g) ≃ {x : F // g.val.val x.val = x.val} :=
    { toFun := fun x => ⟨x.val,congrArg Subtype.val x.property⟩
      invFun := fun x => ⟨x.val,Subtype.ext x.property⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  rw [← Nat.card_congr e] at hm11
  change Nat.card (Function.fixedPoints g.val.val) % 13 =
    Nat.card (Function.fixedPoints (rho g)) % 13 at hm11
  have hl : Nat.card (Function.fixedPoints (rho g)) ≤ 5 := by
    have hb := Nat.card_le_card_of_injective
      (fun x : Function.fixedPoints (rho g) =>
        (⟨x.val.val,congrArg Subtype.val x.property⟩ : Function.fixedPoints g.val.val))
      (by
        intro x y h
        have hh := congrArg (fun z : Function.fixedPoints g.val.val => z.val) h
        change x.val.val = y.val.val at hh
        exact Subtype.ext (Subtype.ext hh))
    exact hb.trans hsmall
  let a : Function.End F := (rho g).toFun
  have ha : a ^ 3 = 1 := by
    funext x
    change ((rho g) ^ 3) x = x
    rw [← map_pow,← hg,pow_orderOf_eq_one,map_one]
    rfl
  have hmF := Equiv.Perm.card_fixedPoints_modEq (f := a) (p := 3) (n := 1)
    (by simpa only [pow_one] using ha)
  change Fintype.card F % 3 = Fintype.card (Function.fixedPoints (rho g)) % 3 at hmF
  rw [← Nat.card_eq_fintype_card,← Nat.card_eq_fintype_card,hFc] at hmF
  let b : Function.End X := g.val.val.toFun
  have hb : b ^ 3 = 1 := by
    funext x
    change ((g ^ 3).val.val) x = x
    rw [← hg,pow_orderOf_eq_one]
    rfl
  have hmX := Equiv.Perm.card_fixedPoints_modEq (f := b) (p := 3) (n := 1)
    (by simpa only [pow_one] using hb)
  change Fintype.card X % 3 = Fintype.card (Function.fixedPoints g.val.val) % 3 at hmX
  rw [hX,← Nat.card_eq_fintype_card] at hmX
  omega

end FiveTransitive.Degree68ThirteenThreeObstruction

end CFSG
