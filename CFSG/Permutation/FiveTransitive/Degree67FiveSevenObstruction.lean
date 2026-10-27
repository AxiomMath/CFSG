module

public import CFSG.Permutation.FiveTransitive.Degree58FiveOrbitSevenFixed
public import CFSG.Permutation.FiveTransitive.FixedNormalizerAction
public import CFSG.Permutation.FiveTransitive.SylowFixedActionCore

public section

namespace CFSG

namespace FiveTransitive.Degree67FiveSevenObstruction

open MulAction Subgroup FixedNormalizerAction

theorem excluded
    {X : Type} [Fintype X] [DecidableEq X]
    (P : Subgroup (Equiv.Perm X)) (hcard : Fintype.card X = 67)
    (hseven : ∀ g : P, orderOf g = 7 → Nat.card (Function.fixedPoints g.val) = 4)
    (Q : Subgroup P) (hQ : IsPGroup 5 Q)
    [Fintype (Fixed (X := X) Q)]
    (hF : Nat.card (Fixed (X := X) Q) = 7)
    (hAlt : alternatingGroup (Fixed (X := X) Q) ≤ Image (X := X) Q) : False := by
  classical
  let _ : Fact (Nat.Prime 5) := ⟨by decide⟩
  let _ : Fact (Nat.Prime 7) := ⟨by decide⟩
  let F := Fixed (X := X) Q
  let N := Normalizer Q
  let rho := toPermHom N F
  have hd : 7 ∣ Nat.card rho.range :=
    (SylowFixedActionCore.odd_prime_dvd_alternating_card F (by decide : Nat.Prime 7) (by decide)
      (by rw [← Nat.card_eq_fintype_card]; change 7 ≤ Nat.card (Fixed (X := X) Q); omega)).trans
      (Subgroup.card_dvd_of_le hAlt)
  obtain ⟨g,hg⟩ := exists_prime_orderOf_dvd_card' (G := N) 7
    (hd.trans (Subgroup.card_range_dvd rho))
  have hsmall : ∀ x : X, Nat.card (orbit Q x) < 125 := by
    intro x
    have hb := Nat.card_le_card_of_injective (fun y : orbit Q x => y.val) Subtype.val_injective
    rw [Nat.card_eq_fintype_card (α := X),hcard] at hb
    omega
  have hm5 := Degree58FiveOrbitSevenFixed.fixed_congruence Q hQ hsmall g.val g.property
    (congrArg Subtype.val (hg ▸ pow_orderOf_eq_one g))
  have hfixeq : (F : Set X) = fixedPoints Q X := fixed_eq Q
  rw [← hfixeq] at hm5
  let e : Function.fixedPoints (rho g) ≃ {x : F // g.val.val x.val = x.val} :=
    { toFun := fun x => ⟨x.val,congrArg Subtype.val x.property⟩
      invFun := fun x => ⟨x.val,Subtype.ext x.property⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  change Nat.card (Function.fixedPoints g.val.val) ≡ Nat.card {x : F // g.val.val x.val = x.val} [MOD 5] at hm5
  rw [← Nat.card_congr e] at hm5
  change Nat.card (Function.fixedPoints g.val.val) % 5 = Nat.card (Function.fixedPoints (rho g)) % 5 at hm5
  have hglobal := hseven g.val ((Subgroup.orderOf_coe g).trans hg)
  rw [hglobal] at hm5
  let f : Function.fixedPoints (rho g) → Function.fixedPoints g.val.val :=
    fun x => ⟨x.val.val,congrArg Subtype.val x.property⟩
  have hf : Function.Injective f := by
    intro x y h
    have hh := congrArg (fun z : Function.fixedPoints g.val.val => z.val) h
    change x.val.val = y.val.val at hh
    exact Subtype.ext (Subtype.ext hh)
  have hle := Nat.card_le_card_of_injective f hf
  rw [hglobal] at hle
  let a : Function.End F := (rho g).toFun
  have ha : a ^ 7 = 1 := by
    funext x
    change ((rho g) ^ 7) x = x
    rw [← map_pow,← hg,pow_orderOf_eq_one,map_one]
    rfl
  have hm7 := Equiv.Perm.card_fixedPoints_modEq (f := a) (p := 7) (n := 1)
    (by simpa only [pow_one] using ha)
  change Fintype.card F % 7 = Fintype.card (Function.fixedPoints (rho g)) % 7 at hm7
  rw [← Nat.card_eq_fintype_card,← Nat.card_eq_fintype_card] at hm7
  change Nat.card (Fixed (X := X) Q) % 7 = _ at hm7
  rw [hF] at hm7
  omega

end FiveTransitive.Degree67FiveSevenObstruction

end CFSG
