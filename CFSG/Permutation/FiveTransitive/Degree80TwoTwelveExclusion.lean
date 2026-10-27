module

public import CFSG.Permutation.FiveTransitive.Degree80TwoTwelvePairs
public import CFSG.Permutation.FiveTransitive.SmallOrbitFiveFixed
public import CFSG.Permutation.FiveTransitive.Degree80FiveOrder
public import CFSG.Permutation.FiveTransitive.Degree80TwoTwelveOrbitAlternatives

public section

namespace CFSG

namespace FiveTransitive.Degree80TwoTwelveExclusion
open MulAction SylowFixedActionCore

theorem fixed_card_ne_twelve
    {X : Type} [Fintype X] [DecidableEq X]
    (P : Subgroup (Equiv.Perm X)) (hcard : Fintype.card X = 80)
    (h5 : IsMultiplyPretransitive P X 5) (hnotAlt : ¬ alternatingGroup X ≤ P)
    (s : Set X) (hs : s.ncard = 5) (S : Sylow 2 (fixingSubgroup P s)) :
    Nat.card (sylowFixedPoints X P s S) ≠ 12 := by
  classical
  intro hF
  let _ : Fact (Nat.Prime 5) := ⟨by decide⟩
  let Q := sylowImage X P s S
  let N := sylowNormalizer X P s S
  let F := sylowFixedPoints X P s S
  let _ : Fintype F := Fintype.ofFinite F
  let rho : N →* Equiv.Perm F := toPermHom N F
  change Nat.card F = 12 at hF
  obtain ⟨g,hg⟩ := Degree80TwoTwelvePairs.exists_five P h5 s hs S hF
  have hg5 : g ^ 5 = 1 := hg ▸ pow_orderOf_eq_one g
  have hcases := Degree80FiveOrder.fixed_card_cases P hcard h5 hnotAlt g.val
    ((Subgroup.orderOf_coe g).trans hg)
  have hgloballe : Nat.card (Function.fixedPoints g.val.val) ≤ 5 := by omega
  have hfixeq : (F : Set X) = fixedPoints Q X := FixedNormalizerAction.fixed_eq Q
  let f : Function.fixedPoints (rho g) → Function.fixedPoints g.val.val :=
    fun x => ⟨x.val.val,congrArg Subtype.val x.property⟩
  have hf : Function.Injective f := by
    intro x y h
    have hh := congrArg (fun z : Function.fixedPoints g.val.val => z.val) h
    change x.val.val = y.val.val at hh
    exact Subtype.ext (Subtype.ext hh)
  have hle := Nat.card_le_card_of_injective f hf
  let a : Function.End F := (rho g).toFun
  have ha : a ^ 5 = 1 := by
    funext x
    change ((rho g) ^ 5) x = x
    rw [← map_pow,hg5,map_one]
    rfl
  have hm := Equiv.Perm.card_fixedPoints_modEq (f := a) (p := 5) (n := 1)
    (by simpa only [pow_one] using ha)
  change Fintype.card F % 5 = Fintype.card (Function.fixedPoints (rho g)) % 5 at hm
  rw [← Nat.card_eq_fintype_card,← Nat.card_eq_fintype_card,hF] at hm
  have hlocal : Nat.card (Function.fixedPoints (rho g)) = 2 := by omega
  have hglobal : Nat.card (Function.fixedPoints g.val.val) = 5 := by omega
  have hQ : IsPGroup 2 Q := S.isPGroup'.map (fixingSubgroup P s).subtype
  have hsmall := Degree80TwoTwelveOrbitAlternatives.orbit_card_le_four P hcard h5 hnotAlt s hs S hF
  have hparity := SmallOrbitFiveFixed.fixed_congruence Q hQ hsmall g.val g.property
    (congrArg Subtype.val hg5)
  rw [← hfixeq] at hparity
  let e : Function.fixedPoints (rho g) ≃ {x : F // g.val • x.val = x.val} :=
    { toFun := fun x => ⟨x.val,congrArg Subtype.val x.property⟩
      invFun := fun x => ⟨x.val,Subtype.ext x.property⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  rw [← Nat.card_congr e] at hparity
  change Nat.card (Function.fixedPoints g.val.val) % 2 =
    Nat.card (Function.fixedPoints (rho g)) % 2 at hparity
  rw [hglobal,hlocal] at hparity
  norm_num at hparity

end FiveTransitive.Degree80TwoTwelveExclusion

end CFSG
