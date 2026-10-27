module

public import CFSG.Permutation.FiveTransitive.Degree67FiveOrbitElevenFixed
public import CFSG.Permutation.FiveTransitive.FixedNormalizerAction
public import CFSG.Permutation.FiveTransitive.HighDegreeManningSupport

public section

namespace CFSG

namespace FiveTransitive.Degree72FiveElevenFixed
open MulAction FixedNormalizerAction

theorem fixed_le_seventeen
    {X : Type} [Fintype X] [DecidableEq X]
    (P : Subgroup (Equiv.Perm X)) (hcard : Fintype.card X = 72)
    (h5 : IsMultiplyPretransitive P X 5) (hnotAlt : ¬ alternatingGroup X ≤ P)
    (Q : Subgroup P) (hQ : IsPGroup 5 Q) (hF : Nat.card (fixedPoints Q X) = 12)
    (g : Normalizer Q) (hg : orderOf g = 11) :
    Nat.card (Function.fixedPoints g.val.val) ≤ 17 := by
  classical
  let _ : Fact (Nat.Prime 11) := ⟨by decide⟩
  let F := Fixed (X := X) Q
  let _ : Fintype F := Fintype.ofFinite _
  let rho : Normalizer Q →* Equiv.Perm F := toPermHom (Normalizer Q) F
  have hfixeq : (F : Set X) = fixedPoints Q X := fixed_eq Q
  have hFc : Nat.card F = 12 := by rw [hfixeq]; exact hF
  have hg7 : g ^ 11 = 1 := hg ▸ pow_orderOf_eq_one g
  have hsmall (x : X) : Nat.card (orbit Q x) < 125 := by
    have hb := Nat.card_le_card_of_injective (fun y : orbit Q x => y.val) Subtype.val_injective
    rw [Nat.card_eq_fintype_card (α := X),hcard] at hb
    omega
  have hm5 := Degree67FiveOrbitElevenFixed.fixed_congruence Q hQ hsmall g.val g.property
    (congrArg Subtype.val hg7)
  rw [← hfixeq] at hm5
  let Efix : Function.fixedPoints (rho g) ≃ {x : F // g.val.val x.val = x.val} :=
    { toFun := fun x => ⟨x.val,congrArg Subtype.val x.property⟩
      invFun := fun x => ⟨x.val,Subtype.ext x.property⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  change Nat.card (Function.fixedPoints g.val.val) % 5 =
    Nat.card {x : F // g.val.val x.val = x.val} % 5 at hm5
  rw [← Nat.card_congr Efix] at hm5
  have hlocal_bound : Nat.card (Function.fixedPoints (rho g)) ≤ 12 := by
    have hh := Nat.card_le_card_of_injective
      (fun x : Function.fixedPoints (rho g) => x.val) Subtype.val_injective
    rwa [hFc] at hh
  have hne : g.val.val ≠ 1 := by
    intro he
    have hh : g = 1 := Subtype.ext (Subtype.ext he)
    rw [hh,orderOf_one] at hg
    omega
  have hb := HighDegreeManningSupport.degree_le_two_mul_support P (by omega) h5 hnotAlt
    g.val.property hne
  rw [hcard] at hb
  have hglobal_bound : Nat.card (Function.fixedPoints g.val.val) ≤ 36 := by
    rw [Nat.card_eq_fintype_card,Equiv.Perm.card_fixedPoints,g.val.val.sum_cycleType,hcard]
    omega
  let a : Function.End F := (rho g).toFun
  have ha : a ^ 11 = 1 := by
    funext x
    change ((rho g) ^ 11) x = x
    rw [← map_pow,hg7,map_one]
    rfl
  have hmL := Equiv.Perm.card_fixedPoints_modEq (f := a) (p := 11) (n := 1)
    (by simpa only [pow_one] using ha)
  change Fintype.card F % 11 = Fintype.card (Function.fixedPoints (rho g)) % 11 at hmL
  rw [← Nat.card_eq_fintype_card,← Nat.card_eq_fintype_card,hFc] at hmL
  let b : Function.End X := g.val.val.toFun
  have hb7 : b ^ 11 = 1 := by
    funext x
    change (g ^ 11).val.val x = x
    rw [hg7]
    rfl
  have hmG := Equiv.Perm.card_fixedPoints_modEq (f := b) (p := 11) (n := 1)
    (by simpa only [pow_one] using hb7)
  change Fintype.card X % 11 = Fintype.card (Function.fixedPoints g.val.val) % 11 at hmG
  rw [hcard,← Nat.card_eq_fintype_card] at hmG
  change Nat.card (Function.fixedPoints g.val.val) ≤ 17
  omega

end FiveTransitive.Degree72FiveElevenFixed

end CFSG
