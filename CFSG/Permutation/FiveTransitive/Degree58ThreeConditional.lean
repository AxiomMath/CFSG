module

public import CFSG.Permutation.FiveTransitive.Degree58ThreeFixed
public import CFSG.Permutation.FiveTransitive.ThreeGroupOrbitSevenFixed

public section

namespace CFSG

namespace FiveTransitive.Degree58ThreeConditional

open MulAction SylowFixedActionCore

private theorem sylow_card_eq_one_of_seven_fixed_two
    {X : Type} [Fintype X] [DecidableEq X]
    (P : Subgroup (Equiv.Perm X)) (hcard : Fintype.card X = 58)
    (h5 : IsMultiplyPretransitive P X 5) (hnotAlt : ¬ alternatingGroup X ≤ P)
    (hseven : ∀ g : P, orderOf g = 7 → Nat.card (Function.fixedPoints g.val) = 2)
    (s : Set X) (hs : s.ncard = 5)
    (S : Sylow 3 (fixingSubgroup P s)) : Nat.card S = 1 := by
  classical
  let _ : Fact (Nat.Prime 3) := ⟨by decide⟩
  let _ : Fact (Nat.Prime 7) := ⟨by decide⟩
  by_contra hS
  let Q := sylowImage X P s S
  let N := sylowNormalizer X P s S
  let F := sylowFixedPoints X P s S
  let _ : Fintype F := Fintype.ofFinite F
  obtain ⟨hF,himage⟩ := Degree58ThreeFixed.three_fixed_card_and_image P hcard h5 hnotAlt s hs S hS
  change Nat.card F = 7 at hF
  let _ : Nontrivial F := Finite.one_lt_card_iff_nontrivial.mp (by omega)
  have hQ : IsPGroup 3 Q := S.isPGroup'.map (fixingSubgroup P s).subtype
  have hfixeq : (F : Set X) = fixedPoints Q X := FixedNormalizerAction.fixed_eq Q
  let rho : N →* Equiv.Perm F := toPermHom N F
  have hd : 7 ∣ Nat.card rho.range := by
    apply dvd_trans (b := Nat.card (alternatingGroup F))
    · rw [nat_card_alternatingGroup,hF]
      norm_num [Nat.factorial]
    · exact Subgroup.card_dvd_of_le himage
  obtain ⟨g,hg⟩ := exists_prime_orderOf_dvd_card' (G := N) 7
    (hd.trans (Subgroup.card_range_dvd rho))
  have hg7 : g ^ 7 = 1 := hg ▸ pow_orderOf_eq_one g
  have hglobal := hseven g.val ((Subgroup.orderOf_coe g).trans hg)
  have hsmall (x : X) : Nat.card (orbit Q x) < 81 := by
    have hb := Nat.card_le_card_of_injective (fun y : orbit Q x => y.val) Subtype.val_injective
    rw [Nat.card_eq_fintype_card (α := X),hcard] at hb
    omega
  have hm3 := ThreeGroupOrbitSevenFixed.fixed_congruence Q hQ hsmall
    g.val g.property (congrArg Subtype.val hg7)
  rw [← hfixeq] at hm3
  change Nat.card (Function.fixedPoints g.val.val) % 3 =
    Nat.card {x : F // g.val.val x.val = x.val} % 3 at hm3
  let e : Function.fixedPoints (rho g) ≃ {x : F // g.val.val x.val = x.val} :=
    { toFun := fun x => ⟨x.val,congrArg Subtype.val x.property⟩
      invFun := fun x => ⟨x.val,Subtype.ext x.property⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  rw [← Nat.card_congr e] at hm3
  change Nat.card (Function.fixedPoints g.val.val) % 3 =
    Nat.card (Function.fixedPoints (rho g)) % 3 at hm3
  rw [hglobal] at hm3
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
    rw [← map_pow,hg7,map_one]
    rfl
  have hm7 := Equiv.Perm.card_fixedPoints_modEq (f := a) (p := 7) (n := 1)
    (by simpa only [pow_one] using ha)
  change Fintype.card F % 7 = Fintype.card (Function.fixedPoints (rho g)) % 7 at hm7
  rw [← Nat.card_eq_fintype_card,← Nat.card_eq_fintype_card,hF] at hm7
  omega

theorem not_dvd_five_fixer_of_seven_fixed_two
    {X : Type} [Fintype X] [DecidableEq X]
    (P : Subgroup (Equiv.Perm X)) (hcard : Fintype.card X = 58)
    (h5 : IsMultiplyPretransitive P X 5) (hnotAlt : ¬ alternatingGroup X ≤ P)
    (hseven : ∀ g : P, orderOf g = 7 → Nat.card (Function.fixedPoints g.val) = 2)
    (s : Set X) (hs : s.ncard = 5) : ¬ 3 ∣ Nat.card (fixingSubgroup P s) := by
  let _ : Fact (Nat.Prime 3) := ⟨by decide⟩
  intro hd
  let S : Sylow 3 (fixingSubgroup P s) := Sylow.nonempty.some
  have hdiv : 3 ∣ Nat.card S := S.pow_dvd_card_of_pow_dvd_card (n := 1) hd
  rw [sylow_card_eq_one_of_seven_fixed_two P hcard h5 hnotAlt hseven s hs S] at hdiv
  norm_num at hdiv

end FiveTransitive.Degree58ThreeConditional

end CFSG
