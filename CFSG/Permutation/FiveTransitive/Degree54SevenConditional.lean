module

public import CFSG.Permutation.FiveTransitive.Degree54SevenFixed
public import CFSG.Permutation.FiveTransitive.Degree54SevenOrbitFiveFixed

public section

namespace CFSG

namespace FiveTransitive.Degree54SevenConditional

open MulAction SylowFixedActionCore

private theorem sylow_card_eq_one_of_five_fixed_four
    {X : Type} [Fintype X] [DecidableEq X]
    (P : Subgroup (Equiv.Perm X)) (hcard : Fintype.card X = 54)
    (h5 : IsMultiplyPretransitive P X 5) (hnotAlt : ¬ alternatingGroup X ≤ P)
    (hfive : ∀ g : P, orderOf g = 5 → Nat.card (Function.fixedPoints g.val) = 4)
    (s : Set X) (hs : s.ncard = 5)
    (S : Sylow 7 (fixingSubgroup P s)) : Nat.card S = 1 := by
  classical
  let _ : Fact (Nat.Prime 7) := ⟨by decide⟩
  let _ : Fact (Nat.Prime 5) := ⟨by decide⟩
  by_contra hS
  let Q := sylowImage X P s S
  let N := sylowNormalizer X P s S
  let F := sylowFixedPoints X P s S
  let _ : Fintype F := Fintype.ofFinite F
  obtain ⟨hF,himage⟩ := Degree54SevenFixed.fixed_card_and_image P hcard h5 hnotAlt s hs S hS
  change Nat.card F = 5 at hF
  have hQ : IsPGroup 7 Q := S.isPGroup'.map (fixingSubgroup P s).subtype
  have hfixeq : (F : Set X) = fixedPoints Q X := FixedNormalizerAction.fixed_eq Q
  let rho : N →* Equiv.Perm F := toPermHom N F
  have hd : 5 ∣ Nat.card rho.range := by
    change 5 ∣ Nat.card ((toPermHom N F).range)
    rw [himage,Subgroup.card_top,Nat.card_perm,hF]
    norm_num [Nat.factorial]
  obtain ⟨g,hg⟩ := exists_prime_orderOf_dvd_card' (G := N) 5
    (hd.trans (Subgroup.card_range_dvd rho))
  have hg5 : g ^ 5 = 1 := hg ▸ pow_orderOf_eq_one g
  have hglobal := hfive g.val ((Subgroup.orderOf_coe g).trans hg)
  have hsmall (x : X) : Nat.card (orbit Q x) < 343 := by
    have hb := Nat.card_le_card_of_injective (fun y : orbit Q x => y.val) Subtype.val_injective
    rw [Nat.card_eq_fintype_card (α := X),hcard] at hb
    omega
  have hm7 := Degree54SevenOrbitFiveFixed.fixed_congruence Q hQ hsmall
    g.val g.property (congrArg Subtype.val hg5)
  rw [← hfixeq] at hm7
  change Nat.card (Function.fixedPoints g.val.val) % 7 =
    Nat.card {x : F // g.val.val x.val = x.val} % 7 at hm7
  let e : Function.fixedPoints (rho g) ≃ {x : F // g.val.val x.val = x.val} :=
    { toFun := fun x => ⟨x.val,congrArg Subtype.val x.property⟩
      invFun := fun x => ⟨x.val,Subtype.ext x.property⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  rw [← Nat.card_congr e] at hm7
  change Nat.card (Function.fixedPoints g.val.val) % 7 =
    Nat.card (Function.fixedPoints (rho g)) % 7 at hm7
  rw [hglobal] at hm7
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
  have ha : a ^ 5 = 1 := by
    funext x
    change ((rho g) ^ 5) x = x
    rw [← map_pow,hg5,map_one]
    rfl
  have hm5 := Equiv.Perm.card_fixedPoints_modEq (f := a) (p := 5) (n := 1)
    (by simpa only [pow_one] using ha)
  change Fintype.card F % 5 = Fintype.card (Function.fixedPoints (rho g)) % 5 at hm5
  rw [← Nat.card_eq_fintype_card,← Nat.card_eq_fintype_card,hF] at hm5
  omega

theorem not_dvd_five_fixer_of_five_fixed_four
    {X : Type} [Fintype X] [DecidableEq X]
    (P : Subgroup (Equiv.Perm X)) (hcard : Fintype.card X = 54)
    (h5 : IsMultiplyPretransitive P X 5) (hnotAlt : ¬ alternatingGroup X ≤ P)
    (hfive : ∀ g : P, orderOf g = 5 → Nat.card (Function.fixedPoints g.val) = 4)
    (s : Set X) (hs : s.ncard = 5) : ¬ 7 ∣ Nat.card (fixingSubgroup P s) := by
  let _ : Fact (Nat.Prime 7) := ⟨by decide⟩
  intro hd
  let S : Sylow 7 (fixingSubgroup P s) := Sylow.nonempty.some
  have hdiv : 7 ∣ Nat.card S := S.pow_dvd_card_of_pow_dvd_card (n := 1) hd
  rw [sylow_card_eq_one_of_five_fixed_four P hcard h5 hnotAlt hfive s hs S] at hdiv
  norm_num at hdiv

theorem not_dvd_ambient_of_five_fixed_four
    {X : Type} [Fintype X] [DecidableEq X]
    (P : Subgroup (Equiv.Perm X)) (hcard : Fintype.card X = 54)
    (h5 : IsMultiplyPretransitive P X 5) (hnotAlt : ¬ alternatingGroup X ≤ P)
    (hfive : ∀ g : P, orderOf g = 5 → Nat.card (Function.fixedPoints g.val) = 4) :
    ¬ 7 ∣ Nat.card P := by
  classical
  let _ : Fact (Nat.Prime 7) := ⟨by decide⟩
  intro hd
  obtain ⟨g,hg⟩ := exists_prime_orderOf_dvd_card' (G := P) 7 hd
  let a : Function.End X := g.val.toFun
  have ha : a ^ 7 = 1 := by
    funext x
    change (g ^ 7).val x = x
    rw [← hg,pow_orderOf_eq_one]
    rfl
  have hm := Equiv.Perm.card_fixedPoints_modEq (f := a) (p := 7) (n := 1)
    (by simpa only [pow_one] using ha)
  change Fintype.card X % 7 = Fintype.card (Function.fixedPoints g.val) % 7 at hm
  rw [hcard,← Nat.card_eq_fintype_card] at hm
  have hf : 5 ≤ (Function.fixedPoints g.val).ncard := by
    rw [← Nat.card_coe_set_eq]
    omega
  obtain ⟨s,hsub,hs⟩ := Set.exists_subset_card_eq hf
  let u : fixingSubgroup P s := ⟨g,(mem_fixingSubgroup_iff P).mpr (fun x hx => hsub hx)⟩
  have hu : orderOf u = 7 := (Subgroup.orderOf_coe u).symm.trans hg
  exact not_dvd_five_fixer_of_five_fixed_four P hcard h5 hnotAlt hfive s hs
    (hu ▸ orderOf_dvd_natCard u)

end FiveTransitive.Degree54SevenConditional

end CFSG
