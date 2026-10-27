module

public import CFSG.Permutation.FiveTransitive.Degree69SevenFixed
public import CFSG.Permutation.FiveTransitive.FixedNormalizerAction
public import CFSG.Permutation.FiveTransitive.Degree54SevenOrbitFiveFixed

public section

namespace CFSG

namespace FiveTransitive.Degree69SevenFiveFixed
open MulAction SylowFixedActionCore

theorem exists_five_large_fixed
    {X : Type} [Fintype X] [DecidableEq X]
    (P : Subgroup (Equiv.Perm X)) (hcard : Fintype.card X = 69)
    (h5 : IsMultiplyPretransitive P X 5) (hnotAlt : ¬ alternatingGroup X ≤ P)
    (s : Set X) (hs : s.ncard = 5)
    (S : Sylow 7 (fixingSubgroup P s)) (hS : Nat.card S ≠ 1) :
    ∃ g : P, orderOf g = 5 ∧
      (Nat.card (Function.fixedPoints g.val) = 29 ∨ Nat.card (Function.fixedPoints g.val) = 34) := by
  classical
  let _ : Fact (Nat.Prime 7) := ⟨by decide⟩
  let _ : Fact (Nat.Prime 5) := ⟨by decide⟩
  let Q := sylowImage X P s S
  let N := sylowNormalizer X P s S
  let F := sylowFixedPoints X P s S
  let _ : Fintype F := Fintype.ofFinite F
  obtain ⟨hF,himage⟩ := Degree69SevenFixed.fixed_card_and_image P hcard h5 hnotAlt s hs S hS
  change Nat.card F = 6 at hF
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
  have hgP : orderOf g.val = 5 := (Subgroup.orderOf_coe g).trans hg
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
  have hlocal := Nat.card_le_card_of_injective
    (fun x : Function.fixedPoints (rho g) => x.val) Subtype.val_injective
  rw [hF] at hlocal
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
  let b : Function.End X := g.val.val.toFun
  have hb : b ^ 5 = 1 := by
    funext x
    change (g ^ 5).val.val x = x
    rw [hg5]
    rfl
  have hglobalMod := Equiv.Perm.card_fixedPoints_modEq (f := b) (p := 5) (n := 1)
    (by simpa only [pow_one] using hb)
  change Fintype.card X % 5 = Fintype.card (Function.fixedPoints g.val.val) % 5 at hglobalMod
  rw [hcard,← Nat.card_eq_fintype_card] at hglobalMod
  have hgperm : orderOf g.val.val = 5 := (Subgroup.orderOf_coe g.val).trans hgP
  have hne : g.val.val ≠ 1 := by intro he; rw [he,orderOf_one] at hgperm; omega
  have hsupp := HighDegreeManningSupport.degree_le_two_mul_support P (by omega) h5
    hnotAlt g.val.property hne
  rw [hcard] at hsupp
  have hglobal : Nat.card (Function.fixedPoints g.val.val) ≤ 34 := by
    rw [Nat.card_eq_fintype_card,Equiv.Perm.card_fixedPoints,g.val.val.sum_cycleType,hcard]
    omega
  exact ⟨g.val,hgP,by omega⟩

theorem not_dvd_five_fixer_of_five_fixed_le
    {X : Type} [Fintype X] [DecidableEq X]
    (P : Subgroup (Equiv.Perm X)) (hcard : Fintype.card X = 69)
    (h5 : IsMultiplyPretransitive P X 5) (hnotAlt : ¬ alternatingGroup X ≤ P)
    (hfive : ∀ g : P, orderOf g = 5 → Nat.card (Function.fixedPoints g.val) ≤ 24)
    (s : Set X) (hs : s.ncard = 5) : ¬ 7 ∣ Nat.card (fixingSubgroup P s) := by
  let _ : Fact (Nat.Prime 7) := ⟨by decide⟩
  intro hd
  let S : Sylow 7 (fixingSubgroup P s) := Sylow.nonempty.some
  have hdiv : 7 ∣ Nat.card S := S.pow_dvd_card_of_pow_dvd_card (n := 1) hd
  have hS : Nat.card S ≠ 1 := by intro he; rw [he] at hdiv; norm_num at hdiv
  obtain ⟨g,hg,hfix⟩ := exists_five_large_fixed P hcard h5 hnotAlt s hs S hS
  have hb := hfive g hg
  omega

theorem not_dvd_ambient_of_five_fixed_le
    {X : Type} [Fintype X] [DecidableEq X]
    (P : Subgroup (Equiv.Perm X)) (hcard : Fintype.card X = 69)
    (h5 : IsMultiplyPretransitive P X 5) (hnotAlt : ¬ alternatingGroup X ≤ P)
    (hfive : ∀ g : P, orderOf g = 5 → Nat.card (Function.fixedPoints g.val) ≤ 24) :
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
  exact not_dvd_five_fixer_of_five_fixed_le P hcard h5 hnotAlt hfive s hs
    (hu ▸ orderOf_dvd_natCard u)

end FiveTransitive.Degree69SevenFiveFixed

end CFSG
