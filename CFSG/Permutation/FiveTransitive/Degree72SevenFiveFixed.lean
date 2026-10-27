module

public import CFSG.Permutation.FiveTransitive.Degree72SevenFixed
public import CFSG.Permutation.FiveTransitive.Degree54SevenOrbitFiveFixed

public section

namespace CFSG

namespace FiveTransitive.Degree72SevenFiveFixed
open MulAction SylowFixedActionCore

private theorem exists_normalizer_five_fixed_thirty_two
    {X : Type} [Fintype X] [DecidableEq X]
    (P : Subgroup (Equiv.Perm X)) (hcard : Fintype.card X = 72)
    (h5 : IsMultiplyPretransitive P X 5) (hnotAlt : ¬ alternatingGroup X ≤ P)
    (s : Set X) (hs : s.ncard = 5)
    (S : Sylow 7 (fixingSubgroup P s)) (hS : Nat.card S ≠ 1) :
    ∃ g : sylowNormalizer X P s S, orderOf g = 5 ∧
      Nat.card (Function.fixedPoints g.val.val) = 32 := by
  classical
  let _ : Fact (Nat.Prime 7) := ⟨by decide⟩
  let _ : Fact (Nat.Prime 5) := ⟨by decide⟩
  let Q := sylowImage X P s S
  let N := sylowNormalizer X P s S
  let F := sylowFixedPoints X P s S
  let _ : Fintype F := Fintype.ofFinite F
  obtain ⟨hF,hAlt⟩ := Degree72SevenFixed.fixed_card_and_alternating P hcard h5 hnotAlt s hs S hS
  change Nat.card F = 9 at hF
  let _ : Nontrivial F := Finite.one_lt_card_iff_nontrivial.mp (by omega)
  have hQ : IsPGroup 7 Q := S.isPGroup'.map (fixingSubgroup P s).subtype
  have hfixeq : (F : Set X) = fixedPoints Q X := FixedNormalizerAction.fixed_eq Q
  let rho : N →* Equiv.Perm F := toPermHom N F
  have hd : 5 ∣ Nat.card rho.range := by
    have ha : 5 ∣ Nat.card (alternatingGroup F) := by
      rw [nat_card_alternatingGroup,hF]
      norm_num [Nat.factorial]
    exact ha.trans (Subgroup.card_dvd_of_le hAlt)
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
  have hglobal : Nat.card (Function.fixedPoints g.val.val) ≤ 36 := by
    rw [Nat.card_eq_fintype_card,Equiv.Perm.card_fixedPoints,g.val.val.sum_cycleType,hcard]
    omega
  have hlocal_le_global : Nat.card (Function.fixedPoints (rho g)) ≤
      Nat.card (Function.fixedPoints g.val.val) := by
    let f : Function.fixedPoints (rho g) → Function.fixedPoints g.val.val :=
      fun x => ⟨x.val.val,congrArg Subtype.val x.property⟩
    exact Nat.card_le_card_of_injective f (by
      intro x y hxy
      exact Subtype.ext (Subtype.ext (congrArg (fun z => z.val) hxy)))
  exact ⟨g,hg,by omega⟩

private theorem exists_five_large_fixed
    {X : Type} [Fintype X] [DecidableEq X]
    (P : Subgroup (Equiv.Perm X)) (hcard : Fintype.card X = 72)
    (h5 : IsMultiplyPretransitive P X 5) (hnotAlt : ¬ alternatingGroup X ≤ P)
    (s : Set X) (hs : s.ncard = 5)
    (S : Sylow 7 (fixingSubgroup P s)) (hS : Nat.card S ≠ 1) :
    ∃ g : P, orderOf g = 5 ∧ Nat.card (Function.fixedPoints g.val) = 32 := by
  obtain ⟨g,hg,hfix⟩ := exists_normalizer_five_fixed_thirty_two P hcard h5 hnotAlt s hs S hS
  exact ⟨g.val,(Subgroup.orderOf_coe g).trans hg,hfix⟩

theorem not_dvd_five_fixer_of_five_fixed_le
    {X : Type} [Fintype X] [DecidableEq X]
    (P : Subgroup (Equiv.Perm X)) (hcard : Fintype.card X = 72)
    (h5 : IsMultiplyPretransitive P X 5) (hnotAlt : ¬ alternatingGroup X ≤ P)
    (hfive : ∀ g : P, orderOf g = 5 → Nat.card (Function.fixedPoints g.val) ≤ 27)
    (s : Set X) (hs : s.ncard = 5) : ¬ 7 ∣ Nat.card (fixingSubgroup P s) := by
  let _ : Fact (Nat.Prime 7) := ⟨by decide⟩
  intro hd
  let S : Sylow 7 (fixingSubgroup P s) := Sylow.nonempty.some
  have hdiv : 7 ∣ Nat.card S := S.pow_dvd_card_of_pow_dvd_card (n := 1) hd
  have hS : Nat.card S ≠ 1 := by intro he; rw [he] at hdiv; norm_num at hdiv
  obtain ⟨g,hg,hfix⟩ := exists_five_large_fixed P hcard h5 hnotAlt s hs S hS
  have hb := hfive g hg
  omega

end FiveTransitive.Degree72SevenFiveFixed

end CFSG
