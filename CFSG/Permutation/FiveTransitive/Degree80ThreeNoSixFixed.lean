module

public import CFSG.Permutation.FiveTransitive.Degree80ThreeMaximal
public import CFSG.Permutation.FiveTransitive.Degree80ThreeEightExcluded
public import CFSG.Permutation.FiveTransitive.MaximalOrderFixedLowerBound

public section

namespace CFSG

namespace FiveTransitive.Degree80ThreeNoSixFixed
open MulAction Subgroup FixedNormalizerAction

theorem eq_bot_of_six_fixed
    {X : Type} [Fintype X] [DecidableEq X]
    (P : Subgroup (Equiv.Perm X)) (hcard : Fintype.card X = 80)
    (h5 : IsMultiplyPretransitive P X 5) (hnotAlt : ¬ alternatingGroup X ≤ P)
    (Q : Subgroup P) (hQ : IsPGroup 3 Q)
    (hfix : 6 ≤ Nat.card (fixedPoints Q X)) : Q = ⊥ := by
  classical
  by_contra hne
  obtain ⟨U,hU,hUfix,hQU,hmax⟩ := MaximalOrderFixedLowerBound.exists_maximal 3 6 Q hQ hfix
  have hUcard : 1 < Nat.card U :=
    (Finite.one_lt_card_iff_nontrivial.mpr (Q.nontrivial_iff_ne_bot.mpr hne)).trans_le hQU
  have hUne : U ≠ ⊥ := by intro he; rw [he] at hUcard; simp at hUcard
  let _ : Fintype (Fixed (X := X) U) := Fintype.ofFinite _
  obtain ⟨hF,hAlt⟩ := Degree80ThreeMaximal.fixed_eight_and_alternating P hcard h5 hnotAlt U hU hUne hUfix hmax
  exact (Degree80ThreeEightExcluded.excluded P hcard h5 hnotAlt U hU hF hAlt).elim

theorem fixed_card_cases
    {X : Type} [Fintype X] [DecidableEq X]
    (P : Subgroup (Equiv.Perm X)) (hcard : Fintype.card X = 80)
    (h5 : IsMultiplyPretransitive P X 5) (hnotAlt : ¬ alternatingGroup X ≤ P)
    (g : P) (hg : orderOf g = 3) :
    Nat.card (Function.fixedPoints g.val) = 2 ∨ Nat.card (Function.fixedPoints g.val) = 5 := by
  classical
  let _ : Fact (Nat.Prime 3) := ⟨by decide⟩
  have hle : Nat.card (Function.fixedPoints g.val) ≤ 5 := by
    by_contra hn
    have hQ : IsPGroup 3 (zpowers g) := by
      apply IsPGroup.of_card (n := 1)
      rw [Nat.card_zpowers,hg,pow_one]
    have heq : Function.fixedPoints g.val = fixedPoints (zpowers g) X := by
      ext x
      constructor
      · intro hx z
        have hh : zpowers g ≤ stabilizer P x := zpowers_le.mpr hx
        exact hh z.property
      · intro hx
        exact hx ⟨g,mem_zpowers g⟩
    have hbot := eq_bot_of_six_fixed P hcard h5 hnotAlt (zpowers g) hQ
      (by rw [← heq]; omega)
    have hg1 : g = 1 := by
      have hh := mem_zpowers g
      rw [hbot,mem_bot] at hh
      exact hh
    rw [hg1,orderOf_one] at hg
    omega
  let a : Function.End X := g.val.toFun
  have ha : a ^ 3 = 1 := by
    funext x
    change (g ^ 3).val x = x
    rw [← hg,pow_orderOf_eq_one]
    rfl
  have hm := Equiv.Perm.card_fixedPoints_modEq (f := a) (p := 3) (n := 1)
    (by simpa only [pow_one] using ha)
  change Fintype.card X % 3 = Fintype.card (Function.fixedPoints g.val) % 3 at hm
  rw [hcard,← Nat.card_eq_fintype_card] at hm
  omega

theorem card_eq_one_of_six_fixed
    {X : Type} [Fintype X] [DecidableEq X]
    (P : Subgroup (Equiv.Perm X)) (hcard : Fintype.card X = 80)
    (h5 : IsMultiplyPretransitive P X 5) (hnotAlt : ¬ alternatingGroup X ≤ P)
    (Q : Subgroup P) (hQ : IsPGroup 3 Q)
    (hfix : 6 ≤ Nat.card (fixedPoints Q X)) : Nat.card Q = 1 := by
  rw [eq_bot_of_six_fixed P hcard h5 hnotAlt Q hQ hfix]
  exact Subgroup.card_bot

end FiveTransitive.Degree80ThreeNoSixFixed

end CFSG
