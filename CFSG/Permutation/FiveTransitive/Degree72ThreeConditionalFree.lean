module

public import CFSG.Permutation.FiveTransitive.Degree72ThreeSixExclusion
public import CFSG.Permutation.FiveTransitive.Degree72ThreeElevenLift
public import CFSG.Permutation.FiveTransitive.Degree72ThreeFixed

public section

namespace CFSG

namespace FiveTransitive.Degree72ThreeConditionalFree
open MulAction SylowFixedActionCore

private theorem fixed_card_eq_twelve
    {X : Type} [Fintype X] [DecidableEq X]
    (P : Subgroup (Equiv.Perm X)) (hcard : Fintype.card X = 72)
    (h5 : IsMultiplyPretransitive P X 5) (hnotAlt : ¬ alternatingGroup X ≤ P)
    (s : Set X) (hs : s.ncard = 5) (S : Sylow 3 (fixingSubgroup P s))
    (hS : Nat.card S ≠ 1) : Nat.card (sylowFixedPoints X P s S) = 12 := by
  rcases Degree72ThreeFixed.three_fixed_card_cases P hcard h5 hnotAlt s hs S hS with h | h
  · exact (Degree72ThreeSixExclusion.fixed_ne_six P hcard h5 hnotAlt s hs S h).elim
  · exact h

theorem sylow_card_eq_one
    {X : Type} [Fintype X] [DecidableEq X]
    (P : Subgroup (Equiv.Perm X)) (hcard : Fintype.card X = 72)
    (h5 : IsMultiplyPretransitive P X 5) (hnotAlt : ¬ alternatingGroup X ≤ P)
    (heleven : ∀ g : P, orderOf g = 11 → Nat.card (Function.fixedPoints g.val) ≤ 17)
    (s : Set X) (hs : s.ncard = 5) (S : Sylow 3 (fixingSubgroup P s)) : Nat.card S = 1 := by
  by_contra hS
  have hF := fixed_card_eq_twelve P hcard h5 hnotAlt s hs S hS
  obtain ⟨g,hg,hfix⟩ := Degree72ThreeElevenLift.exists_eleven_fixed_twentyEight P hcard h5 hnotAlt s hs S hF
  have hb := heleven g.val ((Subgroup.orderOf_coe g).trans hg)
  omega

theorem not_dvd_five_fixer
    {X : Type} [Fintype X] [DecidableEq X]
    (P : Subgroup (Equiv.Perm X)) (hcard : Fintype.card X = 72)
    (h5 : IsMultiplyPretransitive P X 5) (hnotAlt : ¬ alternatingGroup X ≤ P)
    (heleven : ∀ g : P, orderOf g = 11 → Nat.card (Function.fixedPoints g.val) ≤ 17)
    (s : Set X) (hs : s.ncard = 5) : ¬ 3 ∣ Nat.card (fixingSubgroup P s) := by
  let _ : Fact (Nat.Prime 3) := ⟨by decide⟩
  intro hd
  let S : Sylow 3 (fixingSubgroup P s) := Sylow.nonempty.some
  have hdiv : 3 ∣ Nat.card S := S.pow_dvd_card_of_pow_dvd_card (n := 1) hd
  rw [sylow_card_eq_one P hcard h5 hnotAlt heleven s hs S] at hdiv
  norm_num at hdiv

end FiveTransitive.Degree72ThreeConditionalFree

end CFSG
