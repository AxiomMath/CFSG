module

public import CFSG.Permutation.FiveTransitive.Degree79TwoSevenElements
public import CFSG.Permutation.FiveTransitive.Degree79TwoSevenOrbits
public import CFSG.Permutation.FiveTransitive.HighDegreeManningSupport

public section

namespace CFSG

namespace FiveTransitive.Degree79TwoSevenBound
open MulAction SylowFixedActionCore

private theorem sylow_card_le_ten
    {X : Type} [Fintype X] [DecidableEq X]
    (P : Subgroup (Equiv.Perm X)) (hcard : Fintype.card X = 79)
    (h5 : IsMultiplyPretransitive P X 5) (hnotAlt : ¬ alternatingGroup X ≤ P)
    (hthree : ∀ t : Set X, t.ncard = 5 → ¬ 3 ∣ Nat.card (fixingSubgroup P t))
    (hfive : ∀ t : Set X, t.ncard = 5 → ¬ 5 ∣ Nat.card (fixingSubgroup P t))
    (hseven : ∀ t : Set X, t.ncard = 5 → ¬ 7 ∣ Nat.card (fixingSubgroup P t))
    (s : Set X) (hs : s.ncard = 5) (S : Sylow 2 (fixingSubgroup P s))
    (hF : Nat.card (sylowFixedPoints X P s S) = 7) : Nat.card S ≤ 10 := by
  classical
  let _ : Fact (Nat.Prime 5) := ⟨by decide⟩
  let _ : Fact (Nat.Prime 7) := ⟨by decide⟩
  let Q := sylowImage X P s S
  have hQ : IsPGroup 2 Q := S.isPGroup'.map (fixingSubgroup P s).subtype
  have hcommon : Nat.card (fixedPoints Q X) = 7 := by
    rw [← FixedNormalizerAction.fixed_eq Q]
    exact hF
  obtain ⟨g3,hg3,hf3⟩ := Degree79TwoSevenElements.exists_three_exterior_zero P h5 hthree s hs S hF
  obtain ⟨g5,hg5,hf5⟩ := Degree79TwoSevenElements.exists_five_or_seven_exterior_le_two
    P hcard h5 5 (Or.inl rfl) hfive s hs S hF
  obtain ⟨g7,hg7,hf7⟩ := Degree79TwoSevenElements.exists_five_or_seven_exterior_le_two
    P hcard h5 7 (Or.inr rfl) hseven s hs S hF
  have horbit := Degree79TwoSevenOrbits.orbit_card_le_two
    (by rwa [Nat.card_eq_fintype_card] : Nat.card X = 79) Q hQ g3 g5 g7
    (hg3 ▸ pow_orderOf_eq_one g3) (hg5 ▸ pow_orderOf_eq_one g5) (hg7 ▸ pow_orderOf_eq_one g7)
    hf3 hf5 hf7
  let t : Finset X := (fixedPoints Q X).toFinset
  have ht : t.card = 7 := by
    rw [Set.toFinset_card,← Nat.card_eq_fintype_card]
    exact hcommon
  have hfixed : ∀ q : Q, ∀ x ∈ t, q • x = x := by
    intro q x hx
    exact (Set.mem_toFinset.mp hx) q
  have hbound (q : Q) (hq : q ≠ 1) : Nat.card (fixedBy X q) ≤ 39 := by
    have hne : q.val.val ≠ 1 := fun he => hq (Subtype.ext (Subtype.ext he))
    have hb := HighDegreeManningSupport.degree_le_two_mul_support P (by omega) h5 hnotAlt
      q.val.property hne
    rw [hcard] at hb
    change Nat.card (Function.fixedPoints q.val.val) ≤ 39
    rw [Nat.card_eq_fintype_card,Equiv.Perm.card_fixedPoints,q.val.val.sum_cycleType,hcard]
    omega
  have hb := Degree79TwoSevenOrbits.card_le_ten hcard t ht hfixed horbit hbound
  have hQcard : Nat.card Q = Nat.card S := Nat.card_congr
    ((S : Subgroup (fixingSubgroup P s)).equivMapOfInjective
      (fixingSubgroup P s).subtype Subtype.val_injective).toEquiv.symm
  rwa [hQcard] at hb

theorem sylow_card_le_eight
    {X : Type} [Fintype X] [DecidableEq X]
    (P : Subgroup (Equiv.Perm X)) (hcard : Fintype.card X = 79)
    (h5 : IsMultiplyPretransitive P X 5) (hnotAlt : ¬ alternatingGroup X ≤ P)
    (hthree : ∀ t : Set X, t.ncard = 5 → ¬ 3 ∣ Nat.card (fixingSubgroup P t))
    (hfive : ∀ t : Set X, t.ncard = 5 → ¬ 5 ∣ Nat.card (fixingSubgroup P t))
    (hseven : ∀ t : Set X, t.ncard = 5 → ¬ 7 ∣ Nat.card (fixingSubgroup P t))
    (s : Set X) (hs : s.ncard = 5) (S : Sylow 2 (fixingSubgroup P s))
    (hF : Nat.card (sylowFixedPoints X P s S) = 7) : Nat.card S ≤ 8 := by
  let _ : Fact (Nat.Prime 2) := ⟨by decide⟩
  have hb := sylow_card_le_ten P hcard h5 hnotAlt hthree hfive hseven s hs S hF
  obtain ⟨e,he⟩ := IsPGroup.iff_card.mp S.isPGroup'
  have he3 : e ≤ 3 := by
    by_contra hn
    have hp : 16 ≤ 2 ^ e := Nat.pow_le_pow_right (by decide : 0 < 2) (by omega : 4 ≤ e)
    omega
  rw [he]
  exact Nat.pow_le_pow_right (by decide) he3

end FiveTransitive.Degree79TwoSevenBound

end CFSG
