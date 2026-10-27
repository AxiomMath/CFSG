module

public import CFSG.Permutation.FiveTransitive.Degree36SmallPrimeEntrance
public import CFSG.Permutation.FiveTransitive.Degree36AbelianFiveBound
public import CFSG.Permutation.FiveTransitive.Degree31FiveCentralizerImage
public import CFSG.Permutation.FiveTransitive.FiveGroup625NonabelianCentralizer
public import CFSG.Permutation.FiveTransitive.Degree36FiveCentralizerSemiregular

public section

namespace CFSG

namespace FiveTransitive.Degree36SylowFiveOrder

open MulAction SylowFixedActionCore

theorem card_eq_five
    {X : Type} [Fintype X] [DecidableEq X]
    (P : Subgroup (Equiv.Perm X)) (hcard : Fintype.card X = 36)
    (h5 : IsMultiplyPretransitive P X 5) (hnotAlt : ¬ alternatingGroup X ≤ P)
    (s : Set X) (hs : s.ncard = 5)
    (S : Sylow 5 (fixingSubgroup P s)) (hS : Nat.card S ≠ 1) :
    Nat.card S = 5 := by
  classical
  let _ : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  obtain ⟨hF,him,hbound⟩ := Degree36SmallPrimeEntrance.five_entrance P hcard h5 hnotAlt s hs S hS
  let Q := sylowImage X P s S
  have hQcard : Nat.card Q = Nat.card S := Nat.card_congr
    ((S : Subgroup (fixingSubgroup P s)).equivMapOfInjective
      (fixingSubgroup P s).subtype Subtype.val_injective).toEquiv.symm
  have hQ : IsPGroup 5 Q := S.isPGroup'.map (fixingSubgroup P s).subtype
  have hQne : Q ≠ ⊥ := fun h => hS (hQcard.symm.trans (Subgroup.card_eq_one.mpr h))
  have hfixeq : (sylowFixedPoints X P s S : Set X) = fixedPoints Q X :=
    FixedNormalizerAction.fixed_eq Q
  have hfixed : Nat.card (fixedPoints Q X) = 6 := by rw [← hfixeq]; exact hF
  have h9 : 9 ∣ Nat.card (Subgroup.centralizer (Q : Set P)) := by
    by_cases hab : IsMulCommutative Q
    · let _ : IsMulCommutative Q := hab
      have hb := Degree36AbelianFiveBound.card_le_one_hundred_twenty_five
        P hcard h5 hnotAlt Q hQ hfixed
      exact Degree31FiveCentralizerImage.nine_dvd_centralizer Q hF him
        (FiveGroupSmallThreeAutomorphism.nine_not_dvd_card_mulAut Q hQ hb)
    · exact FiveGroup625NonabelianCentralizer.nine_dvd_centralizer Q hQ
        (by rwa [hQcard]) hab hF him
  rw [← hQcard]
  exact Degree36FiveCentralizerSemiregular.card_eq_five P hcard h5 hnotAlt
    Q hQ hQne hfixed h9

end FiveTransitive.Degree36SylowFiveOrder

end CFSG
