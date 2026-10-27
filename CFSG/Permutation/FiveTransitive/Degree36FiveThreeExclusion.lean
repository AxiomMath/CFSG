module

public import CFSG.Permutation.FiveTransitive.Degree36OrderThreeFixed
public import CFSG.Permutation.FiveTransitive.Degree36FiveThreeCentralizer
public import CFSG.Permutation.FiveTransitive.Degree36SylowFiveOrder

public section

namespace CFSG

namespace FiveTransitive.Degree36FiveThreeExclusion

open MulAction SylowFixedActionCore

theorem five_not_dvd_of_nine_not_dvd
    {X : Type} [Fintype X] [DecidableEq X]
    (P : Subgroup (Equiv.Perm X)) (hcard : Fintype.card X = 36)
    (h5 : IsMultiplyPretransitive P X 5) (hnotAlt : ¬ alternatingGroup X ≤ P)
    (s : Set X) (hs : s.ncard = 5) (h9 : ¬ 9 ∣ Nat.card (fixingSubgroup P s)) :
    ¬ 5 ∣ Nat.card (fixingSubgroup P s) := by
  classical
  let _ : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  intro hfive
  let S : Sylow 5 (fixingSubgroup P s) := Sylow.nonempty.some
  have hSfive : 5 ∣ Nat.card S := S.pow_dvd_card_of_pow_dvd_card (n := 1) hfive
  have hSne : Nat.card S ≠ 1 := by intro h; rw [h] at hSfive; norm_num at hSfive
  have hScard := Degree36SylowFiveOrder.card_eq_five P hcard h5 hnotAlt s hs S hSne
  obtain ⟨hF,him,_⟩ := Degree36SmallPrimeEntrance.five_entrance P hcard h5 hnotAlt s hs S hSne
  let Q := sylowImage X P s S
  have hQ : IsPGroup 5 Q := S.isPGroup'.map (fixingSubgroup P s).subtype
  have hQcard : Nat.card Q = 5 := by
    have hmap : Nat.card Q = Nat.card S :=
      Subgroup.card_map_of_injective (fixingSubgroup P s).subtype_injective
    exact hmap.trans hScard
  have hfixed : Nat.card (fixedPoints Q X) = 6 := by
    rw [← FixedNormalizerAction.fixed_eq Q]
    exact hF
  have hC9 : 9 ∣ Nat.card (Subgroup.centralizer (Q : Set P)) :=
    Degree31FiveCentralizerImage.nine_dvd_centralizer Q hF him
      (FiveGroupSmallThreeAutomorphism.nine_not_dvd_card_mulAut Q hQ (by omega))
  exact Degree36FiveThreeCentralizer.nine_not_dvd_centralizer P hcard Q hQ hQcard hfixed
    (Degree36OrderThreeFixed.fixed_card_eq_six P hcard h5 hnotAlt s hs h9) hC9

end FiveTransitive.Degree36FiveThreeExclusion

end CFSG
