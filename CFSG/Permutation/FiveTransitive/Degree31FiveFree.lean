module

public import CFSG.Permutation.FiveTransitive.Degree31SylowFiveFixed
public import CFSG.Permutation.FiveTransitive.Degree31FiveGroupBound
public import CFSG.Permutation.FiveTransitive.Degree31FiveCentralizerImage
public import CFSG.Permutation.FiveTransitive.Degree31FiveCentralizer
public import CFSG.Permutation.FiveTransitive.FiveGroupSmallThreeAutomorphism

public section

namespace CFSG

namespace FiveTransitive.Degree31FiveFree

open MulAction SylowFixedActionCore

theorem five_not_dvd_five_fixer_card
    {X : Type} [Fintype X] [DecidableEq X]
    (P : Subgroup (Equiv.Perm X)) (hcard : Fintype.card X = 31)
    (h5 : IsMultiplyPretransitive P X 5) (hnotAlt : ¬ alternatingGroup X ≤ P)
    (s : Set X) (hs : s.ncard = 5) :
    ¬ 5 ∣ Nat.card (fixingSubgroup P s) := by
  classical
  let _ : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  intro hpdiv
  let S : Sylow 5 (fixingSubgroup P s) := Sylow.nonempty.some
  have hS : Nat.card S ≠ 1 := by
    intro he
    have hh := (S : Subgroup (fixingSubgroup P s)).index_mul_card
    rw [he,mul_one] at hh
    exact S.not_dvd_index (hh ▸ hpdiv)
  let Q := sylowImage X P s S
  let F := sylowFixedPoints X P s S
  have hQcard : Nat.card Q = Nat.card S := Nat.card_congr
    ((S : Subgroup (fixingSubgroup P s)).equivMapOfInjective
      (fixingSubgroup P s).subtype Subtype.val_injective).toEquiv.symm
  have hQ : IsPGroup 5 Q := S.isPGroup'.map (fixingSubgroup P s).subtype
  have hfixeq : (F : Set X) = fixedPoints Q X := by
    ext x
    constructor
    · intro hx q
      exact hx (⟨⟨q.val,Q.le_normalizer q.property⟩,q.property⟩ : sylowInNormalizer X P s S)
    · intro hx q
      exact hx (⟨q.val.val,q.property⟩ : Q)
  obtain ⟨hF,himage⟩ := Degree31SylowFiveFixed.fixed_card_and_image P hcard h5 hnotAlt s hs S hS
  have hfixed : 5 ≤ Nat.card (fixedPoints Q X) := by rw [← hfixeq,hF]; norm_num
  have hQ125 := Degree31FiveGroupBound.card_le_one_twenty_five P hcard h5 hnotAlt Q hQ hfixed
  have haut := FiveGroupSmallThreeAutomorphism.nine_not_dvd_card_mulAut Q hQ hQ125
  have hnine := Degree31FiveCentralizerImage.nine_dvd_centralizer Q hF himage haut
  obtain ⟨e,he⟩ := IsPGroup.iff_card.mp hQ
  have hepos : 1 ≤ e := by
    by_contra hn
    have he0 : e = 0 := by omega
    apply hS
    rw [← hQcard,he,he0,pow_zero]
  have hpQ : 5 ∣ Nat.card Q := by
    rw [he]
    exact pow_dvd_pow 5 hepos
  obtain ⟨u,hu⟩ := exists_prime_orderOf_dvd_card' (G := Q) 5 hpQ
  exact Degree31FiveCentralizer.nine_not_dvd_card P hcard h5 hnotAlt Q hfixed u hu hnine

end FiveTransitive.Degree31FiveFree

end CFSG
