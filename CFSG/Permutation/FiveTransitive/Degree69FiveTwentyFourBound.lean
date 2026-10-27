module

public import CFSG.Permutation.FiveTransitive.Degree69FiveTupleDivisibility

public section

namespace CFSG

namespace FiveTransitive.Degree69FiveTwentyFourBound
open MulAction

theorem card_le_one_twenty_five
    {X : Type} [Fintype X] [DecidableEq X]
    (P : Subgroup (Equiv.Perm X)) (hcard : Fintype.card X = 69)
    (h5 : IsMultiplyPretransitive P X 5) (hnotAlt : ¬ alternatingGroup X ≤ P)
    (Q : Subgroup P) (hQ : IsPGroup 5 Q)
    (hF : Nat.card (fixedPoints Q X) = 24) : Nat.card Q ≤ 125 := by
  let _ : Fact (Nat.Prime 5) := ⟨by decide⟩
  have hd := Degree69FiveTupleDivisibility.card_dvd_desc P hcard h5 hnotAlt Q 11
    (by rw [hF])
  rw [hF] at hd
  obtain ⟨e,he⟩ := IsPGroup.iff_card.mp hQ
  have he3 : e ≤ 3 := by
    by_contra hn
    have h625 : 625 ∣ Nat.card Q := by rw [he]; exact pow_dvd_pow 5 (by omega : 4 ≤ e)
    have hh := h625.trans hd
    norm_num [Nat.descFactorial] at hh
  rw [he]
  exact Nat.pow_le_pow_right (by decide : 0 < 5) he3

end FiveTransitive.Degree69FiveTwentyFourBound

end CFSG
