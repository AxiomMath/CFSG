module

public import CFSG.Permutation.FiveTransitive.Degree20ExcludeFiveExponentThree
public import CFSG.Permutation.FiveTransitive.Degree20NineteenTransfer
public import CFSG.Permutation.FiveTransitive.Degree20StabilizerCases

public section

namespace CFSG

namespace FiveTransitive.Degree20

open MulAction SubMulAction Subgroup

theorem five_point_stabilizer_card_reduced_cases
    (X : Type) [Fintype X] [DecidableEq X]
    (P : Subgroup (Equiv.Perm X))
    (hcard : Fintype.card X = 20)
    (h5 : ∀ a b : Fin 5 → X, Function.Injective a → Function.Injective b →
      ∃ g : P, ∀ i, g • a i = b i)
    (hnotAlt : ¬alternatingGroup X ≤ P)
    (s : Set X) (hs : s.ncard = 5) :
    let h := Nat.card (fixingSubgroup P s)
    (h = 27 ∨ h = 54 ∨ h = 768 ∨ h = 248832) ∨
    (h = 180 ∨ h = 360 ∨ h = 58320 ∨
      h = 116640 ∨ h = 5120) ∨
    (h = 2400 ∨ h = 21600 ∨ h = 777600) := by
  classical
  dsimp
  let h := Nat.card (fixingSubgroup P s)
  have hcases :=
    five_point_stabilizer_card_cases
      X P hcard h5 hnotAlt s hs
  change
    (h = 3 ∨ h = 27 ∨ h = 54 ∨ h = 972 ∨
      h = 768 ∨ h = 248832) ∨
    (h = 180 ∨ h = 360 ∨ h = 58320 ∨
      h = 116640 ∨ h = 5120) ∨
    (h = 1200 ∨ h = 2400 ∨ h = 21600 ∨
      h = 388800 ∨ h = 777600) ∨
    (h = 144000 ∨ h = 46656000) at hcases
  have hmod :
      (13 * h) % 19 ≠ 1 := by
    simpa only [h] using
      five_point_stabilizer_card_mod_nineteen_ne_one
        X P hcard h5 hnotAlt s hs
  have hlarge :=
    five_point_stabilizer_card_not_five_exponent_three
      X P hcard h5 hnotAlt s hs
  change h ≠ 144000 ∧ h ≠ 46656000 at hlarge
  rcases hcases with
      (hthree | htwentySeven | hfiftyFour | hnineSeventyTwo |
        hsevenSixtyEight | htwoFortyEight) |
      (honeEighty | hthreeSixty | hfiftyEight |
        honeSixteen | hfiveThousand) |
      (htwelveHundred | htwentyFourHundred | htwentyOne |
        hthreeEightyEight | hsevenSeventySeven) |
      (honeFortyFour | hfortySixMillion)
  · rw [hthree] at hmod
    norm_num at hmod
  · exact Or.inl (Or.inl htwentySeven)
  · exact Or.inl (Or.inr (Or.inl hfiftyFour))
  · rw [hnineSeventyTwo] at hmod
    norm_num at hmod
  · exact Or.inl (Or.inr (Or.inr (Or.inl hsevenSixtyEight)))
  · exact Or.inl (Or.inr (Or.inr (Or.inr htwoFortyEight)))
  · exact Or.inr (Or.inl (Or.inl honeEighty))
  · exact Or.inr (Or.inl (Or.inr (Or.inl hthreeSixty)))
  · exact Or.inr (Or.inl (Or.inr (Or.inr (Or.inl hfiftyEight))))
  · exact Or.inr (Or.inl
      (Or.inr (Or.inr (Or.inr (Or.inl honeSixteen)))))
  · exact Or.inr (Or.inl
      (Or.inr (Or.inr (Or.inr (Or.inr hfiveThousand)))))
  · rw [htwelveHundred] at hmod
    norm_num at hmod
  · exact Or.inr (Or.inr (Or.inl htwentyFourHundred))
  · exact Or.inr (Or.inr (Or.inr (Or.inl htwentyOne)))
  · rw [hthreeEightyEight] at hmod
    norm_num at hmod
  · exact Or.inr (Or.inr (Or.inr (Or.inr hsevenSeventySeven)))
  · exact (hlarge.1 honeFortyFour).elim
  · exact (hlarge.2 hfortySixMillion).elim

end FiveTransitive.Degree20

end CFSG
