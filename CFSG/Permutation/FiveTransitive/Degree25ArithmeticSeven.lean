module

public import CFSG.Permutation.FiveTransitive.Degree25SevenFixedNormalizer

public section

namespace CFSG

namespace FiveTransitive.Degree25

open MulAction SubMulAction Subgroup

theorem five_point_stabilizer_card_cases_without_seven
    (X : Type) [Fintype X] [DecidableEq X]
    (P : Subgroup (Equiv.Perm X))
    (hcard : Fintype.card X = 25)
    (h5 : ∀ a b : Fin 5 → X, Function.Injective a →
      Function.Injective b →
      ∃ q : P, ∀ i, q • a i = b i)
    (hnotAlt : ¬alternatingGroup X ≤ P)
    (s : Set X) (hs : s.ncard = 5) :
    let h := Nat.card (fixingSubgroup P s)
    h = 270 ∨ h = 6480 ∨ h = 12000 ∨ h = 960 ∨
      h = 1944000 ∨ h = 288000 ∨ h = 23040 ∨
      h = 46656000 ∨ h = 552960 ∨ h = 1024000 ∨
      h = 81920 ∨ h = 165888000 := by
  classical
  dsimp
  let H : Subgroup P := fixingSubgroup P s
  let h := Nat.card H
  change
    h = 270 ∨ h = 6480 ∨ h = 12000 ∨ h = 960 ∨
      h = 1944000 ∨ h = 288000 ∨ h = 23040 ∨
      h = 46656000 ∨ h = 552960 ∨ h = 1024000 ∨
      h = 81920 ∨ h = 165888000
  have hcases :
      h = 270 ∨ h = 10206 ∨ h = 2800 ∨ h = 6480 ∨
      h = 12000 ∨ h = 960 ∨ h = 36288 ∨
      h = 1944000 ∨ h = 67200 ∨ h = 288000 ∨
      h = 23040 ∨ h = 870912 ∨ h = 46656000 ∨
      h = 552960 ∨ h = 1024000 ∨ h = 81920 ∨
      h = 3096576 ∨ h = 165888000 := by
    simpa only [H, h] using
      five_point_stabilizer_card_cases_transfer
        X P hcard h5 hnotAlt s hs
  have hnotSeven : ¬7 ∣ h := by
    simpa only [H, h] using
      seven_not_dvd_five_point_stabilizer
        X P hcard h5 hnotAlt s hs
  rcases hcases with
    hcase | hcase | hcase | hcase | hcase | hcase |
    hcase | hcase | hcase | hcase | hcase | hcase |
    hcase | hcase | hcase | hcase | hcase | hcase
  all_goals try norm_num [hcase] at hnotSeven
  all_goals norm_num [hcase]

end FiveTransitive.Degree25

end CFSG
