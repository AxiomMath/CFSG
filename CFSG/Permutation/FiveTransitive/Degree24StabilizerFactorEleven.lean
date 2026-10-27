module

public import CFSG.Permutation.FiveTransitive.Degree24SylowEleven

public section

namespace CFSG

namespace FiveTransitive.Degree24

open MulAction SubMulAction Subgroup

theorem five_point_stabilizer_card_dvd_without_eleven
    (X : Type) [Fintype X] [DecidableEq X]
    (P : Subgroup (Equiv.Perm X))
    (hcard : Fintype.card X = 24)
    (h5 : ∀ a b : Fin 5 → X, Function.Injective a →
      Function.Injective b →
      ∃ q : P, ∀ i, q • a i = b i)
    (hnotAlt : ¬alternatingGroup X ≤ P)
    (s : Set X) (hs : s.ncard = 5) :
    Nat.card (fixingSubgroup P s) ∣ 2633637888000 := by
  let H : Subgroup P := fixingSubgroup P s
  have hdiv : Nat.card H ∣ 28970016768000 := by
    simpa only [H] using
      five_point_stabilizer_card_dvd_reduced
        X P hcard h5 hnotAlt s hs
  have hnotEleven : ¬11 ∣ Nat.card H := by
    simpa only [H] using
      eleven_not_dvd_five_point_stabilizer_of_not_alternating
        X P hcard h5 hnotAlt s hs
  have hcoprime : Nat.Coprime (Nat.card H) 11 :=
    ((show Nat.Prime 11 by norm_num).coprime_iff_not_dvd.mpr
      hnotEleven).symm
  apply hcoprime.dvd_of_dvd_mul_left
  norm_num at hdiv ⊢
  exact hdiv

end FiveTransitive.Degree24

end CFSG
