module

public import CFSG.Permutation.FiveTransitive.SimpleGoursat
public import Mathlib.Algebra.Order.Ring.Star
public import Mathlib.GroupTheory.SpecificGroups.Alternating

public section

namespace CFSG

namespace FiveTransitive.FixedActionGoursat

open MulAction SubMulAction Subgroup

theorem alternatingGroup_le_of_card_eq_factorial_or_half
    (Y : Type) [Fintype Y] [DecidableEq Y]
    (Q : Subgroup (Equiv.Perm Y))
    (hfive : 5 ≤ Fintype.card Y)
    (hcard :
      Nat.card Q = (Fintype.card Y).factorial ∨
        Nat.card Q = (Fintype.card Y).factorial / 2) :
    alternatingGroup Y ≤ Q := by
  have hpermCard :
      Nat.card (Equiv.Perm Y) =
        (Fintype.card Y).factorial := by
    rw [Nat.card_perm, Nat.card_eq_fintype_card]
  rcases hcard with hfull | hhalf
  · have htop : Q = ⊤ :=
      Subgroup.eq_top_of_card_eq Q
        (hfull.trans hpermCard.symm)
    rw [htop]
    exact le_top
  · have htwoDvd :
        2 ∣ (Fintype.card Y).factorial :=
      Nat.dvd_factorial (by norm_num) (by omega)
    have heven :
        2 * ((Fintype.card Y).factorial / 2) =
          (Fintype.card Y).factorial :=
      Nat.mul_div_cancel' htwoDvd
    have hhalfPos :
        0 < (Fintype.card Y).factorial / 2 := by
      have hfactorialPos :=
        Nat.factorial_pos (Fintype.card Y)
      omega
    have hindexCard := Q.index_mul_card
    have hindex : Q.index = 2 := by
      apply Nat.eq_of_mul_eq_mul_right hhalfPos
      calc
        Q.index *
              ((Fintype.card Y).factorial / 2) =
            (Fintype.card Y).factorial := by
          calc
            Q.index *
                  ((Fintype.card Y).factorial / 2) =
                Nat.card (Equiv.Perm Y) := by
              simpa only [hhalf] using hindexCard
            _ = (Fintype.card Y).factorial :=
              hpermCard
        _ = 2 *
              ((Fintype.card Y).factorial / 2) :=
          heven.symm
    exact
      Equiv.Perm.alternatingGroup_le_of_index_le_two
        (by rw [hindex])

end FiveTransitive.FixedActionGoursat

end CFSG
