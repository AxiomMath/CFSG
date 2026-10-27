module

public import CFSG.RankThree.PartTwo.Sec4.RonanK429RowETools

public section

namespace CFSG.RankThree.PartTwo.Sec4.RonanK429E

open CFSG
open scoped Matrix

variable {ι R : Type*} [Fintype ι] [DecidableEq ι] [CommRing R]

theorem commute_sum_pow {y X : Matrix ι ι R} (hX : X * y = y * X) (n : ℕ) :
    X * (∑ i : Fin n, y ^ (i : ℕ)) = (∑ i : Fin n, y ^ (i : ℕ)) * X := by
  rw [Finset.mul_sum, Finset.sum_mul]
  exact Finset.sum_congr rfl fun i _ => (Commute.pow_right hX i).eq

end CFSG.RankThree.PartTwo.Sec4.RonanK429E
