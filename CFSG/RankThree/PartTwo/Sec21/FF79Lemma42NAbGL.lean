module

public import CFSG.RankThree.Classical.SteinbergBJBinaryThreeSpaceFrobenius

public section

namespace CFSG.RankThree.PartTwo.Sec21.FF79.LemmaN

open CFSG.RankThree.Classical.GL3

@[expose] def klE1 : GL (Fin 3) (ZMod 2) :=
  ⟨!![1, 0, 0; 0, 1, 0; 1, 0, 1], !![1, 0, 0; 0, 1, 0; 1, 0, 1], by decide, by decide⟩

@[expose] def klE2 : GL (Fin 3) (ZMod 2) :=
  ⟨!![1, 0, 0; 1, 1, 0; 1, 0, 1], !![1, 0, 0; 1, 1, 0; 1, 0, 1], by decide, by decide⟩

@[expose] def klE3 : GL (Fin 3) (ZMod 2) :=
  ⟨!![1, 0, 0; 1, 1, 0; 0, 0, 1], !![1, 0, 0; 1, 1, 0; 0, 0, 1], by decide, by decide⟩

theorem frobS_mul_frobX : frobS * frobX = frobX * frobS ^ 4 := Units.ext (by decide)

theorem frob_order_three (i : ℕ) (hi : i < 7) :
    (frobX * frobS ^ i) ^ 3 = 1 ∧ frobX * frobS ^ i ≠ 1 := by
  interval_cases i <;>
    exact ⟨Units.ext (by decide), fun h => absurd (congrArg Units.val h) (by decide)⟩

theorem klE1_mul_klE1 : klE1 * klE1 = 1 := Units.ext (by decide)
theorem klE1_mul_klE2 : klE1 * klE2 = klE3 := Units.ext (by decide)
theorem klE1_mul_klE3 : klE1 * klE3 = klE2 := Units.ext (by decide)
theorem klE1_ne_one : klE1 ≠ 1 := fun h => absurd (congrArg Units.val h) (by decide)

theorem kl_sq_one : (frobX * klE1) ^ 2 = frobX ^ 2 * klE2 := Units.ext (by decide)
theorem kl_sq_two : (frobX * klE2) ^ 2 = frobX ^ 2 * klE3 := Units.ext (by decide)
theorem kl_sq_three : (frobX * klE3) ^ 2 = frobX ^ 2 * klE1 := Units.ext (by decide)

theorem kl_order_three_one : (frobX * klE1) ^ 3 = 1 ∧ frobX * klE1 ≠ 1 :=
  ⟨Units.ext (by decide), fun h => absurd (congrArg Units.val h) (by decide)⟩
theorem kl_order_three_two : (frobX * klE2) ^ 3 = 1 ∧ frobX * klE2 ≠ 1 :=
  ⟨Units.ext (by decide), fun h => absurd (congrArg Units.val h) (by decide)⟩
theorem kl_order_three_three : (frobX * klE3) ^ 3 = 1 ∧ frobX * klE3 ≠ 1 :=
  ⟨Units.ext (by decide), fun h => absurd (congrArg Units.val h) (by decide)⟩

end CFSG.RankThree.PartTwo.Sec21.FF79.LemmaN
