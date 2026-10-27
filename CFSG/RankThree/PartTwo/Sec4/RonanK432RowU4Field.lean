module

public import CFSG.RankThree.PartTwo.Sec4.RonanK432RowU4FieldOuter
public import CFSG.RankThree.PartTwo.Sec4.RonanK432RowU4DiagWitness
public import CFSG.RankThree.PartTwo.Sec4.RonanK432RowSU4W

public section

namespace CFSG.RankThree.PartTwo.Sec4.RonanK432

open CFSG.Assembly.RankThreeEven (projSU)

theorem listRow_projSU_four_two {m : ℕ} (hm : 1 ≤ m) : ListRow (projSU 4 2 m) := by
  obtain ⟨k, hk | hk⟩ := Nat.even_or_odd' m
  · subst hk
    refine listRow_projSU_four_of_dvd (p := 2) (f := 2 * k) hm ?_
    have h4 : 2 ^ (2 * k) % 3 = 1 := by
      rw [pow_mul, Nat.pow_mod]
      norm_num
    have h1 : 1 ≤ 2 ^ (2 * k) := Nat.one_le_pow _ _ (by norm_num)
    omega
  · subst hk
    refine listRow_projSU_four_of_dvd_succ (p := 2) (f := 2 * k + 1) hm ?_
    have h4 : 2 ^ (2 * k + 1) % 3 = 2 := by
      rw [pow_succ, pow_mul, Nat.mul_mod, Nat.pow_mod]
      norm_num
    omega

theorem rowOf_projSU_four_two_of_listRow {n : ℕ} (hn : 1 ≤ n) (hL : ListRow (projSU 4 2 n)) :
    RowOf (projSU 4 2 n) := by
  intro S _ _ _ _ ⟨e⟩
  exact GoodRow.of_mulEquiv e.symm ⟨hL, outerRow_projSU_four_two_all hn⟩

theorem rowOf_seven_SU4 : ∀ n : ℕ, 1 ≤ n → RowOf (projSU 4 2 n) := fun n hn =>
  rowOf_projSU_four_two_of_listRow hn (listRow_projSU_four_two hn)

end CFSG.RankThree.PartTwo.Sec4.RonanK432
