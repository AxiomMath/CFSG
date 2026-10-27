module

public import CFSG.RankThree.PartTwo.Sec21.FF79GL33Code
public import CFSG.Assembly.LowTwoRankDefs
public import CFSG.Assembly.RankThreeEvenDefs

public section

namespace CFSG.RankThree.PartTwo.Sec21.FF79.GL33

@[expose] def e0 : Vec := ![1, 0, 0]

@[expose] def e1 : Vec := ![0, 1, 0]

@[expose] def e2 : Vec := ![0, 0, 1]

theorem decV_one : decV 1 = e0 := by
  funext j; fin_cases j <;> decide

theorem decV_three : decV 3 = e1 := by
  funext j; fin_cases j <;> decide

theorem decV_nine : decV 9 = e2 := by
  funext j; fin_cases j <;> decide

theorem decV_two : decV 2 = -e0 := by
  funext j; fin_cases j <;> decide

theorem decV_zero_coord (r : ℕ) : decV r 0 = ((r % 3 : ℕ) : ZMod 3) := rfl

theorem decV_coord0_eq_zero {r : ℕ} : decV r 0 = 0 ↔ r % 3 = 0 := by
  rw [decV_zero_coord]
  constructor
  · intro h
    have := congrArg ZMod.val h
    rw [ZMod.val_natCast, ZMod.val_zero] at this
    simpa using this
  · intro h
    rw [h]; rfl

theorem negV_lt (r : ℕ) : negV r < 27 := by
  unfold negV; omega

theorem decV_negV (r : ℕ) : decV (negV r) = - decV r := by
  have h2 : (2 : ZMod 3) = -1 := by decide
  have h := decV_digits (d₀ := (2 * (r % 3)) % 3) (d₁ := (2 * ((r / 3) % 3)) % 3)
    (d₂ := (2 * ((r / 9) % 3)) % 3) (by omega) (by omega) (by omega)
  unfold negV
  rw [h]
  funext j
  fin_cases j
  all_goals simp [decV, ZMod.natCast_mod, Nat.cast_mul, h2]
  all_goals exact neg_one_mul _

theorem mem_span_e12 {u : Vec} :
    u ∈ Submodule.span (ZMod 3) {e1, e2} ↔ u 0 = 0 := by
  rw [Submodule.mem_span_pair]
  constructor
  · rintro ⟨a, b, rfl⟩
    simp [e1, e2]
  · intro h
    refine ⟨u 1, u 2, ?_⟩
    funext j
    fin_cases j <;> simp [e1, e2, h]

end CFSG.RankThree.PartTwo.Sec21.FF79.GL33

end
