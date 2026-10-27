module

public import CFSG.LocalAnalysis.AGLEmbeddingD2.Ambient
public import CFSG.LocalAnalysis.SeitzReduction.EPilotPosition
public import CFSG.LocalAnalysis.StandardType.GGQTwoLocalDefs

public section
namespace CFSG.StandardType.QTwo

theorem qTwoGlobGrw_ratio {d : ℕ} (hd : 3 ≤ d) : 3 * (d + 2) ≤ 3 ^ d := by
  induction d, hd using Nat.le_induction with
  | base => norm_num
  | succ d hd ih =>
    calc 3 * (d + 1 + 2) ≤ 3 * (3 * (d + 2)) := by omega
      _ ≤ 3 * 3 ^ d := Nat.mul_le_mul_left 3 ih
      _ = 3 ^ (d + 1) := by rw [pow_succ]; ring

theorem qTwoGlobGrw_order {d : ℕ} (hd : 7 ≤ d) :
    16 * 3 ^ d * (d + 1).factorial < 3 ^ (d * (d - 1) / 2) := by
  induction d, hd using Nat.le_induction with
  | base => norm_num [Nat.factorial]
  | succ d hd ih =>
    rw [Nat.triangle_succ]
    calc 16 * 3 ^ (d + 1) * (d + 1 + 1).factorial
        = (16 * 3 ^ d * (d + 1).factorial) * (3 * (d + 2)) := by
          rw [Nat.factorial_succ, pow_succ]
          ring
      _ < 3 ^ (d * (d - 1) / 2) * (3 * (d + 2)) :=
          Nat.mul_lt_mul_of_pos_right ih (by positivity)
      _ ≤ 3 ^ (d * (d - 1) / 2) * 3 ^ d :=
          Nat.mul_le_mul_left _ (qTwoGlobGrw_ratio (by omega))
      _ = 3 ^ (d * (d - 1) / 2 + d) := (pow_add _ _ _).symm

theorem qTwoGlobGrw_excl {d m a : ℕ} (hd : 7 ≤ d) (hm : m ≤ d + 1)
    (hupper : a ≤ 3 ^ d * 2 * m.factorial)
    (hlower : 3 ^ (d * (d - 1) / 2) ≤ 8 * a) : False := by
  have hf := Nat.factorial_le hm
  have hu : a ≤ 3 ^ d * 2 * (d + 1).factorial :=
    le_trans hupper (Nat.mul_le_mul_left _ hf)
  have hg := qTwoGlobGrw_order hd
  nlinarith

theorem qTwoGlobGrw_sl_order {d : ℕ} (hd : 5 ≤ d) :
    2 * 3 ^ d * d.factorial < 3 ^ (d * (d - 1) / 2) := by
  induction d, hd using Nat.le_induction with
  | base => norm_num [Nat.factorial]
  | succ d hd ih =>
    rw [Nat.triangle_succ]
    calc 2 * 3 ^ (d + 1) * (d + 1).factorial
        = (2 * 3 ^ d * d.factorial) * (3 * (d + 1)) := by
          rw [Nat.factorial_succ, pow_succ]
          ring
      _ < 3 ^ (d * (d - 1) / 2) * (3 * (d + 1)) :=
          Nat.mul_lt_mul_of_pos_right ih (by positivity)
      _ ≤ 3 ^ (d * (d - 1) / 2) * 3 ^ d := by
          apply Nat.mul_le_mul_left
          exact le_trans (by omega) (qTwoGlobGrw_ratio (by omega))
      _ = 3 ^ (d * (d - 1) / 2 + d) := (pow_add _ _ _).symm

end CFSG.StandardType.QTwo
end
