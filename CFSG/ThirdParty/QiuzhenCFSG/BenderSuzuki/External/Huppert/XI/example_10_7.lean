module

public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.MatrixGroups.Suzuki
import Mathlib.Tactic.Group

namespace CFSG
end CFSG
open CFSG

/-!
# Huppert-Blackburn XI.10.7

The two structure equations follow Volume III, physical page 268.  Part (b)
is transposed into the upper-triangular Suzuki convention used in this repo;
this reverses the conjugating product on the right-hand side.
-/

namespace CFSG.BenderSuzuki
namespace External

open _root_.CFSG.BenderSuzuki.MatrixGroups PFAppendixIII


/-- Huppert-Blackburn XI.10.7(b), the `Sz(q)` structure equation. -/
public theorem huppert_blackburn_XI_example_10_7_b (m : ℕ) (hm : 0 < m) :
    let j := SuzukiRootGL m 0 1
    let g := SuzukiRootGL m 1 0
    let T := SuzukiWeylGL m
    T * j * T = g⁻¹ * T * g ∧ g ^ 2 = j := by
  have _hm := hm
  dsimp
  have hchar : (1 + 1 : BinaryGaloisField (2 * m + 1)) = 0 :=
    CharTwo.add_self_eq_zero 1
  constructor
  · have hmul :
        SuzukiRootGL m 1 0 *
              (SuzukiWeylGL m * SuzukiRootGL m 0 1 * SuzukiWeylGL m) =
            SuzukiWeylGL m * SuzukiRootGL m 1 0 := by
      ext i j
      fin_cases i <;> fin_cases j <;>
        simp [SuzukiRootGL, SuzukiRootMatrix, SuzukiWeylGL,
          SuzukiWeylMatrix, Matrix.mul_apply, Fin.sum_univ_four, hchar]
    calc
      SuzukiWeylGL m * SuzukiRootGL m 0 1 * SuzukiWeylGL m =
          (SuzukiRootGL m 1 0)⁻¹ *
            (SuzukiRootGL m 1 0 *
              (SuzukiWeylGL m * SuzukiRootGL m 0 1 * SuzukiWeylGL m)) := by
            group
      _ = (SuzukiRootGL m 1 0)⁻¹ *
            (SuzukiWeylGL m * SuzukiRootGL m 1 0) := by rw [hmul]
      _ = (SuzukiRootGL m 1 0)⁻¹ * SuzukiWeylGL m *
            SuzukiRootGL m 1 0 := by group
  · ext i j
    fin_cases i <;> fin_cases j <;>
      simp [SuzukiRootGL, SuzukiRootMatrix, Matrix.mul_apply,
        Fin.sum_univ_four, pow_two, hchar]

end External
end CFSG.BenderSuzuki
