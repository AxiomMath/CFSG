module

public import CFSG.Monster.Existence.Census.Rigid
public import CFSG.Monster.Existence.Census.TrialityWitnessesInputs

public section

namespace CFSG.Monster.Existence.Census

open CFSG.Monster CFSG.Monster.B CFSG.Monster.Code CFSG.Monster.Spin CFSG.Monster.SpinLattice
  CFSG.Monster.ScalarKernel CFSG.Monster.Griess CFSG.Monster.Visible CFSG.Monster.Generated
  CFSG.Monster.AxisCount CFSG.Monster.B.TwoA.Census Matrix
open CFSG.Monster.B.Rep4371 hiding interp interp_eq_sum

@[expose] def fusGens : List Native.Gen :=
  [Native.Gen.sign 1, Native.Gen.sign 4, Native.Gen.sign 64, Native.Gen.sign 128,
    Native.Gen.perm #[1, 0, 3, 2, 4, 5, 6, 7, 10, 11, 8, 9, 15, 14, 13, 12, 17, 16, 19, 18, 20, 21,
      22, 23],
    Native.Gen.perm #[0, 1, 3, 2, 5, 4, 6, 7, 15, 14, 12, 13, 10, 11, 9, 8, 16, 17, 19, 18, 21, 20,
      22, 23],
    Native.Gen.perm #[0, 1, 2, 3, 5, 4, 7, 6, 11, 10, 9, 8, 14, 15, 12, 13, 17, 16, 19, 18, 20, 21,
      22, 23],
    Native.Gen.perm #[2, 3, 0, 1, 4, 5, 6, 7, 11, 10, 9, 8, 13, 12, 15, 14, 18, 19, 16, 17, 20, 21,
      22, 23],
    Native.Gen.perm #[2, 4, 0, 6, 1, 7, 3, 5, 21, 19, 23, 17, 22, 16, 20, 18, 13, 11, 15, 9, 14, 8,
      12, 10],
    Native.Gen.perm #[1, 7, 2, 3, 5, 6, 4, 0, 8, 22, 17, 15, 19, 13, 10, 20, 16, 14, 9, 23, 11, 21,
      18, 12],
    Native.Gen.xi]

@[expose] def fusShifts : List Model.Pauli :=
  [(false, 0, 0), (true, 63, 0), (true, 63, 0), (true, 63, 0), (true, 63, 0), (true, 63, 0),
    (true, 63, 0), (true, 63, 0), (false, 0, 0), (false, 0, 0), (false, 60, 0)]

@[expose] def fusGen (j : ℕ) : Native.Gen := fusGens.getD j Native.Gen.xi

@[expose] def fusShift (j : ℕ) : Model.Pauli := fusShifts.getD j (false, 0, 0)

@[expose, noinline] def fusCheckC (c : Native.Ctx) (lo hi : ℕ) : Bool :=
  (List.range hi).all fun j => decide (j < lo) ||
    checkRigid c ([Native.Gen.sign 3, Native.Gen.perm idArr] ++ [fusGen j])
      ([fusGen j, Native.Gen.rho (fusShift j)] ++ [Native.Gen.sign 3, Native.Gen.perm idArr])

end CFSG.Monster.Existence.Census
