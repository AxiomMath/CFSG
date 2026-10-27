
module

public import CFSG.Monster.Existence.TwoPoint.GammaExclTwoBCheckBase

public section

namespace CFSG.Monster.Existence

open CFSG.Monster.AxisCount

@[expose] def fiWT2 : List Native.Gen := fiWU[8]! ++ fiWU[0]!

@[expose] def fiCT2 : List Native.Gen :=
  [.rho (false, 0, 3136), .rho (false, 0, 50),
    .perm #[11, 22, 0, 1, 2, 4, 12, 17, 3, 7, 19, 14,
        20, 9, 6, 5, 23, 13, 15, 8, 21, 18, 10, 16]]

@[expose] def fiCT2Alpha : List Native.Gen :=
  [.tau, .xi, .rho (false, 0, 6),
    .perm #[0, 1, 2, 5, 3, 4, 6, 7, 8, 14, 16, 22,
        23, 17, 15, 9, 18, 20, 10, 12, 13, 11, 21, 19],
    .xi, .xi, .rho (false, 0, 32),
    .perm #[0, 5, 10, 15, 16, 20, 22, 23, 1, 4, 11, 14,
        21, 17, 18, 19, 2, 13, 7, 8, 3, 9, 12, 6],
    .tau, .tau, .xi, .xi,
    .perm #[12, 14, 2, 3, 0, 1, 15, 13, 4, 7, 19, 17,
        16, 18, 5, 6, 21, 20, 10, 9, 11, 8, 23, 22]]

@[expose, noinline] def fiT2ConjCheck : Bool :=
  fiEqP (fiRhoT ++ fiCT2) (fiCT2 ++ fiWT2) (HS.pw fiRhoT ++ HS.pw fiCT2)
    (HS.pw fiCT2 ++ HS.pw fiWT2)

@[expose, noinline] def fiT2AlphaConjCheck : Bool :=
  fiEqP (gxXWord ++ fiCT2Alpha) (fiCT2Alpha ++ (fiWT2 ++ fiWAlpha))
    (HS.pw gxXWord ++ HS.pw fiCT2Alpha) (HS.pw fiCT2Alpha ++ (HS.pw fiWT2 ++ HS.pw fiWAlpha))

end CFSG.Monster.Existence
