module

public import Certificates.Data.CFSGNative.MonsterAxis.Dense

public section

namespace CFSG.Monster.Existence

open CFSG.Monster.AxisCount

@[expose] def fiCAlphaGamma : List Native.Gen :=
  [.rho (false, 128, 57), .rho (false, 0, 1536), .rho (false, 0, 30),
    .perm #[3, 20, 0, 1, 2, 21, 22, 23, 4, 18, 13, 11,
        19, 5, 8, 15, 9, 12, 17, 7, 14, 10, 6, 16],
    .xi, .xi, .rho (false, 0, 42),
    .perm #[0, 5, 10, 15, 1, 4, 11, 14, 2, 7, 8, 13,
        3, 6, 9, 12, 21, 17, 18, 19, 16, 20, 22, 23],
    .tau, .tau, .xi, .xi,
    .perm #[12, 14, 2, 3, 0, 1, 15, 13, 4, 7, 19, 17,
        16, 18, 5, 6, 21, 20, 10, 9, 11, 8, 23, 22]]

end CFSG.Monster.Existence
