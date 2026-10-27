module

public import Certificates.Data.CFSGNative.MonsterAxis.Dense

public section

namespace CFSG.Monster.Existence

open CFSG.Monster.AxisCount

@[expose] def fiCGamma : List Native.Gen :=
  [.sign 128, .rho (false, 0, 2623), .rho (false, 0, 50),
    .perm #[8, 22, 0, 1, 2, 5, 14, 16, 3, 6, 18, 12,
        20, 10, 7, 4, 23, 15, 13, 11, 21, 19, 9, 17]]

@[expose] def fiCDelta : List Native.Gen :=
  [.rho (false, 3112, 427), .rho (false, 0, 3011), .rho (false, 0, 24),
    .perm #[6, 18, 4, 5, 7, 16, 19, 17, 0, 11, 12, 21,
        9, 3, 22, 13, 20, 14, 8, 1, 15, 23, 2, 10],
    .xi, .xi, .rho (false, 0, 24),
    .perm #[0, 2, 17, 22, 1, 4, 12, 11, 3, 6, 9, 14,
        7, 5, 20, 19, 15, 21, 16, 13, 8, 18, 10, 23],
    .tau, .xi, .rho (false, 0, 20),
    .perm #[0, 2, 7, 21, 1, 10, 14, 17, 3, 9, 19, 15,
        11, 8, 22, 6, 12, 20, 4, 13, 18, 5, 16, 23]]

end CFSG.Monster.Existence
