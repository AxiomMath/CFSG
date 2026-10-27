module

public import Certificates.Data.CFSGNative.MonsterAxis.Dense

public section

namespace CFSG.Monster.Existence

open CFSG.Monster.AxisCount

@[expose] def hnCW : List Native.Gen :=
  [.sign 1537, .rho (true, 367, 883), .rho (false, 0, 3410), .rho (false, 0, 6),
    .perm #[7, 6, 15, 14, 2, 3, 10, 11, 13, 12, 5, 4,
        8, 9, 0, 1, 22, 19, 21, 17, 18, 23, 20, 16],
    .tau, .tau, .xi, .xi, .rho (false, 0, 2),
    .perm #[0, 6, 8, 9, 1, 7, 15, 14, 2, 5, 18, 19,
        4, 3, 21, 20, 22, 16, 13, 10, 23, 17, 11, 12],
    .xi, .xi, .rho (false, 0, 14),
    .perm #[4, 7, 8, 15, 9, 21, 13, 22, 0, 11, 12, 3,
        1, 23, 5, 16, 14, 18, 17, 10, 6, 2, 19, 20],
    .tau, .xi, .xi, .rho (false, 0, 2),
    .perm #[0, 1, 8, 16, 2, 5, 22, 14, 3, 7, 13, 21,
        4, 6, 19, 11, 20, 18, 9, 23, 12, 10, 15, 17],
    .tau, .xi, .xi, .rho (false, 0, 2),
    .perm #[0, 4, 12, 21, 1, 3, 10, 19, 2, 7, 20, 13,
        5, 6, 18, 11, 23, 8, 22, 16, 14, 17, 9, 15],
    .xi]

end CFSG.Monster.Existence
