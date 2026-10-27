
module

public import CFSG.YGroups.Y443.Native.EdgeNoncommInputs

public section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.YGroups.Y443

open CFSG.Monster CFSG.Monster.AxisCount CFSG.Monster.Griess CFSG.YGroups.Y443Native

@[expose] def coverPHat : List Native.Gen :=
  [.tau, .tau, .rho (false, 1676, 1356), .tau, .rho (true, 1142, 643), .rho (false, 0, 1589),
   .rho (false, 0, 50),
   .perm #[7, 17, 1, 0, 16, 22, 6, 23, 4, 15, 13, 19, 20, 12, 9, 3, 5, 8, 11, 18, 21, 10, 14, 2],
   .xi, .rho (false, 0, 2),
   .perm #[0, 4, 8, 12, 1, 5, 9, 13, 2, 6, 10, 14, 3, 7, 11, 15, 20, 17, 18, 19, 16, 21, 23, 22],
   .tau, .xi, .xi, .rho (false, 0, 48),
   .perm #[0, 4, 17, 21, 1, 5, 16, 20, 2, 6, 19, 23, 3, 7, 18, 22, 13, 8, 11, 10, 9, 12, 14, 15],
   .tau, .xi, .rho (false, 0, 12),
   .perm #[15, 23, 2, 3, 0, 6, 16, 8, 1, 4, 11, 19, 20, 12, 7, 5, 21, 18, 17, 14, 22, 9, 13, 10]]

@[expose] def coverQHat : List Native.Gen :=
  [.tau, .tau, .rho (false, 3353, 3681), .tau, .rho (false, 3957, 3146), .rho (false, 0, 4053),
   .rho (false, 0, 30),
   .perm #[4, 9, 10, 11, 6, 7, 5, 8, 15, 3, 18, 21, 23, 17, 2, 14, 1, 13, 22, 19, 16, 20, 12, 0],
   .xi, .rho (false, 0, 34),
   .perm #[0, 7, 18, 19, 1, 6, 20, 21, 2, 4, 10, 11, 5, 3, 12, 13, 15, 8, 22, 16, 14, 9, 17, 23],
   .xi, .rho (false, 0, 42),
   .perm #[0, 3, 5, 21, 6, 22, 19, 16, 7, 20, 11, 10, 15, 13, 23, 4, 8, 12, 2, 17, 18, 1, 9, 14],
   .tau, .xi, .rho (false, 0, 24),
   .perm #[0, 4, 10, 11, 1, 5, 15, 14, 2, 7, 19, 18, 6, 3, 22, 23, 21, 17, 13, 8, 20, 16, 9, 12],
   .xi, .xi, .rho (false, 0, 30),
   .perm #[0, 3, 9, 23, 11, 20, 15, 14, 5, 7, 8, 22, 21, 10, 16, 17, 2, 12, 4, 18, 6, 19, 13, 1],
   .tau, .xi, .rho (false, 0, 0),
   .perm #[0, 3, 13, 15, 1, 2, 14, 12, 4, 5, 21, 23, 6, 7, 22, 20, 8, 9, 18, 17, 10, 11, 19, 16],
   .tau, .xi, .rho (false, 0, 24),
   .perm #[0, 4, 10, 11, 1, 5, 15, 14, 2, 7, 19, 18, 6, 3, 22, 23, 21, 17, 13, 8, 20, 16, 9, 12],
   .xi, .xi, .rho (false, 0, 52),
   .perm #[8, 10, 12, 19, 14, 23, 17, 21, 0, 11, 22, 5, 7, 16, 13, 4, 20, 1, 6, 9, 15, 2, 3, 18],
   .tau, .xi, .rho (false, 0, 6),
   .perm #[0, 6, 2, 3, 1, 4, 7, 5, 8, 16, 23, 15, 19, 11, 12, 20, 14, 22, 17, 9, 21, 13, 10, 18]]

@[expose] def coverWy : List Native.Gen :=
  [.tau, .tau, .rho (false, 1381, 560), .tau, .rho (false, 3044, 868), .rho (false, 0, 1541),
   .rho (false, 0, 54),
   .perm #[2, 4, 6, 5, 0, 1, 3, 7, 11, 22, 19, 14, 12, 17, 20, 9, 21, 8, 13, 16, 18, 15, 10, 23],
   .xi, .rho (false, 0, 6),
   .perm #[0, 1, 2, 6, 3, 4, 7, 5, 8, 17, 20, 13, 14, 23, 18, 11, 21, 12, 9, 16, 19, 10, 15, 22],
   .xi, .xi, .rho (false, 0, 4),
   .perm #[2, 4, 8, 9, 11, 12, 21, 19, 0, 17, 7, 16, 22, 1, 6, 23, 14, 15, 5, 3, 18, 20, 10, 13],
   .tau, .tau, .xi, .xi, .rho (false, 0, 38),
   .perm #[0, 8, 10, 13, 1, 14, 19, 18, 2, 5, 15, 7, 22, 16, 6, 9, 12, 20, 3, 23, 21, 11, 4, 17],
   .tau, .xi, .rho (false, 0, 6),
   .perm #[0, 6, 2, 3, 1, 4, 7, 5, 8, 16, 23, 15, 19, 11, 12, 20, 14, 22, 17, 9, 21, 13, 10, 18]]

@[expose] def coverQ : List Native.Gen := EdgeNoncomm.gL 3 ++ EdgeNoncomm.gI 4

end CFSG.YGroups.Y443
