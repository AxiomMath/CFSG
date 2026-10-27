module

public import CFSG.Monster.Griess.Short
public import Certificates.Data.CFSGNative.MonsterAxis.Dense
public import Certificates.Data.CFSGNative.YGroups.Y443.MonsterWords
public import Mathlib.Algebra.Order.Algebra
public import Mathlib.Analysis.SpecialFunctions.Pow.NNReal

public section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.YGroups.Y443

open CFSG.Monster CFSG.Monster.AxisCount CFSG.Monster.Griess CFSG.YGroups.Y443Native

@[expose] def swap13Word : List Native.Gen :=
  [.tau, .tau, .rho (false, 2270, 3251), .tau, .rho (false, 1429, 256), .rho (false, 0, 1731),
   .rho (false, 0, 48),
   .perm #[2, 3, 5, 4, 9, 8, 14, 15, 6, 7, 1, 0, 13, 12, 10, 11, 22, 16, 23, 17, 18, 21, 20, 19],
   .xi, .xi, .rho (false, 0, 6),
   .perm #[0, 1, 3, 6, 2, 4, 5, 7, 8, 18, 12, 22, 21, 15, 17, 11, 14, 20, 10, 16, 19, 9, 23, 13],
   .tau, .tau, .xi, .xi, .rho (false, 0, 6),
   .perm #[0, 1, 3, 7, 2, 4, 6, 5, 8, 21, 16, 13, 15, 18, 23, 10, 17, 12, 9, 20, 22, 11, 14, 19],
   .xi, .rho (false, 0, 18),
   .perm #[2, 3, 8, 9, 17, 19, 23, 20, 0, 1, 10, 11, 18, 16, 22, 21, 13, 6, 12, 7, 15, 5, 4, 14],
   .tau, .xi, .xi, .rho (false, 0, 4),
   .perm #[0, 1, 8, 17, 2, 6, 20, 13, 3, 4, 14, 23, 7, 5, 18, 11, 22, 19, 9, 21, 15, 10, 12, 16],
   .xi, .tau, .xi, .xi, .rho (false, 0, 20),
   .perm #[0, 5, 10, 11, 1, 4, 14, 15, 2, 6, 17, 16, 7, 3, 21, 20, 22, 19, 12, 8, 23, 18, 9, 13],
   .xi, .xi, .rho (false, 0, 24),
   .perm #[3, 7, 11, 22, 15, 23, 16, 21, 14, 19, 1, 0, 8, 13, 18, 10, 5, 12, 6, 17, 20, 2, 4, 9],
   .xi, .xi, .tau, .tau, .xi, .rho (false, 0, 6),
   .perm #[0, 11, 2, 3, 1, 8, 9, 10, 4, 16, 14, 21, 19, 6, 20, 12, 23, 13, 17, 7, 15, 22, 5, 18],
   .xi, .tau, .tau, .xi]

end CFSG.YGroups.Y443
