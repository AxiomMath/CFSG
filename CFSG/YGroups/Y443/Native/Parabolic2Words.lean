module

public import CFSG.YGroups.Y443.Native.Align

public section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.YGroups.Y443

open CFSG.Monster CFSG.Monster.AxisCount CFSG.Monster.Griess CFSG.YGroups.Y443Native

@[expose] def armSwapL (s : ℕ) : ℕ :=
  if 1 ≤ s ∧ s ≤ 4 then s + 4 else if 5 ≤ s ∧ s ≤ 8 then s - 4 else s

@[expose] def sletP : List ℕ := slet.map armSwapL

@[expose] def rhoGens : List ℕ := [1, 2, 3, 4, 9, 10, 11]

@[expose] def rhoWord : List Native.Gen :=
  [.tau, .tau, .rho (false, 1351, 48), .tau, .rho (true, 6, 57), .rho (false, 0, 63),
   .rho (false, 0, 48),
   .perm #[7, 4, 6, 5, 15, 12, 14, 13, 11, 8, 10, 9, 3, 0, 2, 1, 16, 17, 18, 19, 20, 22, 23, 21],
   .xi, .xi, .rho (false, 0, 2),
   .perm #[0, 4, 8, 12, 1, 5, 9, 13, 2, 6, 10, 14, 3, 7, 11, 15, 20, 17, 18, 19, 16, 21, 23, 22],
   .xi, .xi]

@[expose] def mWord : List Native.Gen :=
  [.tau, .tau, .rho (false, 2195, 3274), .tau, .rho (true, 596, 3072), .rho (false, 0, 1871),
   .rho (false, 0, 38),
   .perm #[23, 17, 3, 2, 21, 18, 14, 15, 10, 6, 1, 12, 11, 7, 13, 0, 19, 20, 9, 8, 22, 16, 4, 5],
   .xi, .xi, .rho (false, 0, 0),
   .perm #[0, 1, 3, 4, 2, 5, 6, 7, 8, 14, 23, 17, 16, 22, 15, 9, 20, 18, 11, 13, 12, 10, 19, 21],
   .xi, .xi, .rho (false, 0, 0),
   .perm #[4, 6, 13, 15, 16, 19, 23, 22, 0, 11, 2, 9, 1, 8, 10, 3, 5, 7, 12, 14, 18, 17, 20, 21],
   .tau, .xi, .rho (false, 0, 60),
   .perm #[0, 4, 6, 7, 1, 2, 5, 3, 8, 18, 23, 13, 21, 15, 10, 16, 12, 22, 19, 9, 17, 11, 14, 20],
   .xi, .xi, .rho (false, 0, 48),
   .perm #[0, 1, 5, 7, 12, 15, 22, 21, 2, 3, 6, 4, 13, 14, 23, 20, 17, 8, 18, 11, 16, 10, 9, 19],
   .tau, .tau, .xi, .xi, .rho (false, 0, 2),
   .perm #[0, 6, 20, 21, 1, 7, 19, 18, 2, 5, 14, 15, 4, 3, 9, 8, 10, 12, 17, 22, 11, 13, 23, 16],
   .xi, .rho (false, 0, 50),
   .perm #[8, 9, 12, 23, 13, 19, 22, 18, 3, 21, 15, 1, 5, 10, 16, 2, 14, 4, 7, 20, 17, 6, 0, 11],
   .tau, .xi, .rho (false, 0, 48),
   .perm #[0, 3, 9, 11, 1, 2, 10, 8, 4, 5, 17, 19, 6, 7, 18, 16, 12, 13, 22, 21, 14, 15, 23, 20],
   .tau, .xi, .xi, .rho (false, 0, 20),
   .perm #[0, 5, 10, 11, 1, 4, 14, 15, 2, 6, 17, 16, 7, 3, 21, 20, 22, 19, 12, 8, 23, 18, 9, 13],
   .xi, .xi, .rho (false, 0, 44),
   .perm #[8, 10, 13, 17, 15, 22, 20, 19, 7, 23, 1, 9, 12, 6, 18, 5, 3, 14, 2, 16, 21, 0, 11, 4],
   .tau, .tau, .xi, .xi, .rho (false, 0, 20),
   .perm #[0, 5, 10, 11, 1, 4, 14, 15, 2, 6, 17, 16, 7, 3, 21, 20, 22, 19, 12, 8, 23, 18, 9, 13],
   .xi, .xi, .rho (false, 0, 0),
   .perm #[9, 10, 12, 15, 17, 23, 18, 20, 8, 13, 14, 11, 1, 7, 2, 4, 16, 21, 22, 19, 0, 3, 5, 6]]

@[expose] def qWord : List Native.Gen :=
  [.tau, .tau, .rho (false, 3817, 64), .tau, .rho (true, 3555, 3136), .rho (false, 0, 257),
   .rho (false, 0, 36),
   .perm #[3, 0, 4, 7, 2, 6, 1, 5, 15, 8, 11, 12, 23, 16, 19, 20, 14, 9, 10, 13, 22, 17, 18, 21],
   .xi, .xi, .rho (false, 0, 0),
   .perm #[0, 1, 3, 4, 2, 5, 6, 7, 8, 14, 23, 17, 16, 22, 15, 9, 20, 18, 11, 13, 12, 10, 19, 21],
   .xi, .xi, .rho (false, 0, 12),
   .perm #[0, 1, 3, 7, 9, 12, 20, 17, 2, 6, 5, 4, 16, 21, 13, 8, 14, 22, 11, 19, 23, 10, 15, 18],
   .xi, .xi, .tau, .xi, .xi, .rho (false, 0, 0),
   .perm #[0, 1, 3, 4, 2, 5, 6, 7, 8, 14, 23, 17, 16, 22, 15, 9, 20, 18, 11, 13, 12, 10, 19, 21],
   .xi, .xi, .rho (false, 0, 46),
   .perm #[0, 2, 3, 6, 10, 13, 18, 21, 1, 4, 7, 5, 23, 16, 15, 8, 12, 19, 11, 20, 17, 9, 14, 22]]

@[expose] def mtmWord : List Native.Gen := mWord ++ tWord ++ mWord

@[expose] def zmWord : List Native.Gen := mtmWord ++ tWord

end CFSG.YGroups.Y443
