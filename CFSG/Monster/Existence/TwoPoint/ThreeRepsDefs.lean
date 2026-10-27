module

public import CFSG.Monster.Existence.Defs
public import CFSG.Monster.AxisCount.DenseWord
public import CFSG.Monster.Generated.Centralizer

public section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.Monster.Existence

open CFSG.Monster CFSG.Monster.Griess CFSG.Monster.Generated CFSG.Monster.AxisCount

@[expose] def wordThreeA : List Native.Gen :=
  [.sign 2002, .rho (true, 805, 1925), .rho (false, 0, 856), .rho (false, 0, 42),
    .perm #[23, 8, 13, 15, 7, 14, 19, 3, 22, 1, 0, 11, 21, 18, 10, 16, 4, 12, 2, 17, 9, 20, 5, 6],
    .xi, .xi, .rho (false, 0, 14),
    .perm #[0, 5, 12, 13, 1, 4, 8, 9, 2, 6, 23, 22, 7, 3, 19, 18, 16, 21, 10, 14, 17, 20, 15, 11],
    .xi, .rho (false, 0, 4),
    .perm #[1, 3, 6, 9, 7, 22, 10, 21, 18, 20, 2, 15, 16, 5, 8, 17, 0, 19, 13, 23, 11, 14, 12, 4],
    .xi, .xi]

@[expose] def wordThreeC : List Native.Gen :=
  [.sign 586, .rho (false, 3361, 64), .rho (false, 0, 3869), .rho (false, 0, 2),
    .perm #[14, 22, 8, 11, 6, 10, 1, 17, 20, 15, 5, 7, 4, 9, 18, 0, 12, 3, 23, 2, 13, 19, 16, 21],
    .xi, .xi, .rho (false, 0, 2),
    .perm #[0, 6, 8, 9, 1, 7, 15, 14, 2, 5, 18, 19, 4, 3, 21, 20, 22, 16, 13, 10, 23, 17, 11, 12],
    .xi, .xi, .rho (false, 0, 6),
    .perm #[8, 11, 13, 22, 14, 16, 19, 21, 1, 15, 0, 23, 18, 3, 10, 7, 5, 17, 2, 9, 12, 4, 20, 6],
    .xi, .rho (false, 0, 6),
    .perm #[0, 1, 3, 7, 2, 4, 6, 5, 8, 21, 16, 13, 15, 18, 23, 10, 17, 12, 9, 20, 22, 11, 14, 19]]

@[expose] noncomputable def threeARep : MGriess :=
  ⟨wordLin wordThreeA, Gmat_le_AutO (wordLin_mem_Gmat wordThreeA)⟩

@[expose] noncomputable def threeCRep : MGriess :=
  ⟨wordLin wordThreeC, Gmat_le_AutO (wordLin_mem_Gmat wordThreeC)⟩

end CFSG.Monster.Existence
