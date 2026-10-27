
module

public import CFSG.Assembly.LowTwoRankDefs
public import CFSG.Monster.B.Co2.BFS
public import CFSG.Monster.B.Short.Rootless
public import CFSG.Monster.B.TwoA.Base.CodeCheck
public import CFSG.Monster.VisQuot.Monomial
public import CFSG.Sporadic.Mathieu.Actions

public noncomputable section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.Monster.B.TwoA

open CFSG.Monster CFSG.Monster.Code CFSG.Monster.Lifts CFSG.Monster.Visible
  CFSG.Monster.VisQuot CFSG.Monster.ScalarKernel CFSG.Monster.SpinLattice
  CFSG.Monster.B.Short CFSG.Monster.B.Co2 CFSG.Monster.VisCert CFSG.Sporadic.Mathieu

@[expose] def pa7 : Fin 7 → Fin 24 := ![2, 4, 6, 8, 10, 12, 14]

@[expose] def pb7 : Fin 7 → Fin 24 := ![3, 5, 7, 9, 11, 13, 15]

@[expose] def sCoord : Fin 7 → ℕ := ![12288, 49152, 61440, 393216, 405504, 442368, 454656]

@[expose] def sel (t : ZMod 2) (m : ℕ) : ℕ := if t = 1 then m else 0

@[expose] def rCoord : Fin 7 → ℕ := ![49152, 196608, 258048, 1572864, 1634304, 1781760, 1818624]

@[expose] def xsel4 (c : Fin 4 → ZMod 2) : ℕ :=
  sel (c 0) 31 ^^^ sel (c 1) 12288 ^^^ sel (c 2) 49152 ^^^ sel (c 3) 393216

@[expose] def xsel3 (c : Fin 3 → ZMod 2) : ℕ :=
  sel (c 0) 31 ^^^ sel (c 1) 12288 ^^^ sel (c 2) 49152

end CFSG.Monster.B.TwoA
