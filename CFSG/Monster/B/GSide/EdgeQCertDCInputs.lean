module

public import CFSG.Monster.B.GSide.EdgeQCertOrbits
public import CFSG.Monster.B.GSide.EdgeQCertP2
public meta import CFSG.Monster.B.TwoA.Unitary.NData
public meta import Certificates.Data.CFSGNative.MonsterB.Co2Data
public meta import Certificates.Data.CFSGNative.MonsterB.Co2Matrix
public meta import CFSG.Monster.B.GSide.MuFourOmega

public noncomputable section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.Monster.B.GSide

open CFSG.Monster CFSG.Monster.Code CFSG.Monster.B CFSG.Monster.B.Short CFSG.Monster.B.TwoA
  CFSG.Monster.B.TwoA.Sp8 CFSG.Monster.B.TwoA.Amalgam CFSG.Monster.B.TwoA.Unitary
  CFSG.Monster.Visible CFSG.Monster.VisQuot
open CFSG.Monster.B.Co2 (v0 decW)

@[expose] def commK : Fin 15 → ℕ := ![6, 6, 6, 6, 6, 6, 7, 7, 7, 7, 8, 8, 8, 9, 9]

@[expose] def commJ : Fin 15 → ℕ := ![1, 6, 7, 8, 11, 17, 6, 9, 10, 11, 6, 8, 11, 6, 11]

@[expose] def commY : Fin 15 → ℕ := ![589888, 3678222, 1114392, 3678384, 2172920, 1640440, 3219474,
  1573912, 2621992, 3219456, 2695188, 60, 2695168, 1646616, 1646592]

@[expose] def commCode (i : Fin 15) : ℕ :=
  Co2.Native.actD 22 n6RowArr[commK i]! (2 ^ commJ i) ^^^ 2 ^ commJ i

end CFSG.Monster.B.GSide
