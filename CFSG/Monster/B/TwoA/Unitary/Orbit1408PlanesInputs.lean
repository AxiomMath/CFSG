
module

public import CFSG.Monster.B.TwoA.Unitary.Orbit1408PlanesInputsBase
import all CFSG.Monster.B.TwoA.Unitary.Orbit1408PlanesInputsBase

public import CFSG.Monster.B.TwoA.Unitary.Orbit1408PointsBase
public import CFSG.Monster.B.TwoA.Unitary.Orbit1408PointsInputs
public import CFSG.Monster.B.TwoA.Unitary.Orbit1408Data
public import CFSG.Monster.B.TwoA.Unitary.OrbitInputs
public import CFSG.Monster.B.TwoA.Unitary.WStabInputs
public import CFSG.Monster.B.TwoA.Unitary.Orbit1408SchreierBase
public import Certificates.Data.CFSGNative.MonsterB.Short
public import Certificates.Data.CFSGNative.Mathieu.M24
public import CFSG.Certificates.Kernel.AxisPlane.Orbit
public import Certificates.Data.Kernel.VisFrame.Gens
public import Certificates.Data.CFSGNative.MonsterB.Co2Chain
public import Certificates.Data.CFSGNative.MonsterB.Co2Matrix
public import CFSG.Monster.B.TwoA.Unitary.Bridge
public import CFSG.Monster.B.TwoA.Unitary.ActionInputs
public import CFSG.Monster.B.TwoA.Unitary.Stab891Inputs
public import CFSG.Monster.B.TwoA.Unitary.Orbit1408Inputs
public meta import CFSG.Monster.B.TwoA.Unitary.Orbit1408PointsBase
public meta import CFSG.Monster.B.TwoA.Unitary.Orbit1408PointsInputs
public meta import CFSG.Monster.B.TwoA.Unitary.Orbit1408Data
public meta import CFSG.Monster.B.TwoA.Unitary.OrbitInputs
public meta import CFSG.Monster.B.TwoA.Unitary.WStabInputs
public meta import CFSG.Monster.B.TwoA.Unitary.Orbit1408SchreierBase
public meta import Certificates.Data.CFSGNative.MonsterB.Short
public meta import Certificates.Data.CFSGNative.Mathieu.M24
public meta import CFSG.Certificates.Kernel.AxisPlane.Orbit
public meta import Certificates.Data.Kernel.VisFrame.Gens
public meta import Certificates.Data.CFSGNative.MonsterB.Co2Chain
public meta import Certificates.Data.CFSGNative.MonsterB.Co2Matrix
public meta import CFSG.Monster.B.TwoA.Unitary.Bridge
public meta import CFSG.Monster.B.TwoA.Unitary.ActionInputs
public meta import CFSG.Monster.B.TwoA.Unitary.Stab891Inputs
public meta import CFSG.Monster.B.TwoA.Unitary.Orbit1408Inputs
public meta import CFSG.Monster.B.TwoA.Unitary.Orbit1408Data
public meta import CFSG.Monster.B.TwoA.Unitary.NData
public meta import CFSG.Monster.B.TwoA.Unitary.BData
public meta import CFSG.Monster.B.TwoA.Unitary.Form
public meta import CFSG.Monster.B.TwoA.Unitary.PlanesPrelude
public meta import CFSG.Monster.B.TwoA.Census.NatCert
import CFSG.Fischer.F4

public noncomputable section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.Monster.B.TwoA.Unitary

open CFSG.Fischer CFSG.Monster CFSG.Monster.B.Short CFSG.Monster.B.Co2 CFSG.Monster.B.TwoA
  CFSG.Monster.B.TwoA.Census CFSG.Monster.B.Generic

@[expose] def singCert (c : ℕ) : NatCert :=
  natBfs (selAct singGenArr singT singI o14PtSel) o14PtSel.size (o14PtOrb[c]!)[0]! 800

@[expose] def natCert (c : ℕ) : NatCert :=
  natBfs (selAct n6PermsArr natT natI o14PlSel) o14PlSel.size (natOf (o14PlOrb[c]!)[0]!) 1000

end CFSG.Monster.B.TwoA.Unitary
