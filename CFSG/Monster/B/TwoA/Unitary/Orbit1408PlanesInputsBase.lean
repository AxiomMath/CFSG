
module

public import CFSG.Monster.B.TwoA.Unitary.Orbit1408PointsBase
public import CFSG.Monster.B.TwoA.Unitary.Orbit1408SchreierBase
public meta import CFSG.Monster.B.TwoA.Unitary.Orbit1408PointsBase
public meta import CFSG.Monster.B.TwoA.Unitary.Orbit1408SchreierBase
public meta import CFSG.Monster.B.TwoA.Unitary.Orbit1408Data
public meta import CFSG.Monster.B.TwoA.Unitary.NData
public meta import CFSG.Monster.B.TwoA.Unitary.BData
public meta import CFSG.Monster.B.TwoA.Unitary.Form
public meta import CFSG.Monster.B.TwoA.Unitary.PlanesBase
public meta import CFSG.Monster.B.TwoA.Census.NatCert
import all CFSG.Fischer.F4

public noncomputable section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.Monster.B.TwoA.Unitary

open CFSG.Fischer CFSG.Monster CFSG.Monster.B.Short CFSG.Monster.B.Co2 CFSG.Monster.B.TwoA
  CFSG.Monster.B.TwoA.Census CFSG.Monster.B.Generic

@[expose] def singGenArr : Array (Array ℕ) :=
  (List.finRange 17).toArray.map fun k => (List.finRange 693).toArray.map fun i => (singGen k i : ℕ)

@[expose] def singT : Array (Array ℕ) := transArr singGenArr 693

@[expose] def singI : Array (Array ℕ) := singT.map invPermArr

@[expose] def natT : Array (Array ℕ) := transArr n6PermsArr 891

@[expose] def natI : Array (Array ℕ) := natT.map invPermArr

@[expose] def singPart : Array ℕ :=
  (List.range 693).toArray.map fun i => if o14PtOrb[0]!.contains i then 0 else 1

@[expose] def natPart : Array ℕ :=
  (List.range 891).toArray.map fun j => if o14PlOrb[0]!.contains (b6IsoArr[j]! % 891) then 0 else 1

@[expose] def natOf (p : ℕ) : ℕ := (b6IsoArr.toList.map (· % 891)).idxOf p

end CFSG.Monster.B.TwoA.Unitary
