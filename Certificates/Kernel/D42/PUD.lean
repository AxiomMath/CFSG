module

public import Certificates.Kernel.Sporadic.OddCore.MulHCmd
public import Certificates.Kernel.Misc.Perm.HexCmd
public import Certificates.Data.Kernel.Spor.MulHQ
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.D42Inputs
meta import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.D42Inputs
meta import Certificates.Kernel.Sporadic.RawGen
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

namespace CFSG.KD.D42.PUD

open CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.D42 CFSG.Sporadic.SmallOddCore.Native
open CFSG.PSL3Four.Native CFSG.Sporadic.SmallOddCore

meta def idM : Array Nat := idTab 360

meta def gP (j : Nat) : Array (Array Nat) := ((pGens j).map natArr).toArray

meta def gU (j : Nat) : Array (Array Nat) := ((uGens j).map natArr).toArray

meta def invs (g : Array (Array Nat)) : Array (Array Nat) :=
  g.map (CFSG.Monster.B.Co2.Native.invCand 360)

meta def ids (g : Array (Array Nat)) : Array (Array Nat) := Array.replicate g.size idM

meta def recOf (g : Array (Array Nat)) (cap : Nat) : Array (Array Nat) :=
  (bfs (fun j t => conjTab 360 idM g[j]! t) g.size idM cap).tabs

meta def prods (R g : Array (Array Nat)) : Array (Array Nat) :=
  (R.map fun x => (g ++ invs g).map fun h => comp 360 x h).flatten

meta def conjs (R cs : Array (Array Nat)) : Array (Array Nat) :=
  (R.map fun x => (List.range cs.size).toArray.map fun l =>
    comp 360 (comp 360 cs[l]! x) (CFSG.Monster.B.Co2.Native.invCand 360 cs[l]!)).flatten

meta def commT (u y : Array Nat) : Array Nat :=
  comp 360 (comp 360 (comp 360 u y) (CFSG.Monster.B.Co2.Native.invCand 360 u))
    (CFSG.Monster.B.Co2.Native.invCand 360 y)

meta def pick9 (RU : Array (Array Nat)) (y : Array Nat) : Array Nat := Id.run do
  let mut seen : Array (Nat × Nat) := #[]
  for l in [0:RU.size] do
    if seen.size < 9 then
      let c := CFSG.KS.RawGen.pack 9 (commT RU[l]! y)
      if !(seen.any fun p => p.1 == c) then
        seen := seen.push (c, l)
  let s := seen.qsort (fun a b => a.1 < b.1)
  return s.map (·.2)

meta def commRows (RP RU : Array (Array Nat)) : Array (Array Nat) :=
  RP.mapIdx fun i y => if i = 0 then Array.replicate 9 0 else pick9 RU y

meta def gP0 : Array (Array Nat) := gP 0
meta def gP1 : Array (Array Nat) := gP 1
meta def gU0 : Array (Array Nat) := gU 0
meta def gU1 : Array (Array Nat) := gU 1
meta def iP0 : Array (Array Nat) := ids gP0
meta def iP1 : Array (Array Nat) := ids gP1
meta def iU0 : Array (Array Nat) := ids gU0
meta def iU1 : Array (Array Nat) := ids gU1
meta def giP0 : Array (Array Nat) := invs gP0
meta def giP1 : Array (Array Nat) := invs gP1
meta def giU0 : Array (Array Nat) := invs gU0
meta def giU1 : Array (Array Nat) := invs gU1
meta def rP0 : Array (Array Nat) := recOf gP0 81
meta def rP1 : Array (Array Nat) := recOf gP1 9
meta def rU0 : Array (Array Nat) := recOf gU0 512
meta def rU1 : Array (Array Nat) := recOf gU1 512
meta def clP0 : Array (Array Nat) := prods rP0 gP0
meta def clP1 : Array (Array Nat) := prods rP1 gP1
meta def clU0 : Array (Array Nat) := prods rU0 gU0
meta def clU1 : Array (Array Nat) := prods rU1 gU1
meta def nU0 : Array (Array Nat) := conjs rU0 gP0
meta def nU1 : Array (Array Nat) := conjs rU1 gP1
meta def cP0 : Array (Array Nat) := commRows rP0 rU0
meta def cP1 : Array (Array Nat) := commRows rP1 rU1

end CFSG.KD.D42.PUD

#kmulh CFSG.KD.D42.P0 360 9 CFSG.KD.D42.PUD.iP0 CFSG.KD.D42.PUD.gP0 CFSG.KD.D42.PUD.idM 81
#kmulh CFSG.KD.D42.P1 360 9 CFSG.KD.D42.PUD.iP1 CFSG.KD.D42.PUD.gP1 CFSG.KD.D42.PUD.idM 9
#kmulh CFSG.KD.D42.U0 360 9 CFSG.KD.D42.PUD.iU0 CFSG.KD.D42.PUD.gU0 CFSG.KD.D42.PUD.idM 512
#kmulh CFSG.KD.D42.U1 360 9 CFSG.KD.D42.PUD.iU1 CFSG.KD.D42.PUD.gU1 CFSG.KD.D42.PUD.idM 512
#kmisc_packarrs CFSG.KD.D42.P0I CFSG.KD.D42.PUD.giP0 9
#kmisc_packarrs CFSG.KD.D42.P1I CFSG.KD.D42.PUD.giP1 9
#kmisc_packarrs CFSG.KD.D42.U0I CFSG.KD.D42.PUD.giU0 9
#kmisc_packarrs CFSG.KD.D42.U1I CFSG.KD.D42.PUD.giU1 9
#kfind CFSG.KD.D42.P0Cl CFSG.KD.D42.PUD.rP0 CFSG.KD.D42.PUD.clP0
#kfind CFSG.KD.D42.P1Cl CFSG.KD.D42.PUD.rP1 CFSG.KD.D42.PUD.clP1
#kfind CFSG.KD.D42.U0Cl CFSG.KD.D42.PUD.rU0 CFSG.KD.D42.PUD.clU0
#kfind CFSG.KD.D42.U1Cl CFSG.KD.D42.PUD.rU1 CFSG.KD.D42.PUD.clU1
#kfind CFSG.KD.D42.U0N CFSG.KD.D42.PUD.rU0 CFSG.KD.D42.PUD.nU0
#kfind CFSG.KD.D42.U1N CFSG.KD.D42.PUD.rU1 CFSG.KD.D42.PUD.nU1
#kmisc_packarrs CFSG.KD.D42.P0C CFSG.KD.D42.PUD.cP0 9
#kmisc_packarrs CFSG.KD.D42.P1C CFSG.KD.D42.PUD.cP1 9

end
