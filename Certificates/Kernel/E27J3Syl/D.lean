module

public import Certificates.Kernel.Sporadic.OddCore.MulHCmd
public import Certificates.Kernel.Misc.Perm.HexCmd
public import Certificates.Kernel.LocalQT.PEnumD
public import Certificates.Data.Kernel.Spor.MulHQ
public import CFSG.HardMathSupport.Foote.E27.SporJ3Data
public meta import CFSG.HardMathSupport.Foote.E27.SporJ3Data
public meta import Certificates.Kernel.Sporadic.RawGen
meta import Certificates.Data.CFSGNative.MonsterB.Co2Chain
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

namespace CFSG.KD.E27J3S.D

open CFSG.HardMathSupport.Foote.E27 CFSG.Sporadic.SmallOddCore.Native CFSG.PSL3Four.Native
open CFSG.Sporadic.Schreier

meta def idM : Array Nat := idTab 6156

meta def syM : Array (Array Nat) := (Array.range 8).map fun k => natArr (j3SylTbl k)

meta def syIM : Array (Array Nat) := syM.map (CFSG.Monster.B.Co2.Native.invCand 6156)

meta def sgIM : Array (Array Nat) :=
  (j3GenTbls.map natArr).toArray.map (CFSG.Monster.B.Co2.Native.invCand 6156)

meta def gS : Array (Array Nat) := (j3SylGens.map natArr).toArray

meta def idsS : Array (Array Nat) := Array.replicate gS.size idM

meta def giS : Array (Array Nat) := gS.map (CFSG.Monster.B.Co2.Native.invCand 6156)

meta def enS : Enum := bfs (fun j t => conjTab 6156 idM gS[j]! t) gS.size idM 300

meta def recS : Array (Array Nat) := enS.tabs

meta def clS : Array (Array Nat) := (recS.map fun x => (gS ++ giS).map fun g => comp 6156 x g).flatten

meta def xS : Array (Array Nat) := #[natArr (j3SylTbl 2), natArr (j3SylTbl 5)]

meta def mS : Array Nat := Id.run do
  let c := recS.size
  let idx := indexOf recS
  let pos : Array Nat := (recS.map fun x => gS.map fun g => idx.getD (comp 6156 x g) c).flatten
  let mut out : Array Nat := Array.replicate (c * c) 0
  for i in [0:c] do
    out := out.set! (c * i) i
    for j in [1:c] do
      let p := out[c * i + enS.par[j]!]!
      out := out.set! (c * i + j) pos[gS.size * p + enS.lab[j]!]!
  return out

end CFSG.KD.E27J3S.D

#ks_chars CFSG.KD.E27J3S.SY CFSG.HardMathSupport.Foote.E27.j3SylHex
#kmisc_hexflat CFSG.KD.E27J3S.SY CFSG.HardMathSupport.Foote.E27.j3SylHex 4 6156 13 8
#kmisc_packarrs CFSG.KD.E27J3S.SYI CFSG.KD.E27J3S.D.syIM 13
#kmisc_packarrs CFSG.KD.E27J3S.SGI CFSG.KD.E27J3S.D.sgIM 13
#kmulh CFSG.KD.E27J3S.SE 6156 13 CFSG.KD.E27J3S.D.idsS CFSG.KD.E27J3S.D.gS
  CFSG.KD.E27J3S.D.idM 300
#kmisc_packarrs CFSG.KD.E27J3S.SEI CFSG.KD.E27J3S.D.giS 13
#kfind CFSG.KD.E27J3S.SECl CFSG.KD.E27J3S.D.recS CFSG.KD.E27J3S.D.clS
#kfind CFSG.KD.E27J3S.SEX CFSG.KD.E27J3S.D.recS CFSG.KD.E27J3S.D.xS
#krows32 CFSG.KD.E27J3S.SEM CFSG.KD.E27J3S.D.mS

end
