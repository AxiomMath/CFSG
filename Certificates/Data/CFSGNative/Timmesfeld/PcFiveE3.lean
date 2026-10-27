module

public import Certificates.Data.CFSGNative.Timmesfeld.PcE3
public import Certificates.Data.CFSGNative.Timmesfeld.PcFive

public section

namespace Timmesfeld.PcFiveE3

open Timmesfeld.PcReg Timmesfeld.PcE3 Timmesfeld.PcFive

set_option compiler.extract_closed false

@[expose] def fiveE3A : Array Nat :=
  #[1353963, 68135, 36612, 44218, 57836, 43386, 10446, 480, 19656, 3922, 44459, 35367, 9442,
    48787, 52909, 35775, 68769, 6119, 71266, 75297, 1283925, 1180011, 211901, 208510, 1428405,
    721084, 10435, 1096104, 1305642, 416345, 1404349]

@[expose] def fiveE3B : Array Nat :=
  #[11492, 17142, 7023, 21151, 24160, 29167, 52272, 45154, 61897, 58536, 59962, 37065, 73546,
    13177, 1739, 38293, 14976, 70817, 2671, 55150, 604753, 526451, 1221432, 144717, 1135754,
    907571, 1, 1946334, 1270610, 1129420, 1775305]

@[expose] def fiveE3OK (_ : Unit := ()) : Bool :=
  let P := parTree 5 9
  let L := leftTables 5 9 pw cwR
  e3OK 5 9 P L repIdx fiveE3A fiveE3B

end Timmesfeld.PcFiveE3
