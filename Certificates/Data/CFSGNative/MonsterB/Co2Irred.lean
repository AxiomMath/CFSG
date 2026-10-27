module

public import Certificates.Data.CFSGNative.MonsterB.Co2Matrix

public section

namespace CFSG.Monster.B.Co2.Native

@[expose] def rowMinusI (i t : Nat) : Nat := (genRecords[i]!.quotientMatrix)[t]! ^^^ (1 <<< t)

@[expose] def rowSel : Array (Nat × Nat) :=
  #[(0, 0), (0, 1), (0, 2), (0, 3), (0, 5), (0, 6), (0, 7), (0, 8),
    (0, 9), (0, 10), (0, 13), (0, 15), (1, 0), (1, 1), (1, 2), (1, 5),
    (1, 6), (1, 7), (1, 9), (1, 12), (12, 1), (23, 6)]

@[expose] def rowInv : Array Nat :=
  #[1939174, 1939143, 1108711, 1940029, 1388780, 374505, 166091, 476234, 318624, 95728,
    423152, 3068698, 2638750, 2098057, 2115937, 2116510, 2659382, 2116297, 2115617, 2150777,
    2114462, 2544818]

@[expose] def colSel : Array (Nat × Nat) :=
  #[(0, 0), (0, 1), (0, 2), (0, 3), (0, 5), (0, 7), (0, 11), (0, 12),
    (0, 14), (0, 15), (0, 17), (0, 18), (1, 0), (1, 1), (1, 2), (1, 6),
    (1, 12), (1, 13), (1, 15), (1, 18), (12, 1), (23, 12)]

@[expose] def colInv : Array Nat :=
  #[2423767, 2423790, 2423750, 2382838, 2407374, 8193, 32791, 36896, 32786, 4157, 32773,
    1779063, 467797, 184, 315572, 412744, 969298, 179718, 830624, 180801, 587077, 813257]

@[expose] def colOf (i s : Nat) : Nat := Id.run do
  let mut c := 0
  for t in [0:22] do
    if (rowMinusI i t).testBit s then c := c ||| (1 <<< t)
  return c

@[expose] def colArr (_ : Unit := ()) : Array Nat := colSel.map fun p => colOf p.1 p.2

@[expose] def irredCheck (_ : Unit := ()) : Bool :=
  rowSel.size == 22 && colSel.size == 22 && colArr.size == 22 &&
    allLt 22 (fun k => decide (rowSel[k]!.1 < 24) && decide (rowSel[k]!.2 < 22)) &&
    allLt 22 (fun t =>
      actD 22 (rowSel.map fun p => rowMinusI p.1 p.2) rowInv[t]! == 1 <<< t) &&
    allLt 22 (fun k => decide (colSel[k]!.1 < 24) && decide (colSel[k]!.2 < 22)) &&
    allLt 22 (fun k => allLt 22 fun t =>
      colArr[k]!.testBit t == (rowMinusI colSel[k]!.1 t).testBit colSel[k]!.2) &&
    allLt 22 (fun t => actD 22 colArr colInv[t]! == 1 <<< t)

end CFSG.Monster.B.Co2.Native
