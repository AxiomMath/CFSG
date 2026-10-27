
module

public import CFSG.Sporadic.Co1.Module.OrbitsInputs

@[expose] public section

namespace CFSG.Sporadic.Co1.Module

open CFSG.Blueprint CFSG.Sporadic.SmallF2 CFSG.Sporadic.SmallF2.Native Matrix

@[expose] def addRows (X Y : Array ℕ) : Array ℕ :=
  Array.ofFn (n := 24) fun i => (X[i.val]?.getD 0) ^^^ (Y[i.val]?.getD 0)

@[expose] def letterRows (b : Bool) : Array ℕ := if b then dat.rowsA else dat.rowsB

@[expose] def wordRows (w : List Bool) : Array ℕ :=
  w.foldl (fun acc b => mulRows 24 acc (letterRows b)) (idRows 24)

@[expose] def qRows : Array ℕ := #[
  8388608, 10379264, 4321280, 1679360, 4710400, 81920, 11182080, 13221888, 16683008, 9777152,
  8183808, 11567104, 978944, 3391488, 11304960, 15106048, 6160384, 16384000, 14155776, 3145728,
  2097152, 14680064, 0, 0]

@[expose] def f0InvRows : Array ℕ := #[
  13536504, 3423716, 5630794, 8212517, 1746081, 1494171, 5120647, 1219699, 6467590, 3624004,
  8348339, 7598759, 2442, 3414, 3628, 2485, 3596, 4081, 1647, 1113, 3774, 3850, 3405, 1]

@[expose] def stabWord₁ : List Bool :=
  "BBABBABBABBABBABBBBABBABBBBABBBBABBABBABBABABABBABAB".toList.map (· == 'A')

@[expose] def stabWord₂ : List Bool :=
  "ABBABBABBABBABBBBABBBBABBABBABBABABABBABABABABABBABBA".toList.map (· == 'A')

@[expose] def certC1 : Array ℕ := #[
  13447, 0, 44365, 1626, 44788, 11248, 9037, 67489, 39660, 100145, 110316, 69093, 71658, 13864,
  36218, 100554, 71547, 77769, 108638, 3772, 79113, 69670, 6796, 37933]

@[expose] def certC2 : Array ℕ := #[
  1, 0, 456, 327, 388, 394, 268, 131, 259, 134, 326, 142, 267, 199, 323, 323, 395, 73, 138, 256,
  387, 389, 9, 455]

@[expose] def certD1 : Array ℕ := #[
  16408448, 0, 5640786, 14991616, 12566947, 131931, 15079200, 6557677, 8704511, 6572412,
  15879995, 7703693, 8721429, 4853133, 5522962, 8243413, 0, 0, 1214848, 0, 0, 0, 0, 0]

@[expose] def certD2 : Array ℕ := #[
  12638313, 0, 1892155, 2987491, 9817046, 7356474, 6439133, 4328908, 0, 0, 0, 0, 0, 0, 0, 0, 0,
  0, 0, 0, 0, 0, 0, 0]

@[expose] def f0Rows : Array ℕ := addRows qRows (transposeRows 24 qRows)

@[expose] def projRows : Array ℕ :=
  Array.ofFn (n := 24) fun i => if i.val = 1 then 0 else 1 <<< i.val

@[expose] def lamRows : Array ℕ :=
  Array.ofFn (n := 24) fun i => (1 <<< i.val) ^^^ (if i.val = 13 then 10379264 else 0)

end CFSG.Sporadic.Co1.Module
