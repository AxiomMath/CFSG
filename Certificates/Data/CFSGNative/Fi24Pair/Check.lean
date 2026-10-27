module

public import Certificates.Data.CFSGNative.Fi24.Certificate
public import Certificates.Data.CFSGNative.HN.LevelChain

public section

namespace CFSG.Sporadic.Fi24Pair.Native

open CFSG.Sporadic.Th.Native CFSG.Perm.Native CFSG.Sporadic.Fi23.Native
  CFSG.Sporadic.Fi24.Native CFSG.Sporadic.LevelChain.Native

set_option compiler.extract_closed false

@[expose] def pairLines0 : Array (List Int) := #[
  [3, 6, 10, -15, 11, 5, -12, -7, -7, -10, 7, 7, 14, -10, -10, -10, 15, 10, 9, -14, 15, -12],
  [5, 11, 9, -5, 4, -8, -8, 13, 6, -9, -7, -15, 13, 12, 7, 9, -10, -9, 10, -13, 10, 11, -13, 15, 11,
    15],
  [-11, -15, 9, -10, -10, -10, 15, -10, 12, -7, 9, 13, -7, -14, 6, 9, -8, -10, 9],
  [-15, 14, 15, -12, 9, 10, 9, 10, 10, 13, 10, 8, -12, 9, -7, 5, 10, -6, -13, -9, 3, -6, 14, 9,
    -12],
  [-15, -12, -15, -14, 10, 10, -14, -11, -12, 9, 7, 7, -11, 10, -11, -10, 5, -9, 7, 14, 5],
  [14, -11, 9, -11, 10, 11, -9, 7, -8, 11, 13, -7, -8, 5, 14, -7, -12, -13],
  [-15, 11, -14, 11, 15, 9, 13, -10, -10, 13, 11, -7, 12, -7, -14, 13, 6, 12, -15, 8, -5],
  [-12, 14, -13, 10, 10, 10, -15, -9, -11, 7, -13, 11, 15, -10, 5, 15, 7, -14, 12, 3, 7, -5, 9, 9]]

@[expose] def pairLines1 : Array (List Int) := #[
  [15, -12, -13, -12, -10, 13, -15, 10, 15, -9, -7, 9, -11, -10, -14, 6, -10, -12, -14, -12, 3, -5,
    -8, 6],
  [-11, -15, 9, -10, -10, -10, 15, -10, 12, -7, 9, 13, -7, -14, 6, 9, -8, -10, 9],
  [-15, 14, 15, -12, 9, 10, 9, 10, 10, 13, 10, 8, -12, 9, -7, 5, 10, -6, -13, -9, 16, -6, 14, 9,
    -12],
  [-15, -12, -15, -14, 10, 10, -14, -11, -12, 9, 7, 7, -11, 10, -11, -10, 5, -9, 7, 14, 5],
  [14, -11, 9, -11, 10, 11, -9, 7, -8, 11, 13, -7, -8, 5, 14, -7, -12, -13],
  [-15, 11, -14, 11, 15, 9, 13, -10, -10, 13, 11, -7, 12, -7, -14, 13, 6, 12, -15, 8, -5],
  [-12, 14, -13, 10, 10, 10, -15, -9, -11, 7, -13, 11, 15, -10, 5, 15, 7, -14, 12, 16, 7, -5, 9, 9],
  [15, -12, -13, -12, -10, 13, -15, 10, 15, -9, -7, 9, -11, -10, -14, 6, -10, -12, -14, -12, 16, -5,
    -8, 6]]

@[expose] def pairLines2 : Array (List Int) := #[
  [19, 20, 20, 22, -20, -20, -19],
  [19, -20, 19, 27, -19, -20, -19],
  [19, -20, 19, 29, -19, 20, -19],
  [19, 20, 19, 27, -19, 20, -19],
  [19, 26],
  [25],
  [19, 20, 19, 28, -19, 20, -19],
  [33, 37, 38, -37, -33]]

@[expose] def pairLines3 : Array (List Int) := #[
  [33, 33, 38, 37, 36, -37, -38, -33, -33],
  [-33, 34, 33],
  [-33, 38, 37, -38, -37],
  [37, 33, 34, -33, -37],
  [39, -42, -42, 39, -42, 41, 42, -43, -42, -43, -41, -42],
  [19, 20, 28, 20, -19],
  [23, 30],
  [19, 20, -23, 18, 23, -20, -19]]

@[expose] def pairLines4 : Array (List Int) := #[
  [19, 22, -19],
  [30, -23],
  [23, 27, 20, -19],
  [45, 50, 49, -50, -45],
  [-50, 45, 48, -50, 49, 50, -48, -45, 50],
  [-46, 47],
  [-46, 50, 47, -50, -45],
  [-50, 47, 50, 46, -45]]

@[expose] def pairLines5 : Array (List Int) := #[
  [-50, 45, 47, 46, -47, -45, -50],
  [50, 45, 48, -50, 48, 50, -48, -45, -50],
  [45, -50, 48, 50, -48, -47, -50],
  [51, 58, -54, 56, 58, 54, 56, -53, -53, -53],
  [54, 53, -56, -56, 57, -53, -54, 56, -51, -54],
  [19, -20, -24, 20, 20, -18, -24],
  [19, -24, 22, 24, -19],
  [19, -20, 19, 28, -19, -20, -19]]

@[expose] def pairLines6 : Array (List Int) := #[
  [19, 20, 19, 29, -19, -20, -19],
  [19, 20, 24, 26, -24, -20, -19],
  [20],
  [-66, 64, 66],
  [-66, -61, 64, 61, 66],
  [64],
  [-66, 63, -66, -63],
  [61, 61, 63, -66]]

@[expose] def pairLines7 : Array (List Int) := #[
  [61, 62, -61],
  [-66, 65, 65, 66],
  [63, 66, 61, 61, -66, -66],
  [-61, 65, 66, -61],
  [67, 70, 71, 67, 68, -74, 75, -71, -71, -68, -75, -70],
  [70, 72, -75, 71, -75, 73, -75, 74, 75, 75, -67],
  [24, 23, 24, -23, 22, 24, 23, -24, -23, -24, 20, 19, 20, 24, -23, 24, 19, 23, 24, -23, -24, -23,
    -24],
  [24, 23, 24, 23, -24, -23, 24, 23, -24, 20, 23, 24, 21, 24, 23, -24, 23, 19, 24, -23, -24, -23,
    -24, -23, -24, -23, -24]]

@[expose] def pairLines8 : Array (List Int) := #[
  [24, 23, 24, 23, 24, 23, 20, -24, -23, 24, 23, -24, -20, 23, -24, 23, -21, 24, -23, -24, 23, -24,
    23, 24, 20, -23, -24],
  [-24, 23, 24, 23, 24, -18, -23, -23, 24, -23, 24, -18, 24, 23, -24, -20, -23, -24],
  [24, 23, -20, 24, 23, -24, 23, -24, 23, -20, -24, -23, 24, 24, 24, -22, -23, 24, 23, 24, 23, -21,
    24, -23, -24, -23, -24],
  [79, 80, -78, -81, 82, -79, 81, 80, -79, -81, 82, 79, 78],
  [78, 78, -79, -81, 80, 79, 81, 81, 82, -81, 79, -78],
  [82, -81, 82, -81, -82, -80, 78, 81, -78, -79, 80, -78, -82],
  [82, 79, -78, 82, 81, 78, 79, 79, 78, 78, 82],
  [78, -80, -82, 78, 79, 79, -80, 82, 80, 81, -82, -79, -80, 81]]

@[expose] def pairLines9 : Array (List Int) := #[
  [84, -83, -86, 84, -85, -86, 87, 84, -86, -86, 83, 86, 83],
  [-83, -84, -84, 85, 85, 84, 86, -85, -85, -85, -83, -86, 83],
  [83, 83, 87, 87, -85, -87, 85, 84, 86, -85, 83, 84, -85],
  [84, -86, -86, 87, -85, -86, 87, -86, 85, 86, 83, -87],
  [-85, -87, 86, -85, -85, 83, -86, -86, 85, -84, 85],
  [-88, 91, -90, 91, -89, 91, 92, -91, -91, 90, -89, 90],
  [91, -92, -91, 89, 88, 89, -88, 91, 88, -90, 88, 88],
  [88, 88, 91, 90, 89, 92, 91, 88, 89, -88, -88, -91]]

@[expose] def pairLines10 : Array (List Int) := #[
  [89, 89, 91, 91, 91, 91, 92, 92, -91, -88, -88, -88],
  [92, 90, -91, 89, -90, 91, -90, 88, -91, 88, -92, -88],
  [93, -97, 93, 95, 93, 95, -97],
  [93, 97, -93, -97, 96, 93, -97, -95],
  [-97, -93, 95, 93, -96, -97, -93],
  [95, -96, 97, -95, 97, 96, -95, -97],
  [93, -95, 97, 95, 97, 93, -96, -94]]

@[expose] def pairLines (_ : Unit := ()) : Array (List Int) :=
  pairLines0 ++ pairLines1 ++ pairLines2 ++ pairLines3 ++ pairLines4 ++ pairLines5 ++ pairLines6 ++
    pairLines7 ++ pairLines8 ++ pairLines9 ++ pairLines10

@[expose] def pairWords (_ : Unit := ()) : Array (List Int) :=
  CFSG.Sporadic.Fi24.Native.chainWords () ++ pairLines ()

@[expose] def lineNA : Nat := 13

@[expose] def lineNB : Nat := 14

structure ChainData where
  sel : Array Nat
  starts : Array Nat
  ords : Array Nat
  base : Array Nat
  sizes : List Nat
  ntw : Nat
deriving Inhabited

@[expose] def ChainData.Q (D : ChainData) : Array Nat :=
  CFSG.Sporadic.Fi24.Native.chainBase ++ D.base

@[expose] def ChainData.qb (D : ChainData) : Array Nat :=
  (Array.range D.base.size).map (· + CFSG.Sporadic.Fi24.Native.chainBase.size)

@[expose] def chainT : ChainData where
  sel :=
    #[15, 16, 17, 18, 19, 22, 23, 24, 25, 26, 29, 30, 31, 32, 33, 34, 35, 36, 37, 38, 39, 40, 41]
  starts := #[0, 10, 17, 22, 23]
  ords :=
    #[4, 4, 4, 2, 2, 4, 4, 4, 2, 2, 2, 4, 2, 4, 2, 4, 4, 4, 2, 2, 8, 2, 2]
  base := #[0, 1, 2, 3]
  sizes := [8, 16, 8192, 2]
  ntw := 5

@[expose] def chainA : ChainData where
  sel :=
    #[15, 16, 17, 18, 19, 20, 22, 23, 24, 25, 26, 27, 42, 43, 44, 45, 46, 47, 48, 49, 50, 51, 52,
      53, 54, 55, 56, 57]
  starts := #[0, 12, 18, 26, 28]
  ords :=
    #[4, 4, 4, 2, 2, 12, 4, 4, 4, 2, 2, 12, 2, 3, 4, 2, 2, 8, 2, 2, 6, 4, 4, 6, 2, 6, 2, 2]
  base := #[0, 1, 2, 3]
  sizes := [8, 48, 36864, 4]
  ntw := 6

@[expose] def chainB : ChainData where
  sel :=
    #[15, 16, 17, 18, 19, 21, 22, 23, 24, 25, 26, 28, 58, 59, 60, 61, 62, 63, 64, 65, 66, 67, 68,
      69, 70, 71, 72, 73, 74]
  starts := #[0, 12, 18, 27, 29]
  ords :=
    #[4, 4, 4, 2, 2, 6, 4, 4, 4, 2, 2, 6, 8, 2, 4, 2, 4, 4, 2, 2, 2, 2, 4, 2, 2, 4, 8, 2, 2]
  base := #[0, 1, 2, 3]
  sizes := [24, 16, 12288, 4]
  ntw := 6

@[expose] def chainH : ChainData where
  sel :=
    #[15, 16, 17, 18, 19, 20, 21, 75, 76, 77, 78, 79, 80, 81, 82, 83, 84, 85, 86, 87, 88, 89, 90,
      91, 92, 93, 94, 95, 96, 97, 98, 99]
  starts := #[0, 7, 12, 17, 22, 27, 32]
  ords :=
    #[]
  base := #[0, 305530, 5604, 221549, 266275, 186844]
  sizes := [306936, 275264, 218400, 93312, 243, 3]
  ntw := 0

@[expose] def selLetters (L : Array Table) (sel : Array Nat) : Array Table :=
  Array.ofFn (n := 2 * sel.size) fun i => L[2 * sel[i.val / 2]! + i.val % 2]!

@[expose] def selNestOK (W : Array (List Int)) (sel starts : Array Nat) : Bool :=
  allIn 1 (starts.size - 1) fun i => allIn starts[i]! starts[i + 1]! fun k =>
    W[sel[k]!]!.all fun z => decide (3 ≤ z.natAbs) &&
      (List.range' starts[i - 1]! (starts[i]! - starts[i - 1]!)).any fun k' =>
        sel[k']! + 3 == z.natAbs

@[expose] def shiftWord (w : List Int) : List Int := w.map fun l => if 0 < l then l + 2 else l - 2

@[expose] def twistZ (z : Int) : Int :=
  if z.natAbs = 3 then (if 0 < z then (lineNA + 3 : Int) else -(lineNA + 3 : Int))
  else if z.natAbs = 4 then (if 0 < z then (lineNB + 3 : Int) else -(lineNB + 3 : Int))
  else z

@[expose] def twistOK (W : Array (List Int)) (g t : Nat) : Bool :=
  decide (lineNB < t) && W[g]!.all (fun z => decide (3 ≤ z.natAbs ∧ z.natAbs ≤ 15)) &&
    W[t]! == W[g]!.map twistZ

@[expose] def twistsOK (W : Array (List Int)) (D : ChainData) : Bool :=
  D.starts[1]! == 2 * D.ntw && allIn 0 D.ntw fun k => twistOK W D.sel[k]! D.sel[k + D.ntw]!

@[expose] def exactOK (L : Array Table) (W : Array (List Int)) (D : ChainData) : Bool :=
  let LX := selLetters L D.sel
  let T := levelTrees (nPts ()) LX D.starts D.base
  D.sel.all (· < W.size) && selNestOK W D.sel D.starts &&
    levelChainOK (nPts ()) LX D.starts D.ords D.base D.Q D.qb T 3 && orbitSizes T == D.sizes

@[expose] def lowerOK (L : Array Table) (W : Array (List Int)) (D : ChainData) : Bool :=
  let LX := selLetters L D.sel
  let T := levelTrees (nPts ()) LX D.starts D.base
  let m := D.base.size
  D.sel.all (· < W.size) && selNestOK W D.sel D.starts && D.starts.size == m + 1 &&
    LX.size == 2 * D.starts[m]! && allIn 0 m (fun i => D.starts[i]! ≤ D.starts[i + 1]!) &&
    allIn 0 m (fun i => treeOK (nPts ()) D.base[i]! T[i]! LX (levelLv D.starts i)) &&
    allIn 1 m (fun i => allIn D.starts[i]! D.starts[i + 1]! fun j =>
      ap LX[2 * j]! D.base[i - 1]! == D.base[i - 1]!) &&
    orbitSizes T == D.sizes

@[expose] def asch54Fi24Check (_ : Unit := ()) : Bool :=
  let O := orbitData ()
  let W := pairWords ()
  let L := slpLetters (nPts ()) (genTables O) W
  slpOK W && allIn 0 W.size (fun j => invOK (nPts ()) L[2 * j]! L[2 * j + 1]!) &&
    twistsOK W chainT && twistsOK W chainA && twistsOK W chainB &&
    exactOK L W chainT && exactOK L W chainA && exactOK L W chainB && lowerOK L W chainH

end CFSG.Sporadic.Fi24Pair.Native

end
