module

public import CFSG.Sporadic.SuzRecog.TwistTests
public meta import CFSG.Sporadic.SuzRecog.TwistTests

public section

namespace CFSG.Sporadic.SuzRecog.RigidL2

open CFSG.ComponentClassification.AS81.SuzB0 CFSG.Monster.B.Co2.Native CFSG.PSL3Four.Native
  CFSG.Sporadic.SuzOddCore

@[expose] def rigUWords : List (List Nat) :=
  [[], [3], [1, 3, 8, 3, 1], [2, 3, 5, 3, 2], [5, 6, 1, 3, 4], [1, 4, 7, 3, 4], [6, 7, 9, 8, 6],
    [9, 7, 6, 4, 7], [9, 6, 5, 9, 9], [1, 3, 8, 1, 3, 1], [6, 8, 2, 7, 8, 1], [2, 3, 5, 2, 3, 2],
    [5, 6, 1, 3, 4, 3], [6, 7, 9, 8, 6, 3], [9, 6, 5, 9, 9, 3], [7, 4, 4, 6, 4, 4]]

@[expose] def rigUFix : List Nat := [0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]

@[expose] def rigX1 : List Nat := [9, 6, 4]

@[expose] def rigX2 : List Nat := [3, 7, 9, 1]

@[expose] def rigSeeds : List (Nat × Nat) := [(0, 24), (6, 0)]

@[expose] def rigGam : List (List (List Nat)) := [[[8, 1], [6, 8, 7, 2]], [[8, 1], [7, 9, 1]]]

@[expose] def rigGens : List (Nat × List Nat × Nat × Nat) :=
  [(0, [], 0, 24), (0, [9, 6, 4], 0, 66), (0, [3, 7, 9, 1], 0, 43), (0, [9, 6, 4, 9, 6, 4], 0, 74),
    (1, [], 6, 0), (1, [9, 6, 4], 5, 58), (1, [9, 6, 4, 9, 6, 4], 14, 24),
    (1, [3, 7, 9, 1, 9, 6, 4], 10, 19)]

@[expose] def rigBfs : List (List Nat) :=
  [[], [0], [1], [0, 0], [0, 1], [1, 0], [1, 1], [0, 0, 0], [0, 0, 1], [0, 1, 0], [0, 1, 1],
    [1, 0, 0], [1, 0, 1], [1, 1, 0], [0, 0, 0, 0], [0, 0, 0, 1], [0, 0, 1, 0], [0, 0, 1, 1],
    [0, 1, 0, 0], [0, 1, 0, 1], [0, 1, 1, 0], [1, 0, 0, 1], [1, 0, 1, 0], [1, 0, 1, 1],
    [1, 1, 0, 1], [0, 0, 0, 0, 1], [0, 0, 0, 1, 0], [0, 0, 0, 1, 1], [0, 0, 1, 0, 1],
    [0, 0, 1, 1, 0], [0, 1, 0, 0, 1], [0, 1, 0, 1, 1], [0, 1, 1, 0, 1], [1, 0, 0, 1, 0],
    [1, 0, 1, 0, 0], [1, 0, 1, 1, 0], [1, 1, 0, 1, 0], [1, 1, 0, 1, 1], [0, 0, 0, 0, 1, 0],
    [0, 0, 0, 1, 1, 0], [0, 0, 1, 0, 1, 1], [0, 0, 1, 1, 0, 1], [0, 1, 0, 0, 1, 0],
    [0, 1, 0, 1, 1, 0], [0, 1, 1, 0, 1, 0], [0, 1, 1, 0, 1, 1], [1, 0, 0, 1, 0, 1],
    [1, 0, 1, 0, 0, 1], [1, 0, 1, 1, 0, 1], [1, 1, 0, 1, 0, 0], [1, 1, 0, 1, 1, 0],
    [0, 0, 0, 1, 1, 0, 1], [0, 0, 1, 0, 1, 1, 0], [0, 0, 1, 1, 0, 1, 0], [0, 1, 1, 0, 1, 0, 0],
    [1, 0, 0, 1, 0, 1, 1], [1, 0, 1, 1, 0, 1, 1], [1, 1, 0, 1, 0, 0, 1], [1, 1, 0, 1, 1, 0, 1],
    [0, 1, 1, 0, 1, 0, 0, 1]]

@[expose] def rigIrrWords : List (List Nat) :=
  [[], [0], [1], [0, 0], [0, 1], [1, 0], [1, 1], [0, 0, 0]]

@[expose] def rigExpand (u : List Nat) : List Nat :=
  u.flatMap fun l => if l == 0 then rigX1 else rigX2

@[expose] def rigUTab (c : Nat) : Array Nat :=
  if rigUFix.getD c 0 == 1 then compA 1782 qProds[2]! (cWord (rigUWords.getD c []))
  else cWord (rigUWords.getD c [])

@[expose] def rigRTabs : Array (Array (Array Nat)) :=
  Array.ofFn (n := 16) fun c => Array.ofFn (n := 128) fun j =>
    compA 1782 (rigUTab c.val) qElts[j.val]!

@[expose] def rigRTab (c j : Nat) : Array Nat := (rigRTabs[c]!)[j]!

@[expose] def rigTTab (i : Nat) : Array Nat :=
  match rigGens.getD i (0, [], 0, 0) with
  | (_, _, c, j) => rigRTab c j

@[expose] def rigSTab (s : Nat) : Array Nat :=
  match rigSeeds.getD s (0, 0) with
  | (c, j) => rigRTab c j

@[expose] def rigProdTabs : Array (Array Nat) :=
  Array.ofFn (n := 256) fun m => (List.range 8).foldl
    (fun acc i => if m.val.testBit i then compA 1782 acc (rigTTab i) else acc) (idA 1782)

@[expose] def rigEqComp (x p q : Array Nat) : Bool := allLt 1782 fun y => x[y]! == p[q[y]!]!

@[expose] def rigComm (x y : Array Nat) : Bool := allLt 1782 fun z => x[y[z]!]! == y[x[z]!]!

@[expose] def rigCommV (x y : Array Nat) : Bool :=
  anyBelow 4 fun i => allLt 1782 fun z => x[y[z]!]! == (qElts[i]!)[y[x[z]!]!]!

@[expose] def rigModV (x s : Array Nat) : Bool := anyBelow 4 fun i => rigEqComp x s qElts[i]!

@[expose] def rigInV (x : Array Nat) : Bool := anyBelow 4 fun i => eqA 1782 x qElts[i]!

@[expose] def rigBil (v : Nat) : Nat := (gammaBit v 1 + gammaBit 1 v) % 2

@[expose] def rigUTest (t : Tab) : Bool :=
  t[1]! == 1 && allLt 64 fun v => rigBil v != 0 || t[v]! == v || t[v]! == (v ^^^ 1)

@[expose] def rigAgree (t m : Tab) : Bool :=
  allLt 64 fun v => rigBil v != 0 || t[v]! == m[v]! || t[v]! == (m[v]! ^^^ 1)

@[expose] def rigLiftOK : Bool :=
  (List.range 16).all fun c => (rigUWords.getD c []).all (fun k => decide (k < 10)) &&
    rigComm (rigUTab c) w0Tab && rigUTest (matWord (rigUWords.getD c [])) &&
    (rigUFix.getD c 0 == 0 || rigUFix.getD c 0 == 1)

@[expose] def rigUCompleteOK : Bool :=
  allLt 25920 fun i => !(rigUTest matEnum.tabs[i]!) ||
    anyBelow 16 fun c => matEnum.tabs[i]! == matWord (rigUWords.getD c [])

@[expose] def rigGenOK : Bool :=
  (List.range 8).all fun i => match rigGens.getD i (0, [], 0, 0) with
    | (s, u, c, j) => decide (s < 2) && decide (c < 16) && decide (j < 128) &&
        u.all (fun k => decide (k < 10)) && rigComm (cWord u) w0Tab &&
        rigComm (rigRTab c j) w0Tab &&
        allLt 1782 fun z => (cWord u)[(rigSTab s)[z]!]! == (rigRTab c j)[(cWord u)[z]!]!

@[expose] def rigCommOK : Bool :=
  (List.range 8).all fun i => (List.range 8).all fun k => rigCommV (rigTTab i) (rigTTab k)

@[expose] def rigDecompOK : Bool :=
  (List.range 16).all fun c => allLt 128 fun j => !(rigComm (rigRTab c j) w0Tab) ||
    anyBelow 256 fun m => anyBelow 4 fun i => rigEqComp (rigRTab c j) rigProdTabs[m]! qElts[i]!

@[expose] def rigCenterOK : Bool :=
  (List.range 16).all fun c => allLt 128 fun j => !(rigComm (rigRTab c j) w0Tab) ||
    !((List.range 8).all fun i => rigComm (rigRTab c j) (rigTTab i)) || (c == 0 && j < 4)

@[expose] def rigStabOK : Bool :=
  (List.range 2).all fun s => match rigSeeds.getD s (0, 0) with
    | (c₀, j₀) => decide (c₀ < 16) && decide (j₀ < 128) && rigComm (rigRTab c₀ j₀) w0Tab &&
      rigInV (compA 1782 (rigSTab s) (rigSTab s)) &&
      (rigGam.getD s []).all (fun g => g.all (fun k => decide (k < 10)) &&
        rigComm (cWord g) w0Tab && rigCommV (cWord g) (rigSTab s)) &&
      (List.range 16).all fun c => allLt 128 fun j => !(rigComm (rigRTab c j) w0Tab) ||
        !((rigGam.getD s []).all fun g => rigCommV (cWord g) (rigRTab c j)) ||
        !(eqA 1782 (compA 1782 (rigRTab c j) (rigRTab c j))
          (compA 1782 (rigSTab s) (rigSTab s))) ||
        rigModV (rigRTab c j) (rigSTab s)

@[expose] def rigX1OK : Bool :=
  rigX1.all (fun k => decide (k < 10)) && rigComm (cWord rigX1) w0Tab &&
    eqA 1782 (cWord (rigX1 ++ rigX1 ++ rigX1 ++ rigX1 ++ rigX1)) (idA 1782) &&
    (List.range 16).all fun c => allLt 128 fun j => !(rigComm (rigRTab c j) w0Tab) ||
      !(rigCommV (rigRTab c j) (cWord rigX1)) || (c == 0 && j < 4)

@[expose] def rigX2OK : Bool :=
  rigX2.all (fun k => decide (k < 10)) && rigComm (cWord rigX2) w0Tab &&
    rigUTest (matWord (rigX2 ++ rigX2 ++ rigX2))

@[expose] def rigBfsOK : Bool :=
  let W := rigBfs.map fun u => matWord (rigExpand u)
  allLt 25920 fun i => (matEnum.tabs[i]!)[1]! != 1 || W.any fun m => rigAgree matEnum.tabs[i]! m

@[expose] def rigXor (b : List Nat) (m : Nat) : Nat :=
  ((List.range b.length).filter fun k => m.testBit k).foldl (fun acc k => acc ^^^ b.getD k 0) 0

@[expose] def rigIrredOK : Bool :=
  let W := rigIrrWords.map fun u => matWord (rigExpand u)
  allLt 64 fun v => rigBil v != 0 || v == 0 || v == 1 ||
    let b := 1 :: W.map fun m => m[v]!
    allLt 64 fun u => rigBil u != 0 || anyBelow 512 fun m => rigXor b m == u

end CFSG.Sporadic.SuzRecog.RigidL2
