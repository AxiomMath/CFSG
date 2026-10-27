module

public import CFSG.Quasithin.Background.SmithB45Alt7IndData
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.X3ECheck

public section

namespace CFSG.Quasithin.B45Alt7

open CFSG.QuasithinUnique.Setup.X3E

@[expose] def g7N (b : Bool) (k : Nat) : Nat :=
  if b then (k + 1) % 7 else if k < 3 then (k + 1) % 3 else k

@[expose] def cosW (b : Bool) (k : Nat) : List Bool := if b then [] else a7CosW.getD k []

@[expose] def rB (c : Bool) : Nat := if c then 2 else 0

@[expose] def indCols (c b : Bool) : List Nat :=
  (List.range 28).map fun j =>
    wapp 4 (blkOf (rB c)) (cosW b (j / 4)) (1 <<< (j % 4)) <<< (4 * g7N b (j / 4))

@[expose] def indB (c : Bool) : List Nat := if c then indB1 else indB0

@[expose] def indT (c : Bool) : List Nat := if c then indT1 else indT0

@[expose] def indM (c b : Bool) : List Nat :=
  if c then (if b then indMb1 else indMa1) else (if b then indMb0 else indMa0)

@[expose] def indNs (c : Bool) : List Nat := if c then indNs1 else indNs0

@[expose] def indSteps (c : Bool) : Nat := if c then 3 else 2

@[expose] def indBlk (c : Bool) (i : Nat) (b : Bool) : List Nat :=
  blkCols (indM c b) ((indNs c).getD i 0) ((indNs c).getD (i + 1) 0 - (indNs c).getD i 0)

@[expose] def baseOK (c : Bool) : Bool :=
  (List.range 28).all (fun i => papply 28 (indB c) ((indT c).getD i 0) == 1 <<< i) &&
    (List.range 28).all (fun j => papply 28 (indB c) ((indM c false).getD j 0) ==
      papply 28 (indCols c false) ((indB c).getD j 0)) &&
    (List.range 28).all (fun j => papply 28 (indB c) ((indM c true).getD j 0) ==
      papply 28 (indCols c true) ((indB c).getD j 0))

@[expose] def flagOK (c : Bool) : Bool :=
  (indNs c).length == indSteps c + 1 && (indNs c).getD 0 0 == 0 &&
    (indNs c).getD (indSteps c) 0 == 28 &&
    (List.range (indSteps c)).all (fun i => (indNs c).getD i 0 < (indNs c).getD (i + 1) 0) &&
    (List.range (indSteps c + 1)).all fun i => (List.range ((indNs c).getD i 0)).all fun j =>
      (indM c false).getD j 0 < 2 ^ (indNs c).getD i 0 &&
        (indM c true).getD j 0 < 2 ^ (indNs c).getD i 0

@[expose] def nortonAt (c : Bool) (i : Nat) : Bool :=
  if c then
    nortonOK ((indNs c).getD (i + 1) 0 - (indNs c).getD i 0) (indBlk c i) (indAW1.getD i [])
      (indKers1.getD i []) (indPsi1.getD i 0) (indDw1.getD i []) (indRc1.getD i [])
      (indMinv1.getD i [])
  else
    nortonOK ((indNs c).getD (i + 1) 0 - (indNs c).getD i 0) (indBlk c i) (indAW0.getD i [])
      (indKers0.getD i []) (indPsi0.getD i 0) (indDw0.getD i []) (indRc0.getD i [])
      (indMinv0.getD i [])

@[expose] def blocksOK (c : Bool) : Bool := (List.range (indSteps c)).all fun i => nortonAt c i

@[expose] def conjOK : Bool :=
  [(5, 0), (8, 0), (6, 2), (10, 2)].all fun p =>
    (List.range 4).all (fun k => papply 4 (indP p.1) ((indQ p.1).getD k 0) == 1 <<< k) &&
    [false, true].all fun b => (List.range 4).all fun k =>
      papply 4 (blkOf p.1 b) ((indQ p.1).getD k 0) == papply 4 (indQ p.1) ((blkOf p.2 b).getD k 0)

@[expose] def regOK : Bool :=
  [0, 1].all fun i => [5, 10, 15].all fun v =>
    wapp 4 (indBlk true i) (regW.getD 0 []) v == v && wapp 4 (indBlk true i) (regW.getD 1 []) v == v

theorem baseOK_false : baseOK false = true := by decide +kernel

theorem baseOK_true : baseOK true = true := by decide +kernel

theorem flagOK_false : flagOK false = true := by decide +kernel

theorem flagOK_true : flagOK true = true := by decide +kernel

theorem blocksOK_false : blocksOK false = true := by decide +kernel

theorem blocksOK_true : blocksOK true = true := by decide +kernel

theorem conjOK_true : conjOK = true := by decide +kernel

theorem regOK_true : regOK = true := by decide +kernel

end CFSG.Quasithin.B45Alt7
