module

public section

namespace CFSG.CGT.PushingUpLit.SolK.S5Mod

@[expose] def maskOf (p : Nat → Bool) : Nat → Nat
  | 0 => 0
  | n + 1 => maskOf p n + if p n then 2 ^ n else 0

@[expose] def dImg : List (List Nat) :=
  [[0, 1, 2, 3, 4], [1, 0, 2, 3, 4], [0, 1, 3, 2, 4], [1, 0, 3, 2, 4],
    [2, 3, 0, 1, 4], [2, 3, 1, 0, 4], [3, 2, 0, 1, 4], [3, 2, 1, 0, 4]]

@[expose] def compL (l l' : List Nat) : List Nat := l'.map fun y => l.getD y 0

@[expose] def mulTab : List (List Nat) :=
  (List.range 8).map fun i => (List.range 8).map fun j =>
    dImg.findIdx (· == compL (dImg.getD i []) (dImg.getD j []))

@[expose] def mulD (i j : Nat) : Nat := (mulTab.getD i []).getD j 0

@[expose] def par4 (b : Nat) : Nat := (b ^^^ (b >>> 1) ^^^ (b >>> 2) ^^^ (b >>> 3)) &&& 1

@[expose] def vec5 (a : Nat) : Nat := a % 16 + 16 * par4 (a % 16)

@[expose] def actBits (l : List Nat) (x : Nat) : Nat :=
  (List.range 5).foldl (fun acc p => acc ||| (((x >>> p) &&& 1) <<< l.getD p 0)) 0

@[expose] def actTab : List (List Nat) :=
  (List.range 8).map fun i => (List.range 16).map fun a =>
    actBits (dImg.getD i []) (vec5 a) % 16

@[expose] def actD (i a : Nat) : Nat := (actTab.getD i []).getD a 0

@[expose] def addVec (m v : Nat) : Nat := maskOf (fun w => m.testBit w || m.testBit (w ^^^ v)) 16

@[expose] def vspan (l : List Nat) : Nat := l.foldl addVec 1

@[expose] def stepD (m : Nat) : Nat :=
  maskOf (fun k => m.testBit k || (List.range 8).any fun i => (List.range 8).any fun j =>
    m.testBit i && m.testBit j && mulD i j == k) 8

@[expose] def closeD (gs : List Nat) : Nat :=
  stepD (stepD (stepD (maskOf (fun k => k == 0 || gs.contains k) 8)))

@[expose] def closedD (m : Nat) : Bool :=
  m.testBit 0 && (List.range 8).all fun i => (List.range 8).all fun j =>
    !(m.testBit i && m.testBit j) || m.testBit (mulD i j)

@[expose] def closedV (m : Nat) : Bool :=
  m.testBit 0 && (List.range 16).all fun a => (List.range 16).all fun b =>
    !(m.testBit a && m.testBit b) || m.testBit (a ^^^ b)

@[expose] def invV (hm lm : Nat) : Bool :=
  (List.range 8).all fun i => (List.range 16).all fun a =>
    !(hm.testBit i && lm.testBit a) || lm.testBit (actD i a)

@[expose] def hmList : List Nat := (List.range 256).filter closedD

@[expose] def lmList : List Nat := (List.range 65536).filter closedV

@[expose] def genCands (hm : Nat) : List (List Nat) :=
  let es := (List.range 8).filter fun i => hm.testBit i
  [] :: (es.map fun i => [i]) ++
    es.flatMap fun i => (es.filter fun j => i < j).map fun j => [i, j]

@[expose] def genOK (hm : Nat) (gs : List Nat) : Bool :=
  gs.all (fun i => i < 8 && hm.testBit i) &&
    (List.range 8).all fun k => !hm.testBit k || (closeD gs).testBit k

@[expose] def pickGs (hm : Nat) : List Nat := ((genCands hm).find? (genOK hm)).getD []

@[expose] def orbitList (hm : Nat) (ts : List Nat) : List Nat :=
  ((List.range 8).filter fun i => hm.testBit i).flatMap fun i => ts.map (actD i)

@[expose] def tsOK (hm lm : Nat) (ts : List Nat) : Bool :=
  ts.all (fun a => a < 16 && lm.testBit a) &&
    (List.range 16).all fun w => !lm.testBit w || (vspan (orbitList hm ts)).testBit w

@[expose] def radList (hm lm : Nat) : List Nat :=
  ((List.range 8).filter fun i => hm.testBit i).flatMap fun i =>
    ((List.range 16).filter fun a => lm.testBit a).map fun a => actD i a ^^^ a

@[expose] def pickTsAux (hm lm : Nat) : Nat → List Nat → List Nat
  | 0, ts => ts
  | k + 1, ts =>
    let cur := vspan (radList hm lm ++ orbitList hm ts)
    match (List.range 16).find? fun v => lm.testBit v && !cur.testBit v with
    | none => ts
    | some v => pickTsAux hm lm k (ts ++ [v])

@[expose] def pickTs (hm lm : Nat) : List Nat := pickTsAux hm lm 5 []

@[expose] def verify (hm lm : Nat) (gs ts : List Nat) : Bool :=
  decide (gs.length + ts.length ≤ 4) && genOK hm gs && tsOK hm lm ts

@[expose] def check : Bool :=
  hmList.all fun hm => lmList.all fun lm =>
    !invV hm lm || verify hm lm (pickGs hm) (pickTs hm lm)

end CFSG.CGT.PushingUpLit.SolK.S5Mod

namespace CFSG.CGT.PushingUpLit.SolK

@[expose] def S5ModCheck : Prop := S5Mod.check = true

end CFSG.CGT.PushingUpLit.SolK
