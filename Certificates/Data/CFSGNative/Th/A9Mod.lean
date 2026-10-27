module

public section

namespace CFSG.Sporadic.Th.Recog.A9Mod

set_option compiler.extract_closed false

abbrev Mat := Array Nat

@[expose] def mv (m : Mat) (v : Nat) : Nat :=
  ((if v.testBit 0 then m.getD 0 0 else 0) ^^^ (if v.testBit 1 then m.getD 1 0 else 0) ^^^
    (if v.testBit 2 then m.getD 2 0 else 0) ^^^ (if v.testBit 3 then m.getD 3 0 else 0) ^^^
    (if v.testBit 4 then m.getD 4 0 else 0) ^^^ (if v.testBit 5 then m.getD 5 0 else 0) ^^^
    (if v.testBit 6 then m.getD 6 0 else 0) ^^^ (if v.testBit 7 then m.getD 7 0 else 0)) &&& 255

@[expose] def mm (a b : Mat) : Mat := b.map (mv a)

@[expose] def eqM (a b : Mat) : Bool := (List.range 8).all fun j => a.getD j 0 == b.getD j 0

@[expose] def idM : Mat := #[1, 2, 4, 8, 16, 32, 64, 128]

@[expose] def mpow (a : Mat) : Nat → Mat
  | 0 => idM
  | k + 1 => mm (mpow a k) a

@[expose] def evalW (gs : Array Mat) (w : List Nat) : Mat :=
  w.foldl (fun r i => mm r (gs.getD i idM)) idM

@[expose] def withInv (gs : Array Mat) : Array Mat :=
  #[gs.getD 0 idM, gs.getD 1 idM, gs.getD 2 idM, gs.getD 3 idM,
    mpow (gs.getD 0 idM) 8, mpow (gs.getD 1 idM) 5, gs.getD 2 idM, mpow (gs.getD 3 idM) 2]

@[expose] def relsOK (gs : Array Mat) (rels : List (List Nat)) : Bool :=
  let gi := withInv gs
  rels.all fun r => eqM (evalW gi r) idM

def inv? (a : Mat) : Option Mat := Id.run do
  let mut rows : Array Nat := #[]
  for i in [0:8] do
    let mut r := 1 <<< (8 + i)
    for j in [0:8] do
      if (a.getD j 0).testBit i then r := r ||| (1 <<< j)
    rows := rows.push r
  for c in [0:8] do
    let mut p := 8
    for r in [c:8] do
      if p == 8 && (rows[r]!).testBit c then p := r
    if p == 8 then return none
    let tmp := rows[c]!
    rows := rows.set! c rows[p]!
    rows := rows.set! p tmp
    for r in [0:8] do
      if r != c && (rows[r]!).testBit c then rows := rows.set! r (rows[r]! ^^^ rows[c]!)
  let mut out : Mat := #[]
  for j in [0:8] do
    let mut col := 0
    for i in [0:8] do
      if (rows[i]!).testBit (8 + j) then col := col ||| (1 <<< i)
    out := out.push col
  return some out

@[expose] def rinv? (w : Mat) : Option Mat :=
  match inv? w with
  | some wi => if eqM (mm w wi) idM then some wi else none
  | none => none

@[expose] def fixList (m : Mat) : List Nat := (List.range 256).filter fun v => mv m v == v

@[expose] def isInj (p : Mat) : Bool := (List.range 255).all fun v => mv p (v + 1) != 0

def reduce (basis : List Nat) (v : Nat) : Nat := basis.foldl (fun x b => min x (x ^^^ b)) v

def greedy (rl : Array Mat) (x lim : Nat) : List Nat := Id.run do
  let mut basis : List Nat := []
  let mut items : List Nat := []
  for j in [0:rl.size] do
    if items.length < lim then
      let r := reduce basis (mv (rl.getD j idM) x)
      if r != 0 then
        basis := (r :: basis).mergeSort fun a b => decide (a ≥ b)
        items := items ++ [j]
  return items

@[expose] def N1 : Mat := #[2, 4, 8, 16, 32, 9, 128, 192]

@[expose] def N2 : Mat := #[2, 4, 8, 16, 32, 9, 64, 128]

@[expose] def W1 : Mat := #[65, 130, 196, 72, 144, 224, 73, 146]

@[expose] def W1inv : Mat := #[72, 144, 223, 65, 130, 251, 73, 146]

@[expose] def relsK1 : List (List Nat) :=
  [[1, 4, 5, 0, 0],
    [1, 1, 1, 1, 1, 1],
    [1, 1, 4, 4, 5, 5, 4]]

@[expose] def relsK2 : List (List Nat) :=
  [[2, 2],
    [4, 1, 0, 5, 4],
    [4, 1, 1, 4, 2, 4, 4, 2],
    [4, 2, 0, 0, 5, 0, 5, 0, 2],
    [0, 5, 0, 2, 1, 0, 2, 0, 5, 2]]

@[expose] def relsA9 : List (List Nat) :=
  [[2, 2],
    [3, 3, 3],
    [1, 0, 5, 4, 4],
    [1, 4, 1, 2, 0, 2],
    [5, 5, 2, 1, 1, 2],
    [5, 0, 1, 1, 0, 0, 5],
    [3, 5, 0, 3, 4, 2, 4, 2],
    [2, 4, 4, 4, 2, 4, 4, 4],
    [0, 5, 0, 2, 0, 5, 0, 2, 0, 5, 0, 2],
    [0, 0, 2, 1, 0, 2, 7, 4, 2, 4, 1, 2, 3],
    [2, 4, 4, 4, 4, 3, 2, 7, 2, 0, 1, 0, 2, 5, 2, 0, 3, 5, 3, 2, 0, 0, 3],
    [3, 4, 3, 5, 3, 2, 0, 0, 3, 4, 3, 4, 3, 1, 7, 2, 0, 7, 5, 3, 1, 3, 2],
    [7, 0, 7, 4, 4, 2, 7, 1, 7, 0, 3, 2, 7, 0, 7, 4, 4, 2, 7, 1, 7, 0, 3, 2],
    [0, 2, 5, 0, 3, 1, 7, 2, 0, 7, 5, 3, 1, 0, 2, 5, 0, 3, 1, 7, 2, 0, 7, 5, 3, 1],
    [1, 4, 2, 7, 4, 4, 2, 7, 1, 7, 0, 2, 7, 2, 4, 3, 5, 3, 2, 0, 0, 3, 2, 0, 5, 3],
    [7, 1, 4, 1, 4, 1, 7, 4, 3, 5, 3, 2, 0, 0, 3, 4, 7, 2, 7, 2, 4, 5, 4, 5, 5, 3, 2],
    [7, 2, 3, 2, 5, 7, 1, 3, 2, 0, 7, 4, 7, 0, 3, 2, 7, 5, 4, 5, 3, 2, 7, 2, 4, 1, 3, 2, 3, 2],
    [5, 7, 1, 3, 2, 0, 7, 4, 7, 0, 5, 7, 1, 3, 2, 0, 7, 4, 7, 0, 5, 7, 1, 3, 2, 0, 7, 4, 7, 0],
    [3, 1, 4, 2, 7, 4, 4, 2, 7, 1, 7, 0, 7, 2, 5, 7, 1, 3, 2, 0, 7, 4, 7, 0, 2, 3, 2, 7, 2, 4, 3,
      5, 3, 2, 0, 0, 3, 4],
    [5, 7, 1, 3, 2, 0, 7, 4, 7, 0, 2, 3, 2, 7, 2, 3, 2, 7, 2, 3, 2, 7, 4, 2, 4, 7, 1, 3, 2, 0, 7,
      4, 7, 0, 3, 2, 7, 2],
    [5, 7, 1, 3, 2, 0, 7, 4, 7, 5, 4, 5, 5, 3, 2, 7, 2, 4, 3, 5, 3, 2, 0, 0, 3, 4, 4, 3, 1, 7, 2,
      0, 7, 5, 3, 1, 0, 7, 4, 4, 2, 7, 1, 7, 0, 2],
    [1, 3, 2, 7, 2, 0, 1, 7, 4, 4, 2, 7, 1, 7, 0, 2, 3, 1, 4, 2, 4, 7, 4, 3, 1, 7, 2, 0, 7, 5, 3,
      1, 2, 4, 3, 5, 3, 2, 0, 0, 3, 4, 3, 2, 7, 2, 4]]

@[expose] def wordH : List Nat := [0, 1, 1, 0, 1, 1]

@[expose] def wordsL : List (List Nat × List Nat) :=
  [([], []),
   ([0, 2, 1, 2, 0], [0, 2, 1, 2, 0]),
   ([2, 1, 0, 1], [2, 1, 0, 1]),
   ([0, 1, 0, 0, 0, 2], [0, 1, 0, 0, 0, 2]),
   ([0, 2, 1, 0], [0, 2, 1, 0]),
   ([1, 0, 1, 1], [1, 0, 1, 1]),
   ([0, 0, 0], [0, 1, 2]),
   ([1, 1, 2, 1, 2], [0, 0, 2, 0]),
   ([0, 0, 2, 0], [0, 1, 1, 0, 1]),
   ([0, 1, 2], [1, 1, 0, 0, 2, 1]),
   ([1, 1, 0, 0, 2, 1], [0, 0, 0]),
   ([0, 1, 1, 0, 1], [1, 1, 2, 1, 2]),
   ([2, 0, 0, 0, 2], [1, 0, 1, 2, 1]),
   ([1, 0, 2, 0, 1], [1, 1, 1, 0]),
   ([2, 0, 1, 1, 0], [1, 0, 2, 0, 1]),
   ([1, 0, 0, 2], [2, 0, 0, 0, 2]),
   ([1, 0, 1, 2, 1], [1, 0, 0, 2]),
   ([1, 1, 1, 0], [2, 0, 1, 1, 0])]

@[expose] def wordA : List Nat := [1, 1, 3, 2, 3, 2, 0, 3, 0, 3, 0]

@[expose] def wordB : List Nat := [3, 0, 0, 2, 3, 0, 3, 1, 3, 3, 2]

@[expose] def wordB' : List Nat := [0, 1, 1, 3, 2, 1, 3, 1, 3, 2, 1, 3, 1]

@[expose] def wordGab : List Nat :=
  [1, 0, 1, 1, 1, 0, 1, 0, 1, 0, 1, 1, 1, 0, 1, 0, 1, 1, 1, 0, 1, 1, 1, 0]

@[expose] def wordGab' : List Nat :=
  [0, 1, 0, 1, 1, 0, 1, 1, 1, 0, 1, 1, 0, 1, 1, 1, 0, 1, 0, 1, 1, 0, 1, 0, 1, 0, 1, 1, 0]

@[expose] def B1M : Mat := #[2, 1, 8, 4, 64, 128, 16, 32]

@[expose] def B2M : Mat := #[2, 150, 1, 222, 4, 8, 82, 248]

@[expose] def P8A : Mat := #[2, 1, 8, 4, 32, 16, 128, 64]

@[expose] def P8B : Mat := #[129, 128, 130, 144, 136, 132, 160, 192]

@[expose] def pows (X : Mat) : Array Mat := Array.ofFn (n := 8) fun k => mpow X k.val

@[expose] def pairs (case : Nat) (X : Mat) : List (Nat × Nat) :=
  if case == 1 then [(0, 0)] else
    let f := fixList X
    f.flatMap fun a => f.map fun b => (a, b)

@[expose] def spinNF (case : Nat) (xs : Array Mat) (u a b : Nat) : Mat :=
  if case == 1 then mm (xs.map fun m => mv m u) W1inv
  else #[mv (xs.getD 0 idM) u, mv (xs.getD 1 idM) u, mv (xs.getD 2 idM) u,
    mv (xs.getD 3 idM) u, mv (xs.getD 4 idM) u, mv (xs.getD 5 idM) u, a, b]

@[expose] def rlOf (gs : Array Mat) : Array Mat :=
  (wordsL.map fun p => evalW (withInv gs) p.1).toArray

@[expose] def rlpOf (gs : Array Mat) : Array Mat :=
  (wordsL.map fun p => evalW (withInv gs) p.2).toArray

@[expose] def oneSpin (rl : Array Mat) : Option (List Nat × Mat) :=
  (List.range 255).findSome? fun x =>
    let items := greedy rl (x + 1) 8
    if items.length == 8 then
      (rinv? (items.map fun j => mv (rl.getD j idM) (x + 1)).toArray).map fun wi => (items, wi)
    else none

@[expose] def twoSpin (rl : Array Mat) (cl : List Nat) : Option (List Nat × Mat) :=
  (List.range 255).findSome? fun x =>
    let items := greedy rl (x + 1) 7
    if items.length == 7 then
      cl.findSome? fun y =>
        (rinv? (y :: items.map fun j => mv (rl.getD j idM) (x + 1)).toArray).map
          fun wi => (items, wi)
    else none

@[expose] def fixAll (rl : Array Mat) : List Nat :=
  (List.range 256).filter fun v => rl.all fun m => mv m v == v

@[expose] def stage3core (rl rlp : Array Mat) : Option (List Mat) :=
  match oneSpin rl with
  | some r =>
      some ((List.range 256).map fun u => mm (r.1.map fun j => mv (rlp.getD j idM) u).toArray r.2)
  | none =>
      let clp := fixAll rlp
      (twoSpin rl (fixAll rl)).map fun r =>
        (List.range 256).flatMap fun u => clp.map fun u2 =>
          mm (u2 :: r.1.map fun j => mv (rlp.getD j idM) u).toArray r.2

@[expose] def stage3 (gs : Array Mat) : Option (List Mat) := stage3core (rlOf gs) (rlpOf gs)

@[expose] def conjTarget (case : Nat) (ra rb t1 t2 : Mat) (wg : List Nat) : Bool :=
  let tg := evalW #[t1, t2] wg
  let tp := pows tg
  let pr := pairs case tg
  (List.range 256).any fun y => pr.any fun ab =>
    let p := spinNF case tp y ab.1 ab.2
    eqM (mm p ra) (mm t1 p) && eqM (mm p rb) (mm t2 p) && isInj p

@[expose] def conjOK (case : Nat) (gs : Array Mat) : Bool :=
  let gi := withInv gs
  conjTarget case (evalW gi wordA) (evalW gi wordB) B1M B2M wordGab ||
    conjTarget case (evalW gi wordA) (evalW gi wordB') B1M B2M wordGab' ||
    conjTarget case (evalW gi wordA) (evalW gi wordB) P8A P8B wordGab

@[expose] def nOf (case : Nat) : Mat := if case == 1 then N1 else N2

@[expose] def stage4 (case : Nat) (n m1 m2 : Mat) : Bool :=
  match stage3 #[n, m1, m2, idM] with
  | none => false
  | some cands => cands.all fun m3 =>
      !relsOK #[n, m1, m2, m3] relsA9 || conjOK case #[n, m1, m2, m3]

@[expose] def stage2 (case : Nat) (n m1 : Mat) : Bool :=
  let h := evalW (withInv #[n, m1, idM, idM]) wordH
  let hp := pows h
  let pr2 := pairs case h
  (List.range 256).all fun u2 => pr2.all fun ab =>
    let m2 := spinNF case hp u2 ab.1 ab.2
    !relsOK #[n, m1, m2, idM] relsK2 || stage4 case n m1 m2

@[expose] def checkCase (case : Nat) : Bool :=
  let n := nOf case
  let n2 := mm n n
  let n2p := pows n2
  let pr1 := pairs case n2
  (List.range 256).all fun u1 => pr1.all fun ab =>
    let m1 := spinNF case n2p u1 ab.1 ab.2
    !relsOK #[n, m1, idM, idM] relsK1 || stage2 case n m1

@[expose] def check (_ : Unit := ()) : Bool := checkCase 1 && checkCase 2

end CFSG.Sporadic.Th.Recog.A9Mod
