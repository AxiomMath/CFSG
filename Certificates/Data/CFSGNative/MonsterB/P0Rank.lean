module

public section

namespace MonsterB.P0Rank

set_option compiler.extract_closed false

@[expose] def colsAct : List Nat → Nat → Nat
  | [], _ => 0
  | c :: cs, x => (if x % 2 = 1 then c else 0) ^^^ colsAct cs (x / 2)

@[expose] def colsOf (n : Nat) (f : Nat → Nat) : List Nat :=
  (List.range n).map fun b => f (2 ^ b)

@[expose] def actK (cols : List (List Nat)) (κ x : Nat) : Nat :=
  (List.range cols.length).foldr
    (fun k y => if κ.testBit k then colsAct (cols.getD k []) y else y) x

@[expose] def par (x : Nat) : Bool :=
  if h : x = 0 then false else (x % 2 == 1) ^^ par (x / 2)
termination_by x
decreasing_by exact Nat.div_lt_self (Nat.pos_of_ne_zero h) (by decide)

@[expose] def maskT : List Nat → Nat → Nat
  | [], _ => 0
  | c :: cs, k => (if c.testBit k then 1 else 0) + 2 * maskT cs k

@[expose] def maskOf (l : List Nat) : Nat := l.foldl (fun m x => m ||| 2 ^ x) 0

structure Data where
  beta : List (List Nat)
  uConjL : List (List (Nat × Nat))
  uConjT : List (List Nat)
  uSq : List (Nat × Nat)
  uComm : List (List (Nat × Nat))

@[expose] def Data.aCols (dat : Data) : List (List Nat) := dat.uConjL.map (·.map (·.1))

@[expose] def qN (beta : List (List Nat)) (σ : Nat) : Nat :=
  (List.range 16).foldl
    (fun acc j => if σ.testBit j then acc ^^^ colsAct ((beta.getD j []).take j) σ else acc) 0

@[expose] def betaN (beta : List (List Nat)) (σ δ : Nat) : Nat :=
  colsAct ((List.range 16).map fun i => colsAct (beta.getD i []) δ) σ

@[expose] def swalk {α : Type} (cands : α → List Nat) (upd : α → Nat → α)
    (visit : List Nat → α → Bool) : Nat → List Nat → Nat → α → Bool
  | 0, _, _, _ => false
  | fuel + 1, node, top, a =>
    visit node a && (cands a).all fun v =>
      if 2 ^ top ≤ v && node.all (fun x => v ≤ v ^^^ x) then
        swalk cands upd visit fuel (node ++ node.map (v ^^^ ·)) (Nat.log2 v + 1) (upd a v)
      else true

@[expose] def swalkL {α β : Type} (cands : α → List Nat) (upd : α → Nat → α)
    (visit : List Nat → α → List β) : Nat → List Nat → Nat → α → List β
  | 0, _, _, _ => []
  | fuel + 1, node, top, a =>
    visit node a ++ (cands a).flatMap fun v =>
      if 2 ^ top ≤ v && node.all (fun x => v ≤ v ^^^ x) then
        swalkL cands upd visit fuel (node ++ node.map (v ^^^ ·)) (Nat.log2 v + 1) (upd a v)
      else []

@[expose] def embCols : List Nat := [8, 32, 64, 128, 256]

@[expose] def emb (z : Nat) : Nat := colsAct embCols z

@[expose] def lamList (_ : Unit := ()) : List Nat := (List.range 16).map (colsAct [1, 2, 12, 48])

@[expose] def ylist (_ : Unit := ()) : List (List Nat) :=
  swalkL (fun _ : Unit => List.range 32) (fun _ _ => ()) (fun node _ => [node]) 6 [0] 0 ()

@[expose] def ycover (yl : List (List Nat)) : Bool :=
  swalk (fun _ : Unit => List.range 32) (fun _ _ => ())
    (fun node _ => let m := maskOf node; yl.any fun e => maskOf e == m) 6 [0] 0 ()

@[expose] def lamOK (dat : Data) : Bool :=
  let lam := lamList ()
  ((List.range 1024).all fun κ => lam.all fun l => actK dat.uConjT κ l == l) &&
  (List.range 512).all fun τ =>
    lam.any fun l => (List.range 32).any fun z => l ^^^ emb z == τ

@[expose] def inCU (dat : Data) (e : List Nat) (κ : Nat) : Bool :=
  e.all fun z => actK dat.uConjT κ (emb z) == emb z

@[expose] def yTab (dat : Data) (yl : List (List Nat)) : List (List Nat × Array Bool × Nat) :=
  yl.map fun e =>
    let cu := (List.range 1024).map (inCU dat e)
    (e, cu.toArray, cu.count true)

inductive Fact where
  | sq (κ s t : Nat)
  | comm (κ κ' s t : Nat)
  | conj (κ δ c : Nat)
  deriving DecidableEq, Inhabited

@[expose] def findSq (F : List Fact) (κ : Nat) : Option Nat :=
  F.findSome? fun
    | .sq a s _ => if a = κ then some s else none
    | _ => none

@[expose] def findComm (F : List Fact) (κ κ' : Nat) : Option Nat :=
  F.findSome? fun
    | .comm a b s _ => if a = κ ∧ b = κ' then some s else none
    | _ => none

@[expose] def findConj (F : List Fact) (κ δ : Nat) : Option Nat :=
  F.findSome? fun
    | .conj a d c => if a = κ ∧ d = δ then some c else none
    | _ => none

@[expose] def blockRows (w : Nat) (terms : List (Nat × List Nat)) (rhs : Nat) :
    List (List (Nat × Nat) × Bool) :=
  (List.range w).map fun k => (terms.map fun t => (t.1, maskT t.2 k), rhs.testBit k)

@[expose] def c1 (dat : Data) (κ : Nat) : List Nat := colsOf 16 fun x => x ^^^ actK dat.aCols κ x

@[expose] def sysBlocks (dat : Data) (F : List Fact) (ds ks : List Nat) :
    List ((Nat × Nat × Nat) × List (List (Nat × Nat) × Bool)) :=
  let a := ks.length
  let e1 := (List.range a).flatMap fun j =>
    match findSq F (ks.getD j 0) with
    | some s => [((0, j, 0), blockRows 16 [(j, c1 dat (ks.getD j 0))] s)]
    | none => []
  let e2 := (List.range a).flatMap fun j => ((List.range a).filter (j < ·)).flatMap fun k =>
    match findComm F (ks.getD j 0) (ks.getD k 0) with
    | some s => [((1, j, k), blockRows 16 [(j, c1 dat (ks.getD k 0)), (k, c1 dat (ks.getD j 0))] s)]
    | none => []
  let e3 := (List.range ds.length).flatMap fun i => (List.range a).flatMap fun j =>
    match findConj F (ks.getD j 0) (ds.getD i 0) with
    | some c => [((2, i, j), blockRows 9 [(j, colsOf 16 fun x => betaN dat.beta x (ds.getD i 0)),
        (a + i, colsOf 9 fun x => x ^^^ actK dat.uConjT (ks.getD j 0) x)] c)]
    | none => []
  e1 ++ e2 ++ e3

@[expose] def sysRows (dat : Data) (F : List Fact) (ds ks : List Nat) :
    List (List (Nat × Nat) × Bool) :=
  (sysBlocks dat F ds ks).flatMap (·.2)

@[expose] def farkasOK (nv : Nat) (rows : List (List (Nat × Nat) × Bool)) (sel : List Bool) :
    Bool :=
  let ch := (rows.zip sel).filterMap fun p => if p.2 then some p.1 else none
  ch.foldl (fun b r => b ^^ r.2) false &&
    (rows.all fun r => r.1.all fun t => t.1 < nv) &&
    (List.range nv).all fun v =>
      ch.foldl (fun m r => r.1.foldl (fun m t => if t.1 = v then m ^^^ t.2 else m) m) 0 == 0

@[expose] def packRow (r : List (Nat × Nat) × Bool) : Nat :=
  r.1.foldl (fun x t => x ^^^ (t.2 <<< (16 * t.1))) 0

@[expose] def gaussReduce : Nat → List (Nat × Nat × Bool × Nat) → Nat → Bool → Nat →
    List (Nat × Nat × Bool × Nat) ⊕ Nat
  | 0, piv, _, _, _ => .inl piv
  | fuel + 1, piv, x, r, c =>
    if x = 0 then (if r then .inr c else .inl piv)
    else
      let p := Nat.log2 x
      match piv.find? (·.1 = p) with
      | some (_, px, pr, pc) => gaussReduce fuel piv (x ^^^ px) (r ^^ pr) (c ^^^ pc)
      | none => .inl ((p, x, r, c) :: piv)

@[expose] def gaussGo (n fuel : Nat) : List (List (Nat × Nat) × Bool) → Nat →
    List (Nat × Nat × Bool × Nat) → Option (List Bool)
  | [], _, _ => none
  | row :: rest, i, piv =>
    match gaussReduce fuel piv (packRow row) row.2 (2 ^ i) with
    | .inr c => some ((List.range n).map c.testBit)
    | .inl piv' => gaussGo n fuel rest (i + 1) piv'

@[expose] def gaussSel (nv : Nat) (rows : List (List (Nat × Nat) × Bool)) : Option (List Bool) :=
  gaussGo rows.length (16 * nv + 1) rows 0 []

@[expose] def basisOf (l : List Nat) : List Nat :=
  l.foldl (fun bs x =>
    let r := bs.foldl (fun y b => min y (y ^^^ b)) x
    if r = 0 then bs else bs ++ [r]) []

@[expose] def basisIn (l : List Nat) : List Nat :=
  (basisOf (l.mergeSort fun a b => a ≤ b)).filter l.contains

@[expose] def farkasCase (dat : Data) (F : List Fact) (node ks : List Nat) : Bool :=
  let ds := basisIn node
  let kb := basisIn ks
  let nv := kb.length + ds.length
  let rows := sysRows dat F ds kb
  match gaussSel nv rows with
  | some sel => farkasOK nv rows sel
  | none => false

@[expose] def wwalk (dat : Data) (F : List Fact) (node M' : List Nat) (a : Nat) : Bool :=
  swalk (fun c : List Nat => c) (fun c v => let p := 2 ^ (Nat.log2 v + 1); c.filter (p ≤ ·))
    (fun V _ => a * V.length ≤ 2 ^ 14 || farkasCase dat F node V) 11 [0] 0 M'

@[expose] def candOK (dat : Data) (F : List Fact) (node M' : List Nat) (a : Nat) : Bool :=
  (a * M'.length ≤ 2 ^ 15 && farkasCase dat F node M') ||
    (a * M'.length ≤ 2 ^ 16 && wwalk dat F node M' a)

@[expose] def aMat (dat : Data) : Array (List Nat) :=
  ((List.range 1024).map fun κ => colsOf 16 (actK dat.aCols κ)).toArray

@[expose] def bRows (dat : Data) : Array (List Nat) :=
  ((List.range 65536).map fun v =>
    if qN dat.beta v = 0 then colsOf 16 (betaN dat.beta v) else []).toArray

@[expose] def singList (dat : Data) : List Nat :=
  (List.range 65536).filter fun w => w != 0 && qN dat.beta w == 0

@[expose] def dUpd (am br : Array (List Nat)) (s : List Nat × List Nat) (v : Nat) :
    List Nat × List Nat :=
  let p := 2 ^ (Nat.log2 v + 1)
  let r := br[v]!
  (s.1.filter (fun w => p ≤ w && colsAct r w == 0), s.2.filter fun κ => colsAct am[κ]! v == v)

@[expose] def dVisit (dat : Data) (F : List Fact) (yt : List (List Nat × Array Bool × Nat))
    (node : List Nat) (s : List Nat × List Nat) : Bool :=
  let M := s.2
  yt.all fun y =>
    let a := node.length * 16 * y.1.length
    a * M.length ≤ 2 ^ 14 || a * y.2.2 ≤ 2 ^ 14 ||
      (let M' := M.filter fun κ => y.2.1[κ]!
       a * M'.length ≤ 2 ^ 14 || candOK dat F node M' a)

@[expose] def p0Check (dat : Data) (F : List Fact) : Bool :=
  let yl := ylist ()
  let yt := yTab dat yl
  let am := aMat dat
  let br := bRows dat
  ycover yl && lamOK dat &&
    swalk (·.1) (dUpd am br) (dVisit dat F yt) 17 [0] 0 (singList dat, List.range 1024)

@[expose] def gam (beta : List (List Nat)) (s s' : Nat) : Nat :=
  (List.range 16).foldl (fun acc j =>
    if s'.testBit j then
      (List.range 16).foldl (fun acc i =>
        if j < i && s.testBit i then acc ^^^ (beta.getD i []).getD j 0 else acc) acc
    else acc) 0

@[expose] def lmul (beta : List (List Nat)) (x y : Nat × Nat) : Nat × Nat :=
  (x.1 ^^^ y.1, x.2 ^^^ y.2 ^^^ gam beta x.1 y.1)

@[expose] def linv (beta : List (List Nat)) (x : Nat × Nat) : Nat × Nat :=
  (x.1, x.2 ^^^ gam beta x.1 x.1)

@[expose] def conjk (dat : Data) (k : Nat) (x : Nat × Nat) : Nat × Nat :=
  (List.range 16).foldl (fun acc j =>
      if x.1.testBit j then lmul dat.beta acc ((dat.uConjL.getD k []).getD j (0, 0)) else acc)
    (0, colsAct (dat.uConjT.getD k []) x.2)

@[expose] def conjkap (dat : Data) (κ : Nat) (x : Nat × Nat) : Nat × Nat :=
  (List.range 10).foldr (fun k y => if κ.testBit k then conjk dat k y else y) x

@[expose] def moveleftR (dat : Data) (k : Nat) : List Nat → Nat × Nat
  | [] => (0, 0)
  | c :: rest =>
    let X := (dat.uComm.getD c []).getD k (0, 0)
    lmul dat.beta (rest.foldl (fun x c2 => conjk dat c2 x) X) (moveleftR dat k rest)

@[expose] def rmulU (dat : Data) (g : (Nat × Nat) × Nat) (k : Nat) : (Nat × Nat) × Nat :=
  let P := (List.range k).filter g.2.testBit
  let Q := (List.range 10).filter fun c => k < c && g.2.testBit c
  let Y := moveleftR dat k Q.reverse
  if g.2.testBit k then
    let z := lmul dat.beta (conjk dat k Y) (dat.uSq.getD k (0, 0))
    (lmul dat.beta g.1 (P.reverse.foldl (fun y c => conjk dat c y) z), g.2 ^^^ 2 ^ k)
  else
    (lmul dat.beta g.1 (P.reverse.foldl (fun y c => conjk dat c y) Y), g.2 ||| 2 ^ k)

@[expose] def pmul (dat : Data) (g h : (Nat × Nat) × Nat) : (Nat × Nat) × Nat :=
  ((List.range 10).filter h.2.testBit).foldl (rmulU dat)
    (lmul dat.beta g.1 (conjkap dat g.2 h.1), g.2)

@[expose] def colFacts (dat : Data) (ds ks : List Nat) : List Fact :=
  let u := fun κ : Nat => ((0, 0), κ)
  (ks.map fun κ => let g := pmul dat (u κ) (u κ); Fact.sq κ g.1.1 g.1.2) ++
  (ks.flatMap fun κ => ks.map fun κ' =>
    let g := pmul dat (u κ) (u κ')
    let h := pmul dat (u κ') (u κ)
    let x := lmul dat.beta g.1 (linv dat.beta h.1)
    Fact.comm κ κ' x.1 x.2) ++
  (ks.flatMap fun κ => ds.map fun δ => Fact.conj κ δ (conjkap dat κ (δ, 0)).2)

@[expose] def keyFact (dat : Data) (ds ks : List Nat) (key : Nat × Nat × Nat) : Fact :=
  let u := fun κ : Nat => ((0, 0), κ)
  match key with
  | (0, j, _) =>
    let κ := ks.getD j 0
    let g := pmul dat (u κ) (u κ)
    Fact.sq κ g.1.1 g.1.2
  | (1, j, k) =>
    let κ := ks.getD j 0
    let κ' := ks.getD k 0
    let x := lmul dat.beta (pmul dat (u κ) (u κ')).1 (linv dat.beta (pmul dat (u κ') (u κ)).1)
    Fact.comm κ κ' x.1 x.2
  | (_, i, j) =>
    let κ := ks.getD j 0
    let δ := ds.getD i 0
    Fact.conj κ δ (conjkap dat κ (δ, 0)).2

@[expose] def selKeys : List ((Nat × Nat × Nat) × List (List (Nat × Nat) × Bool)) → List Bool →
    List (Nat × Nat × Nat)
  | [], _ => []
  | b :: bl, sel =>
    let n := b.2.length
    (if (sel.take n).any id then [b.1] else []) ++ selKeys bl (sel.drop n)

@[expose] def supportFacts (dat : Data) (node ks : List Nat) : List Fact :=
  let ds := basisIn node
  let kb := basisIn ks
  let bl := sysBlocks dat (colFacts dat ds kb) ds kb
  match gaussSel (kb.length + ds.length) (bl.flatMap (·.2)) with
  | none => []
  | some sel => (selKeys bl sel).map (keyFact dat ds kb)

@[expose] def dConfigs (yt : List (List Nat × Array Bool × Nat)) (node : List Nat)
    (s : List Nat × List Nat) : List (List Nat × List Nat) :=
  let M := s.2
  yt.flatMap fun y =>
    let a := node.length * 16 * y.1.length
    if a * M.length ≤ 2 ^ 14 || a * y.2.2 ≤ 2 ^ 14 then [] else
      let M' := M.filter fun κ => y.2.1[κ]!
      if a * M'.length ≤ 2 ^ 14 then []
      else if a * M'.length ≤ 2 ^ 15 then [(node, M')]
      else if a * M'.length ≤ 2 ^ 16 then
        swalkL (fun c : List Nat => c) (fun c v => let p := 2 ^ (Nat.log2 v + 1); c.filter (p ≤ ·))
          (fun V _ => if a * V.length ≤ 2 ^ 14 then [] else [(node, V)]) 11 [0] 0 M'
      else []

@[expose] def p0Facts (dat : Data) : List Fact :=
  let yt := yTab dat (ylist ())
  let am := aMat dat
  let br := bRows dat
  let cfgs := swalkL (·.1) (dUpd am br) (dConfigs yt) 17 [0] 0 (singList dat, List.range 1024)
  (cfgs.flatMap fun c => supportFacts dat c.1 c.2).eraseDups

end MonsterB.P0Rank
