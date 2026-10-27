module

public import Std.Data.HashMap

public section

namespace CFSG.Quasithin.St84.G24DC.Native

abbrev Row := Nat × Nat

abbrev Mat := Array Row

@[expose] def zeroRow : Row := (0, 0)

@[expose] def rowVal (r : Row) (j : Nat) : Nat :=
  (r.1.testBit j).toNat + 2 * (r.2.testBit j).toNat

@[expose] def mask14 : Nat := (1 <<< 14) - 1

@[expose] def canon (r : Row) : Row := (r.1 &&& mask14, r.2 &&& mask14)

@[expose] def xorRow (p q : Row) : Row := canon (p.1 ^^^ q.1, p.2 ^^^ q.2)

@[expose] def oneM : Mat := ((List.finRange 14).map fun i => (1 <<< i.val, 0)).toArray

@[expose] def omegaCode (b : Nat) : Nat :=
  (b >>> 1) ||| (((b &&& 1) ^^^ (b >>> 1)) <<< 1)

@[expose] def scalarMul (a b : Nat) : Nat :=
  if a = 0 then 0
  else if a = 1 then b
  else if a = 2 then omegaCode b
  else omegaCode b ^^^ b

@[expose] def scale (a u v : Nat) : Row :=
  if a = 0 then zeroRow
  else if a = 1 then canon (u, v)
  else if a = 2 then canon (v, u ^^^ v)
  else canon (u ^^^ v, u)

@[expose] def mulRow (a : Row) (B : Mat) : Row :=
  (List.range 14).foldl (fun (p : Row) j =>
    xorRow p (scale (rowVal a j) (B.getD j zeroRow).1 (B.getD j zeroRow).2)) zeroRow

@[expose] def mulN (A B : Mat) : Mat :=
  ((List.finRange 14).map fun i => mulRow (A.getD i.val zeroRow) B).toArray

@[expose] def matEq (A B : Mat) : Bool := A == B

@[expose] def evalP (im : Array Mat) (w : List Nat) : Mat :=
  w.foldl (fun acc l => mulN acc (im.getD l oneM)) oneM

@[expose] def evalF (im : Array Mat) (w : List (Fin 4)) : Mat :=
  w.foldl (fun acc l => mulN acc (im.getD l.val oneM)) oneM

@[expose] def evalS (im : Array Mat) (w : List (Fin 4 × Bool)) : Mat :=
  w.foldl (fun acc l =>
    let x := im.getD l.1.val oneM
    mulN acc (if l.2 then x else mulN x x)) oneM

@[expose] def gBN (_ : Unit := ()) : Array Mat :=
  #[#[⟨1, 1⟩, ⟨0, 2⟩, ⟨0, 4⟩, ⟨0, 8⟩, ⟨16, 0⟩, ⟨0, 32⟩, ⟨64, 0⟩, ⟨128, 0⟩, ⟨256, 256⟩, ⟨512, 0⟩, ⟨1024, 1024⟩, ⟨2048, 2048⟩, ⟨4096, 4096⟩, ⟨0, 8192⟩],
 #[⟨1, 0⟩, ⟨2, 0⟩, ⟨0, 4⟩, ⟨8, 8⟩, ⟨16, 16⟩, ⟨32, 0⟩, ⟨64, 0⟩, ⟨128, 0⟩, ⟨256, 0⟩, ⟨0, 512⟩, ⟨0, 1024⟩, ⟨2048, 2048⟩, ⟨4096, 0⟩, ⟨8192, 0⟩],
 #[⟨1, 0⟩, ⟨46, 0⟩, ⟨36, 0⟩, ⟨40, 0⟩, ⟨592, 0⟩, ⟨32, 0⟩, ⟨64, 0⟩, ⟨640, 0⟩, ⟨7424, 0⟩, ⟨512, 0⟩, ⟨5120, 0⟩, ⟨6144, 0⟩, ⟨4096, 0⟩, ⟨8192, 0⟩],
 #[⟨3, 0⟩, ⟨2, 0⟩, ⟨4, 0⟩, ⟨24, 0⟩, ⟨16, 0⟩, ⟨416, 0⟩, ⟨320, 0⟩, ⟨128, 0⟩, ⟨256, 0⟩, ⟨1536, 0⟩, ⟨1024, 0⟩, ⟨2048, 0⟩, ⟨12288, 0⟩, ⟨8192, 0⟩]]

@[expose] def relsB : List (List (Fin 4 × Bool)) :=
  [[(2, true), (2, true)],
   [(3, true), (3, true)],
   [(0, true), (0, true), (0, true)],
   [(1, true), (1, true), (1, true)],
   [(3, true), (1, false), (3, true), (1, true)],
   [(0, true), (2, true), (0, false), (2, true)],
   [(0, true), (1, false), (0, false), (1, true)],
   [(0, false), (3, true), (0, false), (3, true), (0, false), (3, true)],
   [(2, true), (1, false), (2, true), (1, false), (2, true), (1, false)],
   [(3, true), (2, true), (3, true), (2, true), (0, false), (3, true), (2, true), (3, true), (2, true), (0, false), (3, true), (2, true), (3, true), (2, true), (0, false)],
   [(3, true), (2, true), (3, true), (2, true), (3, true), (1, true), (2, true), (3, true), (1, true), (2, true), (3, true), (2, true), (3, true), (2, true), (1, true), (2, true)]]

@[expose] def xCWord : List (Fin 4 × Bool) :=
  [(2, true), (3, true), (2, true), (0, true), (0, true), (3, true), (0, false), (0, false), (2, true), (3, true), (2, true), (0, true), (0, true), (3, true), (0, false), (0, false)]

@[expose] def wWords : List (List (List (Fin 4))) :=
  [[[0], [1], [2], [3]],
   [[0, 0], [1, 1], [2], [3]],
   [[0, 0], [1], [2], [2, 3, 2, 3, 2, 3, 2]],
   [[0], [1, 1], [2], [2, 3, 2, 3, 2, 3, 2]],
   [[0], [1], [2], [3]],
   [[0], [1], [2], [0, 2, 3, 2, 3, 2, 3, 0, 2, 3, 0]],
   [[0], [1], [2], [0, 3, 0, 2, 3, 2, 3, 2, 3, 0, 2]],
   [[0], [1], [2], [2, 3, 2, 3, 2, 3, 2]],
   [[0, 0], [1, 1], [2], [3]],
   [[0, 0], [1, 1], [2], [0, 3, 0, 2, 3, 2, 3, 2, 3, 0, 2]],
   [[0, 0], [1, 1], [2], [0, 2, 3, 2, 3, 2, 3, 0, 2, 3, 0]],
   [[0, 0], [1, 1], [2], [2, 3, 2, 3, 2, 3, 2]]]

@[expose] def wImgN (_ : Unit := ()) : Array (Array Mat) :=
  let g := gBN ()
  (wWords.map fun row => (row.map (evalF g)).toArray).toArray


structure Tab where
  elts : Array Mat
  pars : Array (Nat × Nat)
  muls : Array (Array Nat)
  look : Std.HashMap Mat Nat

structure BState where
  T : Array Mat
  pars : Array (Nat × Nat)
  muls : Array (Array Nat)
  look : Std.HashMap Mat Nat

@[expose] def addGens (g : Array Mat) (st : BState) (i : Nat) : BState × Array Nat :=
  (List.range 4).foldl (fun (p : BState × Array Nat) k =>
    let st := p.1
    let idx := p.2
    let y := mulN (st.T.getD i oneM) (g.getD k oneM)
    match st.look.get? y with
    | some j => (st, idx.push j)
    | none =>
      let j := st.T.size
      let st' : BState :=
        { T := st.T.push y, pars := st.pars.push (i, k), muls := st.muls,
          look := st.look.insert y j }
      (st', idx.push j))
    (st, #[])

@[expose] def expand (g : Array Mat) (st : BState) (start stop : Nat) : BState :=
  (List.range (stop - start)).foldl (fun (st : BState) d =>
    let i := start + d
    let (st, idx) := addGens g st i
    { st with muls := st.muls.push idx }) st

@[expose] def bfsLoop (g : Array Mat) (fuel : Nat) (st : BState) (start stop : Nat) : BState :=
  match fuel with
  | 0 => st
  | fuel + 1 =>
    if start < stop then
      let st := expand g st start stop
      bfsLoop g fuel st stop st.T.size
    else st

@[expose] def tab (g : Array Mat) : Tab :=
  let st : BState :=
    { T := #[oneM], pars := #[(0, 0)], muls := #[],
      look := (∅ : Std.HashMap Mat Nat).insert oneM 0 }
  let st := bfsLoop g 10000 st 0 1
  ⟨st.T, st.pars, st.muls, st.look⟩

@[expose] def wordOf (pars : Array (Nat × Nat)) (i : Nat) : List Nat :=
  let rec go (fuel : Nat) (j : Nat) (acc : List Nat) : List Nat :=
    match fuel with
    | 0 => acc
    | fuel + 1 =>
      if j = 0 then acc
      else
        let p := pars.getD j (0, 0)
        go fuel p.1 (p.2 :: acc)
  go (i + 1) i []

@[expose] def parOK (T : Tab) (g : Array Mat) : Bool :=
  (List.range T.elts.size).all fun i =>
    if i = 0 then matEq (T.elts.getD 0 oneM) oneM
    else
      let p := T.pars.getD i (0, 0)
      decide (p.1 < i) && decide (p.2 < 4) &&
        matEq (T.elts.getD i oneM) (mulN (T.elts.getD p.1 oneM) (g.getD p.2 oneM))

@[expose] def closedOK (T : Tab) (g : Array Mat) : Bool :=
  (List.range T.elts.size).all fun i =>
    (List.range 4).all fun k =>
      let j := (T.muls.getD i #[]).getD k 0
      decide ((T.muls.getD i #[]).size = 4) && decide (j < T.elts.size) &&
        matEq (T.elts.getD j oneM) (mulN (T.elts.getD i oneM) (g.getD k oneM))

@[expose] def tableOK (T : Tab) (g : Array Mat) : Bool :=
  matEq (T.elts.getD 0 oneM) oneM && decide (T.elts.size = 36864) &&
    decide (T.muls.size = T.elts.size) && parOK T g && closedOK T g

@[expose] def invs (T : Tab) : Array Mat :=
  T.elts.filter fun x => matEq (mulN x x) oneM && !matEq x oneM

@[expose] def hElem (g : Array Mat) (s t : Nat) : Mat :=
  let k0 := g.getD 0 oneM
  let k1 := g.getD 1 oneM
  let a := if s = 0 then oneM else if s = 1 then k0 else mulN k0 k0
  let b := if t = 0 then oneM else if t = 1 then k1 else mulN k1 k1
  mulN a b

@[expose] def hCells (g : Array Mat) : Array Mat :=
  ((List.range 3).flatMap fun s => (List.range 3).map fun t => hElem g s t).toArray

@[expose] def hOK (g : Array Mat) : Bool :=
  let k0 := g.getD 0 oneM
  let k1 := g.getD 1 oneM
  let H := hCells g
  matEq (mulN (mulN k0 k0) k0) oneM && matEq (mulN (mulN k1 k1) k1) oneM &&
    matEq (mulN k0 k1) (mulN k1 k0) &&
    (List.range 9).all (fun a => (List.range 9).all fun b =>
      if a = b then true else !matEq (H.getD a oneM) (H.getD b oneM))

@[expose] def hPairs (g : Array Mat) : Array (Mat × Mat) :=
  let H := hCells g
  ((List.range 3).flatMap fun s => (List.range 3).flatMap fun t =>
    (List.range 3).flatMap fun u => (List.range 3).flatMap fun v =>
      if (s * v) % 3 = (t * u) % 3 then []
      else [(H.getD (3 * s + t) oneM, H.getD (3 * u + v) oneM)]).toArray

structure Tuple where
  j : Nat
  s : Nat
  t : Nat
  valid : Bool
  mats : Array Mat

@[expose] def hPow (row : Array Mat) (s t : Nat) : Mat :=
  let k0 := row.getD 0 oneM
  let k1 := row.getD 1 oneM
  let a := if s = 0 then oneM else if s = 1 then k0 else mulN k0 k0
  let b := if t = 0 then oneM else if t = 1 then k1 else mulN k1 k1
  mulN a b

@[expose] def tupleOf (w : Array (Array Mat)) (j s t : Nat) : Tuple :=
  let row := w.getD (4 + j) #[]
  let hW := hPow row s t
  let hW2 := mulN hW hW
  let valid := matEq (mulN hW2 hW) oneM
  let mats := ((List.range 4).map fun k => mulN (mulN hW (row.getD k oneM)) hW2).toArray
  ⟨j, s, t, valid, mats⟩

@[expose] def tuples (w : Array (Array Mat)) : Array Tuple :=
  ((List.range 8).flatMap fun j => (List.range 3).flatMap fun s =>
    (List.range 3).map fun t => tupleOf w j s t).toArray

@[expose] def eqTuple (a b : Array Mat) : Bool :=
  decide (a.size = b.size) && (List.range a.size).all fun k => matEq (a.getD k oneM) (b.getD k oneM)

@[expose] def w1Tuple (T : Tab) (row : Array Mat) (im : Array Mat) : Option (Array Mat) :=
  let rec go (k : Nat) (acc : Array Mat) : Option (Array Mat) :=
    match k with
    | 0 => some acc
    | k + 1 =>
      let x := im.getD k oneM
      let idx := T.look.getD x 0
      if matEq (T.elts.getD idx oneM) x then
        go k (acc.set! k (evalP row (wordOf T.pars idx)))
      else none
  go 4 (Array.replicate 4 oneM)

@[expose] def decomposes (T : Tab) (tups : Array Tuple) (w : Array (Array Mat))
    (im : Array Mat) : Bool :=
  let hit : Array Mat → Bool := fun mats => tups.any fun t => t.valid && eqTuple t.mats mats
  hit im || (List.range 3).any fun d =>
    match w1Tuple T (w.getD (d + 1) #[]) im with
    | some mats => hit mats
    | none => false

structure Counts where
  candidates : Nat
  relOK : Nat
  kill : Nat
  dec : Nat
  fail : Nat

@[expose] def countCandidate (T : Tab) (tups : Array Tuple) (w : Array (Array Mat))
    (im : Array Mat) (c : Counts) : Counts :=
  let c := { c with candidates := c.candidates + 1 }
  if relsB.any (fun r => !matEq (evalS im r) oneM) then c
  else
    let c := { c with relOK := c.relOK + 1 }
    if matEq (evalS im xCWord) oneM then { c with kill := c.kill + 1 }
    else if decomposes T tups w im then { c with dec := c.dec + 1 }
    else { c with fail := c.fail + 1 }

@[expose] def counts (T : Tab) (tups : Array Tuple) (w : Array (Array Mat))
    (pairs : Array (Mat × Mat)) (inv : Array Mat) : Counts :=
  pairs.foldl (fun (c : Counts) pq =>
    let yas := inv.filter fun y => matEq (mulN pq.1 y) (mulN y pq.1)
    let ybs := inv.filter fun y => matEq (mulN pq.2 y) (mulN y pq.2)
    yas.foldl (fun (c : Counts) ya =>
      ybs.foldl (fun (c : Counts) yb =>
        countCandidate T tups w #[pq.1, pq.2, ya, yb] c) c) c)
    { candidates := 0, relOK := 0, kill := 0, dec := 0, fail := 0 }

@[expose] def relsBOK (g : Array Mat) : Bool :=
  relsB.all fun r => matEq (evalS g r) oneM

@[expose] def xCOK (g : Array Mat) : Bool :=
  !matEq (evalS g xCWord) oneM

@[expose] def invsOK (inv : Array Mat) : Bool := decide (inv.size = 495)

@[expose] def pairsOK (pairs : Array (Mat × Mat)) : Bool := decide (pairs.size = 48)

@[expose] def countsOK (c : Counts) : Bool :=
  decide (c.candidates = 2160) && decide (c.relOK = 2016) &&
    decide (c.kill = 1872) && decide (c.dec = 144)

@[expose] def mainOK (c : Counts) : Bool := decide (c.fail = 0)

@[expose] def dcCheck (_ : Unit := ()) : Bool :=
  let g := gBN ()
  let T := tab g
  let w := wImgN ()
  let inv := invs T
  let pairs := hPairs g
  let tups := tuples w
  let c := counts T tups w pairs inv
  tableOK T g && relsBOK g && hOK g && invsOK inv && pairsOK pairs && xCOK g &&
    countsOK c && mainOK c

end CFSG.Quasithin.St84.G24DC.Native
