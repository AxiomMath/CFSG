module

public import CFSG.Sporadic.Co2Smith.GlDataF0Inputs
public import CFSG.Sporadic.Co2Smith.GlU62WeylInputs
public import CFSG.Sporadic.Co2Smith.GlU62D1Data
public import CFSG.Sporadic.Co2Smith.GlU62D1Data2

public section

namespace CFSG.Sporadic.Co2Smith.Native

open CFSG.Sporadic.SmallF2.Native CFSG.Monster.B.Co2.Native

set_option compiler.extract_closed false

@[expose] def d1Inv (w : List Nat) : List Nat :=
  w.reverse.flatMap fun k => List.replicate (d1Ord.getD k 1 - 1) k

@[expose] def d1ER (j : Nat) : Array Nat := glR (d1EWords.getD j [])

@[expose] def d1EIR (j : Nat) : Array Nat := glR (d1Inv (d1EWords.getD j []))

@[expose] def d1G (j : Nat) : Array Nat := if j < 3 then d1ER j else d1EIR (j - 3)

@[expose] def d1GI (j : Nat) : Array Nat := if j < 3 then d1EIR j else d1ER (j - 3)

@[expose] def d1Step (ent : Array (Array Nat)) (s : Nat × Nat × Nat) : Array (Array Nat) :=
  if s.1 == 0 then
    ent.push (mulRows 22 (mulRows 22 (d1G s.2.2) (ent.getD s.2.1 (idRows 22))) (d1GI s.2.2))
  else ent.push (mulRows 22 (ent.getD s.2.1 (idRows 22)) (ent.getD s.2.2 (idRows 22)))

@[expose] def d1Run (start : Array (Array Nat)) (l : List (Nat × Nat × Nat)) :
    Array (Array Nat) :=
  l.foldl d1Step start

@[expose, noinline] def d1QD : List Nat :=
  (List.range 512).filter fun e => commRows (glQRows e) glX25

@[expose] def d1FR (e : Nat) : Array Nat := glConj glD1h (glQRows e)

@[expose, noinline] def d1X0R : List (Array Nat) := (List.range 4).map (glRootRows 0)

@[expose, noinline] def d1B8R : List (Array Nat) := d1X0R ++ d1X0R.map (mulRows 22 glX25)

@[expose] def d1EltOK : Bool :=
  validM glZ && validM glX25 && validM (subId glZ) && glF0Valid glX25 && !glFixZ glX25 &&
  d1QD.length == 128 &&
  (List.range 3).all (fun j => (d1EWords.getD j []).all (glCzLet.contains ·) &&
    commRows (d1ER j) glX25 && mulRows 22 (d1ER j) (d1EIR j) == idRows 22) &&
  (List.range 5).all fun g => (d1MarkWords.getD g []).all (glC0Let.contains ·) &&
    commRows (glR (d1MarkWords.getD g [])) glZ && commRows (glR (d1MarkWords.getD g [])) glX25

@[expose] def d1Lam1OK : Bool :=
  (List.range d1QD.length).all fun i =>
    d1X0R.contains (glQRows (d1QD.getD i 0)) ||
      (d1Run #[glQRows (d1QD.getD i 0)] (d1Lam1.getD i [])).contains glZ

@[expose, noinline] def d1Tgt : List (Array Nat) :=
  [glRootRows 0 1, glRootRows 0 2, glRootRows 4 1, glRootRows 4 2, glRootRows 5 1, glRootRows 5 2]

@[expose] def d1Lam2OK : Bool :=
  (List.range d1QD.length).all fun i =>
    d1B8R.contains (d1FR (d1QD.getD i 0)) ||
      d1Tgt.all (d1Run #[d1FR (d1QD.getD i 0), glX25] (d1Lam2.getD i [])).contains

@[expose] def d1DecR (c : Nat) : Array Nat :=
  mulRows 22 (mulRows 22 (mulRows 22 (if c / 64 == 1 then glX25 else idRows 22)
    (glRootRows 0 (c / 16 % 4))) (glRootRows 4 (c / 4 % 4))) (glRootRows 5 (c % 4))

@[expose] def d1DecOK : Bool :=
  (List.range d1QD.length).all fun i => d1DecR (d1Dec.getD i 0) == d1FR (d1QD.getD i 0)

@[expose] def d1PR (p : List Nat) : Array Nat :=
  p.foldl (fun a j => mulRows 22 a (d1ER j)) (idRows 22)

@[expose] def d1PIR (p : List Nat) : Array Nat :=
  p.reverse.foldl (fun a j => mulRows 22 a (d1EIR j)) (idRows 22)

@[expose] def d1Q4 (j : Nat) : Array Nat := glRootRows (if j < 2 then 1 else 2) (j % 2 + 1)

@[expose] def d1UNode (A A' : Array Nat) : Array (Array Nat) :=
  (Array.range 4).map fun j => mulRows 22 (mulRows 22 A (d1Q4 j)) A'

@[expose, noinline] def d1U : Array (Array (Array Nat)) :=
  d1Tree.map fun p => d1UNode (d1PR p) (d1PIR p)

@[expose] def d1UR (i j : Nat) : Array Nat := (d1U.getD i #[]).getD j #[]

@[expose] def d1TreeChk (X0 : List (Array Nat)) (U : Array (Array (Array Nat))) : Bool :=
  (List.range 576).all (fun i => (List.range 4).all fun j => validM ((U.getD i #[]).getD j #[])) &&
  (List.range 576).all fun i => (List.range i).all fun k => (List.range 4).any fun j =>
    !X0.contains (mulRows 22 ((U.getD i #[]).getD j #[]) ((U.getD k #[]).getD j #[]))

@[expose] def d1TreeOK : Bool := d1Tree.size == 576 && d1X0R.all validM && d1TreeChk d1X0R d1U

@[expose] def d1OR (p : List Nat) : Array Nat :=
  mulRows 22 (mulRows 22 (glR p) glX25) (glR (d1Inv p))

@[expose, noinline] def d1ORA : Array (Array Nat) := d1Orb.map d1OR

@[expose] def d1OrbOK : Bool :=
  d1Orb.size == 1260 &&
  d1Orb.all (fun p => p.all (glCzLet.contains ·) &&
    mulRows 22 (glR p) (glR (d1Inv p)) == idRows 22) &&
  d1ORA.all validM &&
  (List.range 1260).all fun i => (List.range i).all fun k => d1ORA.getD i #[] != d1ORA.getD k #[]

@[expose] def d1Prod (l : List (Array Nat)) : Array Nat := l.foldl (mulRows 22) (idRows 22)

@[expose] def d1Phi (s q : Array Nat) : Array Nat :=
  d1Prod [q, s, q, q, q, s, glAl, s, q, s, q, q, q, glAl, glAl]

@[expose] def d1InX (r : Nat) (R : Array Nat) : Bool :=
  (List.range 4).any fun t => R == glRootRows r t

@[expose] def d1PhiOK : Bool :=
  d1QD.all (fun e => d1InX 1 (d1Phi glX34 (glQRows e)) && d1InX 2 (d1Phi glX43 (glQRows e)) &&
    d1InX 4 (d1Phi glX34 (d1FR e)) && d1InX 5 (d1Phi glX43 (d1FR e))) &&
  [1, 2, 3].all fun t => d1QD.any (fun e => d1Phi glX34 (glQRows e) == glRootRows 1 t) &&
    d1QD.any (fun e => d1Phi glX43 (glQRows e) == glRootRows 2 t) &&
    d1QD.any (fun e => d1Phi glX34 (d1FR e) == glRootRows 4 t) &&
    d1QD.any (fun e => d1Phi glX43 (d1FR e) == glRootRows 5 t)

@[expose] def d1RootOK : Bool :=
  [0, 1, 2, 4, 5].all (fun r => (List.range 4).all fun s => validM (glRootRows r s) &&
    (List.range 4).all fun t => s == t || glRootRows r s != glRootRows r t) &&
  (List.range 18).all fun r => [1, 2, 3].all fun t =>
    glInChart r 0 || (!commRows (glRootRows r t) glZ && validM (glRootRows r t))

@[expose] def d1BRoot (g : Nat) : Nat :=
  if g < 8 then 0 else if g < 10 then 1 else if g < 12 then 2 else if g < 14 then 4 else 5

@[expose] def d1BPar (g : Nat) : Nat := if g % 2 == 0 then 1 else 2

@[expose] def d1BG (g : Nat) : Array Nat :=
  if g < 5 then glR (d1MarkWords.getD g []) else if g == 5 then glAl
  else glRootRows (d1BRoot g) (d1BPar g)

@[expose] def d1Nu (ν : List Nat) (r : Nat) : Nat :=
  if r == 1 then ν.getD 0 1 else if r == 2 then ν.getD 1 1 else if r == 4 then ν.getD 2 1
  else if r == 5 then ν.getD 3 1 else 1

@[expose] def d1BT (ν : List Nat) (g : Nat) : Array Nat :=
  if g < 6 then d1BG g else glRootRows (d1BRoot g) (f4mul (d1Nu ν (d1BRoot g)) (d1BPar g))

@[expose] def d1WR (F : Nat → Array Nat) (w : List Nat) : Array Nat :=
  w.foldl (fun a g => mulRows 22 a (F g)) (idRows 22)

@[expose] def d1BreakOK : Bool :=
  [1, 2, 3].all fun a => [1, 2, 3].all fun b => [1, 2, 3].all fun c => [1, 2, 3].all fun d =>
    (a == 1 && b == 1 && c == 1 && d == 1) || d1Break.any fun e =>
      e.1 == [a, b, c, d] && d1WR d1BG e.2.1 == d1WR d1BG e.2.2 &&
        d1WR (d1BT [a, b, c, d]) e.2.1 != d1WR (d1BT [a, b, c, d]) e.2.2 &&
        validM (d1WR (d1BT [a, b, c, d]) e.2.1) && validM (d1WR (d1BT [a, b, c, d]) e.2.2)

@[expose] def d1OK : Bool :=
  d1EltOK && d1Lam1OK && d1Lam2OK && d1DecOK && d1TreeOK && d1OrbOK && d1PhiOK && d1RootOK &&
    d1BreakOK

end CFSG.Sporadic.Co2Smith.Native
