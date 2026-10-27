module

public import Certificates.Data.CFSGNative.J4Tree.Aff
public import Certificates.Data.CFSGNative.J4Tree.Index
public import Certificates.Data.CFSGNative.J4Tree.Inv
public import Std.Data.HashSet
public import Std.Data.HashMap

public section

namespace CFSG.J4Tree.Native.Node

open CFSG.J4Tree.Native

set_option compiler.extract_closed false

@[expose] def bfsStep {α : Type} (gs : List α) (step : α → Code → Code) (S : Std.HashSet Code)
    (F : List Code) : Std.HashSet Code × List Code :=
  F.foldl (fun acc x => gs.foldl (fun (acc : Std.HashSet Code × List Code) g =>
    let y := step g x
    if acc.1.contains y then acc else (acc.1.insert y, y :: acc.2)) acc) (S, [])

@[expose] def bfsRun {α : Type} (gs : List α) (step : α → Code → Code) :
    Nat → Std.HashSet Code × List Code → Std.HashSet Code × List Code
  | 0, st => st
  | n + 1, st => if st.2.isEmpty then st else bfsRun gs step n (bfsStep gs step st.1 st.2)

@[expose] def bfsFrom {α : Type} (gs : List α) (step : α → Code → Code) (x₀ : Code) (n : Nat) :
    Std.HashSet Code :=
  (bfsRun gs step n ((∅ : Std.HashSet Code).insert x₀, [x₀])).1

@[expose] def closedUnder {α : Type} (gs : List α) (step : α → Code → Code)
    (S : Std.HashSet Code) : Bool :=
  S.toList.all fun x => gs.all fun g => S.contains (step g x)

@[expose] def rmul (g x : Code) : Code := x * g

@[expose] def conjP (p : Code × Code) (x : Code) : Code := p.1 * x * p.2

@[expose] def letterOf (ch : Char) : Int :=
  if ch = 'a' then 1 else if ch = 'b' then 2 else if ch = 'c' then 3
  else if ch = 'A' then -1 else if ch = 'B' then -2 else -3

@[expose] def wordOf (s : String) : List Int := s.toList.map letterOf

@[expose] def codeOfStr (s : String) : Code := codeOfWord (wordOf s)

@[expose] def cc (ce : Nat × Nat) : Code := codeOfCoord ce.1 ce.2

structure Kid where
  y : Nat × Nat
  tgt : Nat
  conj : String
deriving Inhabited

structure NodeData where
  id : Nat
  gens : List (Nat × Nat)
  ngens : List String
  kids : List Kid
deriving Inhabited

structure FEntry where
  f : Code
  par : Nat
  lab : Nat
  root : Nat
deriving Inhabited

@[noinline, expose] def buildForest (Al : List Code) (nc ni yc : Array Code) (fuel : Nat) :
    Array FEntry × Std.HashMap Code Nat := Id.run do
  let mut ents : Array FEntry := #[]
  let mut cos : Std.HashMap Code Nat := {}
  for j in [0:yc.size] do
    let y := yc[j]!
    if !cos.contains y then
      let i := ents.size
      ents := ents.push ⟨y, 0, 0, j + 1⟩
      for a in Al do
        cos := cos.insert (y * a) i
  let mut q := 0
  for _ in [0:fuel] do
    if q < ents.size then
      let e := ents[q]!
      for l in [0:nc.size] do
        let z := nc[l]! * e.f * ni[l]!
        if !cos.contains z then
          let i := ents.size
          ents := ents.push ⟨z, q, l, 0⟩
          for a in Al do
            cos := cos.insert (z * a) i
      q := q + 1
  return (ents, cos)

@[expose] def entryOK (S A : Std.HashSet Code) (nc ni yc : Array Code) (ents : Array FEntry)
    (i : Nat) : Bool :=
  match ents[i]? with
  | none => false
  | some e =>
    S.contains e.f && e.f * e.f == 1 &&
      if e.root != 0 then yc[e.root - 1]? == some e.f
      else decide (e.par < i) &&
        match ents[e.par]?, nc[e.lab]?, ni[e.lab]? with
        | some p, some n, some n' => A.contains (n * p.f * n' * e.f)
        | _, _, _ => false

@[expose] def forestOK (S A : Std.HashSet Code) (nc ni yc : Array Code) (ents : Array FEntry) :
    Bool :=
  (List.range ents.size).all (entryOK S A nc ni yc ents)

@[expose] def coverOK (t : Code → Bool) (Sl : List Code) (A : Std.HashSet Code)
    (ents : Array FEntry) (cos : Std.HashMap Code Nat) : Bool :=
  Sl.all fun s => A.contains s || !(s * s == 1) || !(t s) ||
    match cos[s]? with
    | some i => match ents[i]? with
      | some e => A.contains (e.f * s)
      | none => false
    | none => false

@[noinline, expose] def greedyGens (Cl : List Code) : List Code := Id.run do
  let mut gens : Array Code := #[]
  let mut cur : Std.HashSet Code := (∅ : Std.HashSet Code).insert 1
  for x in Cl do
    if !cur.contains x then
      gens := gens.push x
      cur := (bfsRun gens.toList rmul (Cl.length + 1) (cur, cur.toList)).1
  return gens.toList

@[noinline, expose] def prunedWith (S : Std.HashSet Code) (y : Code) (Cl cg : List Code) : Bool :=
  let Cc := bfsFrom cg rmul 1 (Cl.length + 1)
  let B0 := Cl.filter fun z => z * z == 1 && cg.all fun g => z * g == g * z
  cg.all (fun g => S.contains g && g * y == y * g) && Cc.contains 1 && closedUnder cg rmul Cc &&
    Cc.size == Cl.length && (decide (1024 < B0.length) || decide (64 < (B0.filter Code.inE).length))

@[noinline, expose] def prunedOK (S : Std.HashSet Code) (Sl : List Code) (y : Code) : Bool :=
  let Cl := Sl.filter fun s => s * y == y * s
  prunedWith S y Cl (greedyGens Cl)

@[noinline, expose] def mergeWith (bc : List Code) (gp : List (Code × Code)) (ordK : Nat) (y : Code)
    (tgt : Nat) (h : Code) (At O : Std.HashSet Code) : Bool :=
  let hi := h.inv
  h * hi == 1 && hi.wf && !(treeTopIds.contains tgt) && decide (1 ≤ tgt) && decide (tgt ≤ treeN) &&
    (treeBasis tgt).all (fun ce => decide (ce.2 < 1024)) && At.contains 1 &&
    closedUnder ((treeBasis tgt).map cc) rmul At &&
    (y :: bc).all (fun b => At.contains (hi * b * h)) &&
    O.contains y && closedUnder gp conjP O && O.size * treeOrd tgt == ordK

@[noinline, expose] def mergeOK (bc : List Code) (gp : List (Code × Code)) (ordK : Nat) (y : Code)
    (kd : Kid) : Bool :=
  mergeWith bc gp ordK y kd.tgt (codeOfStr kd.conj)
    (bfsFrom ((treeBasis kd.tgt).map cc) rmul 1 4096) (bfsFrom gp conjP y (ordK + 1))

@[expose] def kidOK (S : Std.HashSet Code) (Sl : List Code) (bc : List Code)
    (gp : List (Code × Code)) (ordK : Nat) (kd : Kid) : Bool :=
  decide (kd.y.2 < 1024) && S.contains (cc kd.y) && cc kd.y * cc kd.y == 1 &&
    if kd.tgt == 0 then prunedOK S Sl (cc kd.y) else mergeOK bc gp ordK (cc kd.y) kd

@[expose] def basisOK (bc : List Code) : Bool :=
  bc.all fun b => b * b == 1 && bc.all fun b' => b * b' == b' * b

@[expose] def commOK (gc bc : List Code) : Bool := gc.all fun g => bc.all fun b => g * b == b * g

@[expose] def selfClOK (Sl : List Code) (A : Std.HashSet Code) (gc : List Code) : Bool :=
  Sl.all fun s => !(s * s == 1) || !(gc.all fun g => s * g == g * s) || A.contains s

@[expose] def n1OK (A : Std.HashSet Code) (bc : List Code) (n : Code) : Bool :=
  n * n.inv == 1 && n.inv.wf && bc.all fun b => A.contains (n * b * n.inv)

@[expose] def normOK (A : Std.HashSet Code) (bc : List Code) (ngens : List String) : Bool :=
  ngens.all fun w =>
    n1OK A bc (codeOfStr w)

@[noinline, expose] def nodeOKWith (t : Code → Bool) (nd : NodeData) (bc gc : List Code)
    (A S : Std.HashSet Code) (Sl : List Code) (nc ni yc : Array Code) (gp : List (Code × Code))
    (fo : Array FEntry × Std.HashMap Code Nat) : Bool :=
  (treeBasis nd.id).all (fun ce => decide (ce.2 < 1024)) &&
    nd.gens.all (fun ce => decide (ce.2 < 1024)) &&
    A.contains 1 && closedUnder bc rmul A && S.contains 1 && closedUnder gc rmul S &&
    S.size == treeOrd nd.id && treeOrd nd.id == 2 ^ Nat.log2 (treeOrd nd.id) && basisOK bc &&
    commOK gc bc && gp.all (fun p => p.1 * p.2 == 1 && p.2.wf) && selfClOK Sl A gc &&
    normOK A bc nd.ngens && forestOK S A nc ni yc fo.1 && coverOK t Sl A fo.1 fo.2 &&
    nd.kids.all (kidOK S Sl bc gp (treeOrd nd.id))

@[expose] def basisCodes (nd : NodeData) : List Code := (treeBasis nd.id).map cc

@[expose] def genCodes (nd : NodeData) : List Code := nd.gens.map cc

@[expose] def normCodes (nd : NodeData) : Array Code := (nd.ngens.map codeOfStr).toArray

@[expose] def kidCodes (nd : NodeData) : Array Code := (nd.kids.map fun kd => cc kd.y).toArray

@[expose] def invCodes (nd : NodeData) : Array Code := (normCodes nd).map Code.inv

@[expose] def genPairs (nd : NodeData) : List (Code × Code) := (genCodes nd).map fun g => (g, g.inv)

@[expose] def nodeA (nd : NodeData) : Std.HashSet Code := bfsFrom (basisCodes nd) rmul 1 4096

@[expose] def nodeS (nd : NodeData) : Std.HashSet Code :=
  bfsFrom (genCodes nd) rmul 1 (treeOrd nd.id + 1)

@[expose] def forestOf (nd : NodeData) (A S : Std.HashSet Code) :
    Array FEntry × Std.HashMap Code Nat :=
  buildForest A.toList (normCodes nd) (invCodes nd) (kidCodes nd) (S.size + nd.kids.length + 1)

@[noinline, expose] def nodeOKAS (t : Code → Bool) (nd : NodeData) (A S : Std.HashSet Code) :
    Bool :=
  nodeOKWith t nd (basisCodes nd) (genCodes nd) A S S.toList (normCodes nd) (invCodes nd)
    (kidCodes nd) (genPairs nd) (forestOf nd A S)

@[expose] def nodeOK (t : Code → Bool) (nd : NodeData) : Bool := nodeOKAS t nd (nodeA nd) (nodeS nd)

@[expose] def parseNat (s : String) : Nat := s.toNat?.getD 0

@[expose] def fields (s sep : String) : List String := (s.splitOn sep).filter (· ≠ "")

@[expose] def parsePair (s : String) : Nat × Nat :=
  match s.splitOn "," with
  | [a, b] => (parseNat a, parseNat b)
  | _ => (0, 0)

@[expose] def parseKid (s : String) : Kid :=
  match s.splitOn "," with
  | [a, b, t, w] => ⟨(parseNat a, parseNat b), parseNat t, w⟩
  | _ => ⟨(0, 0), 0, ""⟩

@[expose] def parseNode (s : String) : NodeData :=
  match s.splitOn "|" with
  | [i, g, n, k] => ⟨parseNat i, (fields g " ").map parsePair, fields n " ",
      (fields k " ").map parseKid⟩
  | _ => default

@[expose] def parseChunk (s : String) : List NodeData := (fields s "\n").map parseNode

end CFSG.J4Tree.Native.Node
