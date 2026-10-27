module

public import Certificates.Data.CFSGNative.Co2Smith.Check
public import CFSG.Sporadic.Co2Smith.GlDataWords
public import CFSG.Sporadic.Co2Smith.GlDataWit
public import CFSG.Sporadic.Co2Rank3.CheckInputs
public import CFSG.Sporadic.Co2Smith.CheckInputs

public section

namespace CFSG.Sporadic.Co2Smith.Native

open CFSG.Sporadic.SmallF2.Native CFSG.Monster.B.Co2.Native CFSG.Certificates.Native
  CFSG.Sporadic.Co2Cert

set_option compiler.extract_closed false

@[expose] def glRows : Array (Array Nat) :=
  glLetterWords.map (mRows CFSG.Sporadic.Co2Smith.seedRowsArr)

@[expose] def glR (w : List Nat) : Array Nat := wRows glRows w

@[expose] def glC0Let : List Nat := [0, 11, 12, 13]

@[expose] def glCzLet : List Nat := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 14, 15, 16, 17, 18,
  19, 20, 21]

@[expose] def glAl : Array Nat := glR [9]

@[expose] def glGa : Array Nat := glR [10]

@[expose] def glZ : Array Nat := glR [0]

@[expose] def glConj (b a : Array Nat) : Array Nat := mulRows 22 (mulRows 22 b a) b

@[expose] def glX61 : Array Nat := glR glX61Word

@[expose] def glW1 : Array Nat := glConj glZ glX61

@[expose] def glD0h : Array Nat := glR glD0hWord

@[expose] def glD1h : Array Nat := glR glD1hWord

@[expose] def glW2 : Array Nat := glConj glD1h glW1

@[expose] def glW3 : Array Nat := glConj glD0h glW2

@[expose] def glX52 : Array Nat := glConj glD1h glX61

@[expose] def glX43 : Array Nat := glConj glD0h glX52

@[expose] def glX25 : Array Nat := glConj glD1h glZ

@[expose] def glX34 : Array Nat := glConj glD0h glX25

@[expose] def glB3 : Array Nat := mulRows 22 glX34 glX43

@[expose] def glW0 : Array Nat := mulRows 22 (mulRows 22 glW1 glW2) glW3

@[expose] def glU : Array Nat := glR glUWord

@[expose] def glV : Array Nat := mulRows 22 (mulRows 22 glU glW0) glU

@[expose] def glV1 : Array Nat := mulRows 22 (mulRows 22 (mulRows 22 glB3 glB3) glV) glB3

@[expose] def glPermArr (R : Array Nat) : Array Nat :=
  Array.ofFn (n := 2300) fun i => (co2PosTable[colAct R co2PackedVecs[i.val]!]!).toNat

@[expose] def glPermOK (R p : Array Nat) : Bool :=
  p.size == 2300 && allLt 2300 fun i =>
    decide (p[i]! < 2300) && co2PackedVecs[p[i]!]! == colAct R co2PackedVecs[i]!

@[expose] def glMaps (R : Array Nat) (x y : Nat) : Bool :=
  colAct R co2PackedVecs[x]! == co2PackedVecs[y]!

@[expose] def glCArr : Array Nat := wordA 2300 co2StrongArrs (rawInvs 2300 co2StrongArrs) glCWord

@[expose] def glCInv : Array Nat := invCand 2300 glCArr

@[expose] def glPsiArr (R : Array Nat) : Array Nat :=
  compA 2300 (compA 2300 glCArr (glPermArr R)) glCInv

@[expose] def glLetOK : Bool :=
  glRows.size == 22 && glCzLet.all (fun k => commRows glRows[k]! glZ) &&
    glC0Let.all (fun k => commRows glRows[k]! glAl && commRows glRows[k]! glGa) &&
    commRows glU glZ

@[expose] def glOrdOK : Bool :=
  powRows 22 glAl 3 == idRows 22 && mulRows 22 glGa glGa == idRows 22 &&
    glConj glGa glAl == mulRows 22 glAl glAl && glMaps glAl 0 1753 && glMaps glGa 0 2294

@[expose] def glPtOK : Bool :=
  (List.range 11).all (fun k => glMaps glRows[k]! 80 80) && mulRows 22 glU glU == idRows 22 &&
    glMaps glU 80 1172 && glMaps glV 80 1348 && glMaps glV1 80 582 &&
    mulRows 22 glV1 glV1 == idRows 22

@[expose] def glCOK : Bool :=
  lettersOK 11 glCWord && isInvA 2300 glCArr glCInv && glCArr[80]! == 0 &&
    glCArr[1172]! == 3 && glCArr[582]! == 1

@[expose] def glArcOK : Bool :=
  glPermOK glAl (glPermArr glAl) && glPermOK glGa (glPermArr glGa) &&
    glPermOK glZ (glPermArr glZ)

@[expose] def glGenOK : Bool :=
  glNWords.all (fun w => glMaps (glR w) 80 80 && glMaps (glR w) 1172 1172) &&
    glMWords.all (fun w => glMaps (glR w) 80 80 && glMaps (glR w) 582 582)

@[expose] def glElemOK : Bool :=
  glLetOK && glOrdOK && glPtOK && glCOK && glArcOK && glGenOK

@[expose] def glFix (arcs : List (Array Nat)) (v : Nat) : Nat :=
  arcs.foldr (fun p acc => 2 * acc + if p[v]! == v then 1 else 0) 0

@[expose] def glInit (arcs : List (Array Nat)) (b : List Nat) (s : Nat) : Array Nat :=
  Array.ofFn (n := 2300) fun v => (individualize 2300 b s)[v.val]! * 16 + glFix arcs v.val

@[expose] def glArcNbr (p : Array Nat) : Array (List Nat) := p.map fun x => [x]

@[expose] def glRound (nbr : Array (List Nat)) (arcs : List (Array Nat)) (col : Array Nat) :
    Array Nat :=
  arcs.foldl (fun col p => refineStep 2300 (glArcNbr p) col) (refineStep 2300 nbr col)

@[expose] def glRefine (nbr : Array (List Nat)) (arcs : List (Array Nat)) (col : Array Nat) :
    Nat → Array Nat
  | 0 => col
  | k + 1 => glRound nbr arcs (glRefine nbr arcs col k)

@[expose] def glColour (nbr : Array (List Nat)) (arcs : List (Array Nat)) (b : List Nat)
    (s k : Nat) : Array Nat :=
  glRefine nbr arcs (glInit arcs b s) k

@[expose] def glBase : List Nat := [80, 1, 0]

@[expose] def glClassIn (col : Array Nat) (x : Nat) (pts : List Nat) : Bool :=
  allLt 2300 fun w => !(col[w]! == col[x]!) || pts.contains w

@[expose] def glRefineOK (arcs : List (Array Nat)) (b p₀ p₁ p₂ : List Nat)
    (extra : List (Nat × List Nat)) : Bool :=
  let nbr := CFSG.Sporadic.Co2Rank3.co2Nbr
  let c0 := glColour nbr arcs b 0 3
  let c1 := glColour nbr arcs b 1 3
  let c2 := glColour nbr arcs b 2 3
  let c3 := glColour nbr arcs b 3 3
  glClassIn c0 b[0]! p₀ && glClassIn c1 b[1]! p₁ && glClassIn c2 b[2]! p₂ &&
    extra.all (fun e => glClassIn c1 e.1 e.2) && decide c3.toList.Nodup && c3.size == 2300

@[expose] def glWit0Pts (t : Nat) : List Nat := (glWit0.filter fun e => e.2.1 == t).map (·.1)

@[expose] def glRefineC0OK : Bool :=
  glRefineOK [glPermArr glAl, glPermArr glGa] glBase (glWit0.map (·.1)) (glWit1.map (·.1))
    (glWit2.map (·.1)) [(1172, glWit0Pts 1), (1348, glWit0Pts 2)]

@[expose] def glRefineCzOK : Bool :=
  glRefineOK [glPermArr glAl, glPermArr glGa, glPermArr glZ] glBase (glWitZ0.map (·.1))
    (glWitZ1.map (·.1)) (glWitZ2.map (·.1)) []

@[expose] def glForm (t : Nat) : Array Nat :=
  if t == 1 then glU else if t == 2 then glV else idRows 22

@[expose] def glWitEntryOK (L : List Nat) (cz : Bool) (b : List Nat) (s x t : Nat)
    (w : List Nat) : Bool :=
  let R := glR w
  decide (x < 2300) && w.all (fun k => L.contains k) && (!cz || commRows R glZ) &&
    (List.range s).all (fun j => glMaps R b[j]! b[j]!) &&
    glMaps (mulRows 22 R (glForm t)) b[s]! x

@[expose] def glWitC0OK : Bool :=
  glWit0.all (fun e => glWitEntryOK glC0Let false glBase 0 e.1 e.2.1 e.2.2 &&
      glMaps (glR e.2.2) 80 80 && decide (e.2.1 < 3)) &&
    glWit1.all (fun e => glWitEntryOK glC0Let false glBase 1 e.1 0 e.2) &&
    glWit2.all (fun e => glWitEntryOK glC0Let false glBase 2 e.1 0 e.2)

@[expose] def glWitCzOK : Bool :=
  glWitZ0.all (fun e => glWitEntryOK glC0Let true glBase 0 e.1 0 e.2) &&
    glWitZ1.all (fun e => glWitEntryOK glC0Let true glBase 1 e.1 0 e.2) &&
    glWitZ2.all (fun e => glWitEntryOK glC0Let true glBase 2 e.1 0 e.2)

@[expose] def glWitPtsOK : Bool :=
  decide (glWit0.map (·.1)).Nodup && decide (glWit1.map (·.1)).Nodup &&
    decide (glWit2.map (·.1)).Nodup && decide (glWitZ0.map (·.1)).Nodup &&
    decide (glWitZ1.map (·.1)).Nodup && decide (glWitZ2.map (·.1)).Nodup &&
    glWit0.length == 40 && glWit1.length == 108 && glWit2.length == 12 &&
    glWitZ0.length == 10 && glWitZ1.length == 36 && glWitZ2.length == 4 &&
    (glWit0Pts 1).length == 27 && (glWit0Pts 2).length == 12

@[expose] def glWitOK : Bool := glWitC0OK && glWitCzOK && glWitPtsOK

@[expose] def glExtend (O : Array (Array Nat)) (W : Array (List Int)) : Array (Array Nat) :=
  (List.range (W.size - O.size)).foldl
    (fun S j => S.push (wordA 2300 S (rawInvs 2300 S) W[O.size + j]!)) O

@[expose] def glOrig (ws : List (List Nat)) : Array (Array Nat) :=
  (ws.map fun w => glPsiArr (glR w)).toArray

@[expose] def glChainOK (ws : List (List Nat)) (base : List Nat) (W : Array (List Int))
    (ord : Nat) : Bool :=
  let S := glExtend (glOrig ws) W
  ws.all (fun w => glPermOK (glR w) (glPermArr (glR w))) && decide (ws.length ≤ S.size) &&
    allLt ws.length (fun i => eqA 2300 S[i]! (glPsiArr (glR ws[i]!))) &&
    rawChainOK 2300 (S.extract 0 ws.length) S base.toArray W 1 &&
    (rawOrbitSizes 2300 S base.toArray).prod == ord

@[expose] def glChainNOK : Bool := glChainOK glNWords glChainNBase glChainNW 20643840

@[expose] def glChainMOK : Bool := glChainOK glMWords glChainMBase glChainMW 13063680

end CFSG.Sporadic.Co2Smith.Native
