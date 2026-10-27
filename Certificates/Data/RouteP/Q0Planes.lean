module

public import Certificates.Data.RouteP.Objects

public section

namespace CFSG.EvenSporadicStandard.TwoFi22.DS81.RouteP.Model.Native

open CFSG.Sporadic.Th.Native

set_option compiler.extract_closed false

@[expose, irreducible] def planesXText : String := include_str "Q0PlanesX.txt"

@[expose, irreducible] def planeGensText : String := include_str "Q0PlaneGens.txt"

@[expose, irreducible] def planeWordsText : String := include_str "Q0PlaneWords.txt"

abbrev planeCount : Nat := 891

abbrev planeGenCount : Nat := 14

@[expose] def planeXData (_ : Unit := ()) : Array (Array Nat) :=
  (numLines planesXText).map fun l => l.map UInt32.toNat

@[expose] def planeGenData (_ : Unit := ()) : Array (Array Nat) :=
  (numLines planeGensText).map fun l => l.map UInt32.toNat

@[expose] def planeTabs (_ : Unit := ()) : Array (Array Nat) := (planeGenData ()).extract 0 14

@[expose] def planeDTabs (_ : Unit := ()) : Array (Array Nat) := (planeTabs ()).extract 0 13

@[expose] def planePar (_ : Unit := ()) : Array Nat := (planeGenData ())[14]!

@[expose] def planeLab (_ : Unit := ()) : Array Nat := (planeGenData ())[15]!

@[expose] def planeSep (_ : Unit := ()) : Array Nat := (planeGenData ())[16]!

@[expose] def wordLines (text pre : String) : Array (List Int) :=
  ((text.splitOn "\n").filter fun l => l.startsWith pre).toArray.map fun l =>
    ((l.splitOn " ").drop 1).filterMap fun t => if t.isEmpty then none else t.toInt?

@[expose] def planeDWords (_ : Unit := ()) : Array (List Int) := wordLines planeWordsText "D "

@[expose] def planeUWord (_ : Unit := ()) : List Int := (wordLines planeWordsText "U ")[0]!

@[expose] def planeVWord (_ : Unit := ()) : List Int := (wordLines planeWordsText "V ")[0]!

@[expose] def planeLetterRegs : List Nat :=
  [53, 57, 31, 33, 35, 37, 39, 41, 43, 45, 47, 49, 51, 6, 7, 8]

@[expose] def planeLetters (tabs : Array Table) : Array Table :=
  (planeLetterRegs.map fun r => tabs[r]!).toArray

@[expose] def planeInvWord (w : List Int) : List Int := w.reverse.map fun l => -l

@[expose] def planeGenWord (dws : Array (List Int)) (u v : List Int) (s : Nat) : List Int :=
  if s < 2 then dws[s]! else if s < 13 then [(s : Int) + 1]
  else planeInvWord u ++ planeInvWord v ++ u ++ v

@[expose] def planeGenTab (gs gsInv : Array Table) (w : List Int) : Table :=
  wordT degree (letterTab degree gs gsInv) w

@[inline, expose] def anyIn (lo hi : Nat) (p : Nat → Bool) : Bool := !allIn lo hi fun i => !p i

@[inline, expose] def memRow (r : Array Nat) (p : Nat) : Bool := anyIn 0 24 fun j => r[j]! == p

@[expose] def interAux (X : Array (Array Nat)) (a b : Nat) : Nat → Nat
  | 0 => 0
  | m + 1 => interAux X a b m + if memRow (X[b]!) ((X[a]!)[m]!) then 1 else 0

@[expose] def planeInterCount (X : Array (Array Nat)) (a b : Nat) : Nat := interAux X a b 24

@[expose] def rowOK (r : Array Nat) : Bool :=
  r.size == 24 && allIn 0 24 (fun j => decide (r[j]! < degree)) &&
    allIn 0 23 (fun j => decide (r[j]! < r[j + 1]!))

@[expose] def rowsOK (X : Array (Array Nat)) : Bool :=
  X.size == planeCount && allIn 0 planeCount fun i => rowOK X[i]!

@[expose] def baseOK (X : Array (Array Nat)) : Bool :=
  allIn 0 24 fun j => anyIn 0 24 fun i => planeArr[i]! == X[0]![j]!

@[expose] def distinctOK (X : Array (Array Nat)) : Bool :=
  allIn 0 planeCount fun i => allIn 0 i fun j => anyIn 0 24 fun a => !memRow X[j]! X[i]![a]!

@[expose] def sepOK (X : Array (Array Nat)) (sep : Array Nat) : Bool :=
  sep.size == 21 && allIn 0 21 fun t =>
    decide (sep[t]! < planeCount) && allIn 0 24 fun i =>
      memRow X[sep[t]!]! planeArr[i]! == (decide (i < 3) || i == t + 3)

@[expose] def dwordsOK (dws : Array (List Int)) : Bool :=
  dws.size == 2 && allIn 0 2 fun s => dws[s]!.all fun l => decide (1 ≤ l.natAbs ∧ l.natAbs ≤ 13)

@[inline, expose] def fix3 (t : Table) : Bool :=
  ap t 0 == 0 && ap t 1479 == 1479 && ap t 99705 == 99705

@[expose] def fixTripleOK (G : Array Table) : Bool :=
  G.size == planeGenCount && allIn 0 planeGenCount fun s => fix3 G[s]!

@[expose] def actOK (G : Array Table) (X T : Array (Array Nat)) : Bool :=
  T.size == planeGenCount && allIn 0 planeGenCount fun s =>
    T[s]!.size == planeCount && allIn 0 planeCount fun i =>
      decide (T[s]![i]! < planeCount) && allIn 0 24 fun a =>
        memRow X[T[s]![i]!]! (ap G[s]! X[i]![a]!)

@[expose] def planeTreeOK (T : Array (Array Nat)) (par lab : Array Nat) : Bool :=
  par.size == planeCount && lab.size == planeCount &&
    allIn 1 planeCount fun k => decide (par[k]! < k) && decide (lab[k]! < planeGenCount) &&
      T[lab[k]!]![par[k]!]! == k

@[expose] def maskAct : List (Array Nat) → Nat → Nat → Nat
  | [], _, i => i
  | t :: ts, m, i => if m % 2 = 1 then t[maskAct ts (m / 2) i]! else maskAct ts (m / 2) i

@[expose] def epsTabsFrom (T : Array (Array Nat)) : Nat → Nat → List (Array Nat)
  | 0, _ => []
  | k + 1, s => T[2 + s]! :: epsTabsFrom T k (s + 1)

@[expose] def fixMasks (T : Array (Array Nat)) : List Nat :=
  let ets := epsTabsFrom T 11 0
  (List.range 2048).filter fun m => allIn 0 planeCount fun i => maskAct ets m i == i

@[expose] def fixMasksExpected : List Nat := [0, 256, 1216, 1472]

@[expose] def lettersInvOK (gs : Array Table) : Bool :=
  gs.size == 16 && allIn 0 16 fun l => invOK degree gs[l]! (invT degree gs[l]!)

@[expose] def planesOKAt (tabs : Array Table) (X T : Array (Array Nat)) (par lab sep : Array Nat)
    (dws : Array (List Int)) (u v : List Int) : Bool :=
  let gs := planeLetters tabs
  let gsInv := gs.map (invT degree)
  let G := (Array.range planeGenCount).map fun s => planeGenTab gs gsInv (planeGenWord dws u v s)
  lettersInvOK gs && rowsOK X && baseOK X && distinctOK X && sepOK X sep && dwordsOK dws &&
    fixTripleOK G && fix3 (planeGenTab gs gsInv u) && fix3 (planeGenTab gs gsInv v) &&
    actOK G X T && planeTreeOK T par lab && fixMasks T == fixMasksExpected

@[expose] def q0PlanesOK (_ : Unit := ()) : Bool :=
  planesOKAt (objRun ()).1 (planeXData ()) (planeTabs ()) (planePar ()) (planeLab ())
    (planeSep ()) (planeDWords ()) (planeUWord ()) (planeVWord ())

end CFSG.EvenSporadicStandard.TwoFi22.DS81.RouteP.Model.Native
