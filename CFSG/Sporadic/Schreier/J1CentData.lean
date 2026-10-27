module

public import CFSG.Sporadic.Schreier.J1ClosureSpec
public import CFSG.Sporadic.Schreier.J1CountCheckInputs
public import Certificates.Data.CFSGNative.SporadicSchreier.MathieuOddCore

public section

namespace CFSG.Sporadic.Schreier

open CFSG.Sporadic.Th.Native CFSG.Sporadic.Schreier.Native

@[expose] def classLabels (n : ℕ) (E : Array Table) : Array ℕ × Array ℕ × Array ℕ := Id.run do
  let Einv := E.map (invT n)
  let mut reps : Array ℕ := #[]
  let mut lab : Array ℕ := Array.replicate E.size 0
  let mut cj : Array ℕ := Array.replicate E.size 0
  let mut done : Array Bool := Array.replicate E.size false
  for i in [0:E.size] do
    if !done[i]! then
      let r := reps.size
      reps := reps.push i
      for c in [0:E.size] do
        let y := conjT n E[c]! Einv[c]! E[i]!
        for k in [0:E.size] do
          if !done[k]! && tblEq n E[k]! y then
            done := done.set! k true
            lab := lab.set! k r
            cj := cj.set! k c
  return (reps, lab, cj)

@[expose] def classLabelsOK (n : ℕ) (E : Array Table) (reps lab cj : Array ℕ) : Bool :=
  decide (0 < reps.size) && reps[0]! == 0 && reps.all (fun i => decide (i < E.size)) &&
    allIn 0 E.size fun k => decide (lab[k]! < reps.size) && decide (cj[k]! < E.size) &&
      invOK n E[cj[k]!]! (invT n E[cj[k]!]!) &&
      tblEq n E[k]! (conjT n E[cj[k]!]! (invT n E[cj[k]!]!) E[reps[lab[k]!]!]!)

@[expose] def j1LetterTbl (l : ℤ) : Table :=
  if l = 1 then j1ATbl else if l = -1 then j1AInvTbl else if l = 2 then j1BTbl else j1BInvTbl

@[expose] def j1CWords : List (List ℤ) :=
  [[1],
    [-2, -2, -1, -2, -1, -2, -2, -1, -2, -1, -2, -2, -1, -2, -2, -1, -2, -1, -2, -1, 2, 1, 2,
      2, 1, 2, 2, 1, 2, 1, 2, 1, 2, 2, 1, 2, 1, 2, 2, 1, 2],
    [-2, -1, -2, -1, -2, -2, -1, -2, -1, -2, -1, -2, -2, -1, -2, -2, -1, -2, -1, -2, -1, 2, 1,
      2, 1, 2, 2, 1, 2, 1, 2, 1, 2, 2, 1, 2, 1, 2, 2, 1, 2, 1, 2],
    [-2, -1, -2, -2, -1, -2, -1, -2, -1, -2, -2, -1, -2, -1, -2, -2, -1, -2, -1, -2, -2, -1, 2,
      1, 2, 2, 1, 2, 1, 2, 2, 1, 2, 1, 2, 2, 1, 2, 2, 1, 2, 1, 2, 2]]

@[expose] def j1DWords : List (List ℤ) :=
  [[2, 3, -2, -3], [2, 2, 3, -2, -3, -2], [4, 2, 3, -2, -3, -4]]

@[expose] def j1CTbl (i : ℕ) : Table := wordT 3080 j1LetterTbl (j1CWords.getD i [])

@[expose] def j1CInvTbl (i : ℕ) : Table := invT 3080 (j1CTbl i)

@[expose] def j1CLetterTbl (l : ℤ) : Table :=
  if 0 < l then j1CTbl (l.toNat - 1) else j1CInvTbl ((-l).toNat - 1)

@[expose] def j1DTbl (j : ℕ) : Table := wordT 3080 j1CLetterTbl (j1DWords.getD j [])

@[expose] def j1DGens : Array Table := #[j1DTbl 0, j1DTbl 1, j1DTbl 2]

@[expose] def j1DGensInv : Array Table := #[invT 3080 (j1DTbl 0), invT 3080 (j1DTbl 1),
  invT 3080 (j1DTbl 2)]

@[expose] def j1DClo : Array Table × Array ℕ × Array ℕ := mulClosure 3080 j1DGens 200

opaque j1DEltsSeal : {x : Array Table // x = j1DClo.1} := ⟨j1DClo.1, rfl⟩

@[expose] def j1DElts : Array Table := j1DEltsSeal.1

theorem j1DElts_def : j1DElts = j1DClo.1 := j1DEltsSeal.2

attribute [irreducible] j1DElts

@[expose] def j1DClasses : Array ℕ × Array ℕ × Array ℕ := classLabels 3080 j1DElts

@[expose] def j1CentTables : List Table :=
  filterProducts 3080 (commT 3080 j1ATbl) j1Tables (idT 3080) []

end CFSG.Sporadic.Schreier
