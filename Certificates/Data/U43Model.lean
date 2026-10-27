module

public import Certificates.Data.CFSGNative.KGroups.Perm
public import Certificates.Data.U43ModelWords
public import Std.Data.HashSet

public section

namespace CFSG.KGroups.U43

open CFSG.Monster.B.Co2.Native CFSG.KGroups.Native

@[expose] def lettArr (G Gi : Array (Array Nat)) (l : Nat × Bool) : Array Nat :=
  if l.2 then G[l.1]! else Gi[l.1]!

@[expose] def evalArr (n : Nat) (G Gi : Array (Array Nat)) : Word → Array Nat
  | [] => idA n
  | l :: w => compA n (lettArr G Gi l) (evalArr n G Gi w)

@[expose] def invArrs (n : Nat) (G : Array (Array Nat)) : Array (Array Nat) :=
  G.map (invCand n)

@[expose] def invsOK (n : Nat) (G Gi : Array (Array Nat)) : Bool :=
  G.size == Gi.size && allLt G.size fun i => isInvA n G[i]! Gi[i]!

@[expose] def genAB (tA tB : Array Nat) : Array (Array Nat) := #[tA, tB]

structure Rec where
  L : Array (Array Nat)
  par : Array Nat
  lab : Array Nat

@[expose] def keyOf (t : Array Nat) : Nat × Nat × Nat := (t[0]!, t[1]!, t[9]!)

@[expose] def bfsRec (step : Nat → Array Nat → Array Nat) (k cap : Nat) (x0 : Array Nat) : Rec :=
  Id.run do
    let mut seen : Std.HashSet (Nat × Nat × Nat) := {}
    seen := seen.insert (keyOf x0)
    let mut L : Array (Array Nat) := #[x0]
    let mut par : Array Nat := #[0]
    let mut lab : Array Nat := #[0]
    for h in [0:cap] do
      if h < L.size then
        let x := L[h]!
        for j in [0:k] do
          let y := step j x
          if !seen.contains (keyOf y) then
            seen := seen.insert (keyOf y)
            L := L.push y
            par := par.push h
            lab := lab.push j
    return ⟨L, par, lab⟩

@[expose] def derivOK (n : Nat) (step : Nat → Array Nat → Array Nat) (k : Nat) (x0 : Array Nat)
    (r : Rec) (N : Nat) : Bool :=
  r.L.size == N && r.par.size == N && r.lab.size == N && eqA n r.L[0]! x0 &&
    allLt N fun i => i == 0 ||
      (r.par[i]! < i && r.lab[i]! < k && eqA n r.L[i]! (step r.lab[i]! r.L[r.par[i]!]!))

@[expose] def keysNodup (L : Array (Array Nat)) : Bool := decide ((L.toList.map keyOf).Nodup)

@[expose] def closedOK (n : Nat) (S Si L : Array (Array Nat)) : Bool :=
  allLt S.size fun j => allLt L.size fun i =>
    L.any (fun t => eqA n t (compA n S[j]! L[i]!)) &&
      L.any (fun t => eqA n t (compA n Si[j]! L[i]!))

@[expose] def leftStep (n : Nat) (E : Array (Array Nat)) (k : Nat) (t : Array Nat) : Array Nat :=
  compA n E[k]! t

@[expose] def conjStep (n : Nat) (G Gi : Array (Array Nat)) (k : Nat) (t : Array Nat) :
    Array Nat :=
  compA n G[k]! (compA n t Gi[k]!)

@[expose] def orbRec (n : Nat) (tA tB : Array Nat) : Rec :=
  bfsRec (conjStep n (genAB tA tB) (invArrs n (genAB tA tB))) 2 3000 tA

@[expose] def orbCheck (n : Nat) (tA tB : Array Nat) : Bool :=
  invsOK n (genAB tA tB) (invArrs n (genAB tA tB)) &&
    derivOK n (conjStep n (genAB tA tB) (invArrs n (genAB tA tB))) 2 tA (orbRec n tA tB) 2835 &&
    keysNodup (orbRec n tA tB).L

@[expose] def wArr (n : Nat) (tA tB : Array Nat) (w : Word) : Array Nat :=
  evalArr n (genAB tA tB) (invArrs n (genAB tA tB)) w

@[expose] def gensWith (n : Nat) (tA tB last : Array Nat) : Array (Array Nat) :=
  #[wArr n tA tB wordA, wArr n tA tB wordS, wArr n tA tB wordU, wArr n tA tB wordV, last]

@[expose] def hGens (n : Nat) (tA tB : Array Nat) : Array (Array Nat) :=
  gensWith n tA tB (idA n)

@[expose] def h4Check (n : Nat) (tA tB : Array Nat) (rels4 : List Word) : Bool :=
  let E := hGens n tA tB
  let Ei := invArrs n E
  let r := bfsRec (leftStep n E) 4 1200 (idA n)
  invsOK n (genAB tA tB) (invArrs n (genAB tA tB)) && invsOK n E Ei &&
    (List.range 4).all (fun i => eqA n (compA n E[i]! tA) (compA n tA E[i]!)) &&
    rels4.all (fun w => eqA n (evalArr n E Ei w) (idA n)) &&
    derivOK n (leftStep n E) 4 (idA n) r 1152 && keysNodup r.L

@[expose] def sylGens (n : Nat) (tA tB : Array Nat) : Array (Array Nat) :=
  let E := hGens n tA tB
  let Ei := invArrs n E
  #[evalArr n E Ei sylWord0, evalArr n E Ei sylWord1, evalArr n E Ei sylWord2]

@[expose] def sylCheck (n : Nat) (tA tB : Array Nat) : Bool :=
  let E := hGens n tA tB
  let S := sylGens n tA tB
  let Si := invArrs n S
  let r := bfsRec (leftStep n S) 3 200 (idA n)
  let ro := orbRec n tA tB
  invsOK n (genAB tA tB) (invArrs n (genAB tA tB)) && invsOK n E (invArrs n E) &&
    invsOK n S Si && derivOK n (leftStep n S) 3 (idA n) r 128 && keysNodup r.L &&
    closedOK n S Si r.L &&
    allLt 128 fun i => !(isInvolA n r.L[i]!) || ro.L.any (fun t => eqA n r.L[i]! t)

@[expose] def phiArr (n : Nat) (tA tB : Array Nat) : Array Nat := wArr n tA tB wordPhi

@[expose] def modelCheck (n : Nat) (tA tB : Array Nat) (rels5 : List Word) : Bool :=
  let M := gensWith n tA tB (phiArr n tA tB)
  let Mi := invArrs n M
  invsOK n (genAB tA tB) (invArrs n (genAB tA tB)) && invsOK n M Mi &&
    rels5.all (fun w => eqA n (evalArr n M Mi w) (idA n)) &&
    eqA n (evalArr n M Mi [(0, false), (0, false)]) tA && eqA n (evalArr n M Mi surjB) tB

end CFSG.KGroups.U43
