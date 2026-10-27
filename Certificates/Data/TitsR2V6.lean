module

public import CFSG.Quasithin.H13.L32NKGCertInputs
public import Mathlib

public section

namespace Certificates.TitsR2V6

open CFSG.Quasithin.H13.KGCert

@[expose] def u33Ac : List ℕ := [1, 6, 2, 8, 32, 48]

@[expose] def u33Gens : List (List ℕ) := [u33Ac, gAc]

@[expose] def evalW (gens : List (List ℕ)) (w : List ℕ) : List ℕ :=
  w.foldr (fun i acc => mulC (gens.getD i oneC) acc) oneC

@[expose] def bfsW (gens : List (List ℕ)) :
    ℕ → Std.HashSet (List ℕ) → List (List ℕ) → List (List ℕ × List ℕ) → List (List ℕ)
  | 0, _, acc, _ => acc
  | fuel + 1, seen, acc, fr =>
    match fr with
    | [] => acc
    | _ =>
      let st := fr.foldl
        (fun (st : Std.HashSet (List ℕ) × List (List ℕ) × List (List ℕ × List ℕ)) wx =>
          (List.range gens.length).foldl
            (fun (st : Std.HashSet (List ℕ) × List (List ℕ) × List (List ℕ × List ℕ)) i =>
              let y := mulC (gens.getD i oneC) wx.2
              if st.1.contains y then st
              else (st.1.insert y, (i :: wx.1) :: st.2.1, (i :: wx.1, y) :: st.2.2)) st)
        (seen, acc, [])
      bfsW gens fuel st.1 st.2.1 st.2.2

@[expose] def wordsOf (gens : List (List ℕ)) : List (List ℕ) :=
  bfsW gens 400 ((∅ : Std.HashSet (List ℕ)).insert oneC) [[]] [([], oneC)]

@[expose] def u33Elems (_ : Unit := ()) : List (List ℕ) := (wordsOf u33Gens).map (evalW u33Gens)

@[expose] def isInvC (x : List ℕ) : Bool := mulC x x == oneC && x != oneC

@[expose] def commC (x y : List ℕ) : Bool := mulC x y == mulC y x

@[expose] def fixCount (x : List ℕ) : ℕ := ((List.range 64).filter fun n => mulVecC x n == n).length

@[expose] def centCount (L : List (List ℕ)) (u : List ℕ) : ℕ := (L.filter (commC u)).length

@[expose] def validCheck (L : List (List ℕ)) : Bool :=
  L.all fun x => x.length == 6 && x.all fun c => decide (c < 64)

@[expose] def closedCheck (gens L : List (List ℕ)) : Bool :=
  let hs : Std.HashSet (List ℕ) := Std.HashSet.ofList L
  L.all fun x => gens.all fun g => hs.contains (mulC g x)

@[expose] def nodupCheck (L : List (List ℕ)) : Bool :=
  decide (((L.map code36).mergeSort).IsChain (· < ·))

@[expose] def u33U0 : List ℕ := [1, 2, 5, 40, 16, 32]

@[expose] def u33CycWords : List (List ℕ) :=
  [[], [0, 1, 1, 1, 1], [1, 1, 1, 1], [1, 1, 0, 1, 1, 1, 1, 1], [0, 1, 0, 0, 1, 0, 1],
    [1, 0, 0, 1, 1, 0, 1]]

@[expose] def zeroC : List ℕ := [0, 0, 0, 0, 0, 0]

@[expose] def innerInvCheck (_ : Unit := ()) : Bool :=
  let L := u33Elems ()
  let I := L.filter isInvC
  I.length == 63 && I.all fun u => fixCount u == 16 && centCount L u == 96 &&
    centCount g22Elems u == 192 && L.any fun g => mulC g u33U0 == mulC u g

@[expose] def outerInvCheck (_ : Unit := ()) : Bool :=
  let hs : Std.HashSet (List ℕ) := Std.HashSet.ofList (u33Elems ())
  let J := g22Elems.filter fun x => !hs.contains x && mulC x x == oneC
  J.length == 252 && J.all fun x => fixCount x == 8 && centCount g22Elems x == 48

@[expose] def threeACheck (_ : Unit := ()) : Bool :=
  let L := u33Elems ()
  let I := L.filter isInvC
  L.all fun r => !(mulC r (mulC r r) == oneC && r != oneC && I.any (commC r)) ||
    (List.range 63).all fun n => mulVecC r (n + 1) != n + 1

@[expose] def transCheck (_ : Unit := ()) : Bool :=
  let L := u33Elems ()
  (List.range 63).all fun n => L.any fun x => mulVecC x 1 == n + 1

@[expose] def powN (x : List ℕ) : ℕ → List ℕ
  | 0 => oneC
  | n + 1 => mulC x (powN x n)

@[expose] def pow168Check (_ : Unit := ()) : Bool := (u33Elems ()).all fun x => powN x 168 == oneC

@[expose] def endCheck : Bool :=
  (u33CycWords.map fun w => mulVecC (evalW u33Gens w) 1) == oneC &&
    (List.range 64).all fun v =>
      let cols := u33CycWords.map fun w => mulVecC (evalW u33Gens w) v
      !(commC cols u33Ac && commC cols gAc) || cols == zeroC || cols == oneC

end Certificates.TitsR2V6
