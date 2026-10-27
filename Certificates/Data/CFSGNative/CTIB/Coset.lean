module

public import Certificates.Data.CFSGNative.CTIB.Lift

public section

namespace CFSG.Monster.B.CTIB.Native

set_option compiler.extract_closed false

@[expose] def genInvImgs (_ : Unit) : Array Nat := autPow gArr (genImgs 1) 47

@[expose] def letterImgs (gi : Array Nat) (l : Int) : Array Nat :=
  if l = 1 ∨ l = -1 then genImgs 0 else if l = 2 then genImgs 1 else gi

@[expose] def wordAut (gi : Array Nat) (w : List Int) : Array Nat :=
  w.foldl (fun A l => autComp gArr A (letterImgs gi l)) id23

@[expose] def rankOff (k : Nat) : Nat := if k = 6 then 0 else if k = 8 then 15 else 30

@[expose] def centWordN (k j : Nat) : List Int := (parseWords centWordStr).getD (rankOff k + j) []

@[expose] def deltaN (k j : Nat) : Nat := deltaVals.getD (rankOff k + j) 0

@[expose] def liftImgsN (k : Nat) : List Nat :=
  if k = 6 then liftImgs6 else if k = 8 then liftImgs8 else liftImgs10

@[expose] def liftRowsN (k : Nat) : List Nat :=
  if k = 6 then liftRows6 else if k = 8 then liftRows8 else liftRows10

@[expose] def sqCode (k : Nat) : Nat := if k = 8 then 0 else 2 ^ 22

@[expose] def orbitRecs (k : Nat) : List (Nat × Nat) :=
  let rec pairs : List Nat → List (Nat × Nat)
    | a :: b :: t => (a, b) :: pairs t
    | _ => []
  pairs (parseNats (if k = 6 then orbitStr6 else if k = 8 then orbitStr8 else orbitStr10))

@[expose] def fusionRecsN (k : Nat) : List (Nat × Nat × Nat) :=
  if k = 6 then fusionRecs6 else if k = 8 then fusionRecs8 else fusionRecs10

@[expose] def qinv (d : Nat) : Nat := qmul gArr (qmul gArr d d) d

@[expose] def innerOK (A : Array Nat) (d : Nat) : Bool :=
  A.size == 22 &&
    (List.range 22).all fun i => A[i]! == qmul gArr (qmul gArr (qinv d) (2 ^ i)) d

@[expose] def invWord (w : List Int) : List Int := (w.map (- ·)).reverse

@[expose] def deltaAutOK (gi H Ag : Array Nat) (g : List Int) (d : Nat) : Bool :=
  innerOK (autComp gArr (autComp gArr (autComp gArr (autPow gArr H 3) (wordAut gi (invWord g))) H)
    Ag) d

@[expose] def fuseAct (A : Array Nat) (gA : Array (Array Nat)) (ds : Array Nat) (m n : Nat) :
    Nat :=
  if m < 22 then qconj gArr A m n else fuse gArr (gA.getD (m - 22) #[]) (ds.getD (m - 22) 0) n

@[expose] def repsIncreasing (l : List Nat) : Bool := chainLt l

@[expose] def cosetOK (k count : Nat) : Bool :=
  let A := (liftImgsN k).toArray
  let L := (liftRowsN k).toArray
  let w := sqCode k
  let valid : Nat → Bool := fun n => decide (n < 2 ^ 23) && isInv gArr A w n
  let gi := genInvImgs ()
  let gA : Array (Array Nat) := ((List.range 15).map fun j => wordAut gi (centWordN k j)).toArray
  let ds : Array Nat := ((List.range 15).map fun j => deltaN k j).toArray
  let qr := orbitRecs k
  let fr := fusionRecsN k
  countInv gArr A L w == count &&
  qr.all (fun r => orbitOK (qconj gArr A) 22 valid r.1 r.2) &&
  repsIncreasing (qr.map (·.1)) && (qr.map (·.2)).sum == count &&
  repsIncreasing (fr.map (·.2.2)) && (fr.map (·.2.1)).sum == count &&
  fr.all (fun r =>
    let c := natBfs (fuseAct A gA ds) 37 r.2.2 (r.2.1 + 1)
    natCertOK (fuseAct A gA ds) 37 valid r.2.2 c.1 c.2.1 c.2.2.1 c.2.2.2 &&
      c.1.size == r.2.1 && c.1.all (r.2.2 ≤ ·) &&
      (qr.filter fun q => c.1.contains q.1).length == r.1) &&
  (List.range 15).all (fun j => deltaAutOK gi A (gA.getD j #[]) (centWordN k j) (deltaN k j))

@[expose] def centImgsOK (_ : Unit) : Bool :=
  let gi := genInvImgs ()
  let imgs := parseNats centImgsStr
  (List.range 45).all fun t =>
    (wordAut gi ((parseWords centWordStr).getD t [])).toList == (imgs.drop (22 * t)).take 22

@[expose] def cosetCheck (_ : Unit) : Bool :=
  cosetOK 6 67584 && cosetOK 8 18432 && cosetOK 10 6144 && centImgsOK ()

end CFSG.Monster.B.CTIB.Native
