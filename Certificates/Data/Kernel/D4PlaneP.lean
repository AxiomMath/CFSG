module

public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.D4TwoPlaneData

public section

namespace CFSG.KC.D4PlaneP

open CFSG.Quasithin CFSG.AGLEmbedding.D4Two

@[expose] def r3 : Nat := 0x010101010101010101010101010101010101010101010101

@[expose] def m64 : Nat := 0xFFFFFFFFFFFFFFFF

@[expose] def m192 : Nat := 0xFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFF

@[expose] def laneK (s Y o : Nat) : Nat := s &&& (((Y >>> o) &&& 255) * r3)

@[expose] def mulKs (s Y o : Nat) : Nat :=
  laneK s Y o ^^^ (laneK s Y (64 + o) <<< 64) ^^^ (laneK s Y (128 + o) <<< 128)

@[expose] def mulK (X Y k : Nat) : Nat := mulKs (((X >>> k) &&& r3) * 255) Y (8 * k)

@[expose] def redP (x : Nat) : Nat :=
  (x &&& m192) ^^^ ((x >>> 192) &&& m64) ^^^ (((x >>> 192) &&& m64) <<< 64) ^^^
    ((x >>> 256) <<< 64) ^^^ ((x >>> 256) <<< 128)

@[expose] def mulP (X Y : Nat) : Nat :=
  redP (mulK X Y 0 ^^^ mulK X Y 1 ^^^ mulK X Y 2 ^^^ mulK X Y 3 ^^^ mulK X Y 4 ^^^ mulK X Y 5 ^^^
    mulK X Y 6 ^^^ mulK X Y 7)

@[expose] def oneP : Nat := 0x8040201008040201

@[expose] def encE (v : Nat) : Nat := (v &&& 1) ||| (((v >>> 1) &&& 1) <<< 64) ||| ((v >>> 2) <<< 128)

@[expose] def packL : List GF8 → Nat
  | [] => 0
  | e :: l => encE e.toNat ||| (packL l <<< 1)

@[expose] def packA (A : Array GF8) : Nat := packL ((List.range 64).map fun t => A.getD t 0)

@[expose] def letP (ls : List Nat) (l : Nat) : Nat := ls.getD (min l 17) 0

@[expose] def wordP (ls : List Nat) (w : List Nat) : Nat :=
  w.foldr (fun l A => mulP (letP ls l) A) oneP

@[expose] def bfsStepP (A B : Nat) (acc : List Nat) (p : Nat × Bool) : List Nat :=
  acc ++ [mulP (acc.getD p.1 oneP) (if p.2 then A else B)]

@[expose] def bfsP (A B : Nat) (par : List (Nat × Bool)) : List Nat :=
  par.foldl (bfsStepP A B) [oneP]

@[expose] def enumP (ls : List Nat) : List Nat := bfsP (wordP ls wordA) (wordP ls wordB) bfsPar

@[expose] def bfsOK (A B : Nat) (par : List (Nat × Bool)) (es : List Nat) : Bool :=
  es.length == par.length + 1 && es.getD 0 0 == oneP &&
    (List.range par.length).all fun k =>
      let p := par.getD k (0, false)
      decide (p.1 ≤ k) && es.getD (k + 1) 0 == mulP (es.getD p.1 oneP) (if p.2 then A else B)

@[expose] def cube1P (x : Nat) : Bool := mulP x (mulP x x) == oneP

@[expose] def commP (x y : Nat) : Bool := mulP x y == mulP y x

@[expose] def spanP (x y : Nat) : List Nat :=
  [oneP, x, mulP x x].flatMap fun u => [oneP, y, mulP y y].map fun v => mulP u v

@[expose] def atP (es : List Nat) (i : Nat) : Nat := es.getD i oneP

@[expose] def coverR (Om : List Nat) (Es : List (List Nat)) : Bool :=
  Om.all fun x =>
    x == oneP || (Om.filter (commP x)).all fun y =>
      [oneP, x, mulP x x].contains y ||
        let S := spanP x y
        Es.any fun E => E.contains x && E.contains y && E.all fun p => S.contains p

@[expose] def coverP (es : List Nat) (cs : List D4PlaneCert) : Bool :=
  coverR (es.filter cube1P) (cs.map fun c => c.idxs.map (atP es))

@[expose] def poolP (ls es : List Nat) (c : D4PlaneCert) : Bool :=
  c.pool.all fun e =>
    c.idxs.contains e.2 && atP es e.2 != oneP && commP (wordP ls e.1) (atP es e.2)

@[expose] def prodP (l : List Nat) : Nat := l.foldr mulP oneP

@[expose] def targetP (ls : List Nat) (c : D4PlaneCert) : Bool :=
  let pa := c.pool.map fun e => wordP ls e.1
  (List.range 18).all fun j =>
    prodP ((c.targets.getD j []).map fun m => pa.getD m oneP) == letP ls j

end CFSG.KC.D4PlaneP

end
