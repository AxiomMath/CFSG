module

public import Certificates.Data.CFSGNative.MonsterB.Co2Chain
public import CFSG.Quasithin.Background.Harris.R1.J2VertWords

public section

namespace CFSG.Quasithin.Background.Harris.R1.J2Vert

open CFSG.Monster.B.Co2.Native

@[expose] def evalW (n : Nat) (base : Array (Array Nat)) : List (Fin 3) → Array Nat
  | [] => idA n
  | k :: w => compA n (base.getD k.val (idA n)) (evalW n base w)

@[expose] def rGenArrs (n : Nat) (base : Array (Array Nat)) : Array (Array Nat) :=
  ((List.range 8).map fun i => evalW n base (rWords.getD i [])).toArray

@[expose] def relVal (n : Nat) (gs : Array (Array Nat)) (r : List (Fin 8 × Bool)) : Array Nat :=
  r.foldr (fun p acc => compA n (if p.2 then gs.getD p.1.val (idA n)
    else invCand n (gs.getD p.1.val (idA n))) acc) (idA n)

@[expose] def genCheck (n : Nat) (gs : Array (Array Nat)) (k : Nat) : Bool :=
  (List.range k).all fun i => isInvA n (gs.getD i (idA n)) (invCand n (gs.getD i (idA n)))

@[expose] def relCheck (n : Nat) (gs : Array (Array Nat)) (rels : List (List (Fin 8 × Bool))) :
    Bool :=
  genCheck n gs 8 && rels.all fun r => eqA n (relVal n gs r) (idA n)

@[expose] def buildTab (n : Nat) (gs : Array (Array Nat)) (pl : List (Nat × Nat)) :
    List (Array Nat) :=
  (pl.foldl (fun (acc : Array (Array Nat)) (pr : Nat × Nat) =>
    acc.push (compA n (acc.getD pr.1 (idA n)) (gs.getD pr.2 (idA n)))) #[idA n]).toList

@[expose] def tabLower (n : Nat) (gs : Array (Array Nat)) (pl : List (Nat × Nat)) (N : Nat) : Bool :=
  decide ((buildTab n gs pl).length = N) && decide (buildTab n gs pl).Nodup

@[expose] def tabClosed (n : Nat) (gs : Array (Array Nat)) (k : Nat) (pl : List (Nat × Nat)) :
    Bool :=
  genCheck n gs k && (buildTab n gs pl).all fun x => (List.range k).all fun i =>
    (buildTab n gs pl).contains (compA n x (gs.getD i (idA n))) &&
      (buildTab n gs pl).contains (compA n x (invCand n (gs.getD i (idA n))))

@[expose] def tabMem (n : Nat) (gs : Array (Array Nat)) (pl : List (Nat × Nat))
    (ts : Array (Array Nat)) (k : Nat) : Bool :=
  (List.range k).all fun i => (buildTab n gs pl).contains (ts.getD i (idA n))

@[expose] def normalLineCheck (n : Nat) (sg ts : Array (Array Nat)) (k : Nat)
    (qs : List (Array Nat)) : Bool :=
  qs.all fun v =>
    !eqA n (compA n v v) (idA n) || eqA n v (idA n) || eqA n v (sg.getD 0 (idA n)) ||
    !((List.range k).all fun j =>
      eqA n (compA n (compA n (ts.getD j (idA n)) v) (invCand n (ts.getD j (idA n)))) v ||
      eqA n (compA n (compA n (ts.getD j (idA n)) v) (invCand n (ts.getD j (idA n))))
        (compA n (sg.getD 0 (idA n)) v)) ||
    eqA n v (sg.getD 1 (idA n)) || eqA n v (compA n (sg.getD 0 (idA n)) (sg.getD 1 (idA n)))

@[expose] def rootCount (n : Nat) (t : List (Array Nat)) (x s : Array Nat) : Nat :=
  (t.filter fun y => eqA n (compA n y x) (compA n x y) && eqA n (compA n y y) s).length

@[expose] def centCount (n : Nat) (t : List (Array Nat)) (x : Array Nat) : Nat :=
  (t.filter fun y => eqA n (compA n y x) (compA n x y)).length

end CFSG.Quasithin.Background.Harris.R1.J2Vert
