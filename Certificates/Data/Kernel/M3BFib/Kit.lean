module

public import Certificates.Data.CFSGNative.Timmesfeld.M3B

public section

namespace CFSG.KC.M3BF

open Timmesfeld.M3B (WT)

@[expose] noncomputable def enc (ds : List Nat) : Nat :=
  List.rec (motive := fun _ => Nat) 0 (fun d _ ih => Nat.add d (Nat.mul 64 ih)) ds

@[expose] noncomputable def digN (n : Nat) (x : Nat) : List Nat :=
  Nat.rec (motive := fun _ => Nat → List Nat) (fun _ => [])
    (fun _ ih y => List.cons (Nat.mod y 64) (ih (Nat.div y 64))) n x

@[expose] noncomputable def dig (x : Nat) : List Nat := digN 12 x

@[expose] noncomputable def dig3 (x : Nat) : List Nat :=
  List.rec (motive := fun _ => List Nat) [] (fun d _ ih => List.cons (Nat.mod d 3) ih) (dig x)

@[expose] noncomputable def red (x : Nat) : Nat := enc (dig3 x)

@[expose] noncomputable def vm (u P : List Nat) : Nat :=
  List.rec (motive := fun _ => List Nat → Nat) (fun _ => 0)
    (fun p _ ih v => List.rec (motive := fun _ => Nat) 0
      (fun a v' _ => Nat.add (Nat.mul a p) (ih v')) v) P u

@[expose] noncomputable def dot (u v : List Nat) : Nat :=
  List.rec (motive := fun _ => List Nat → Nat) (fun _ => 0)
    (fun a _ ih w => List.rec (motive := fun _ => Nat) 0
      (fun b w' _ => Nat.add (Nat.mul a b) (ih w')) w) u v

@[expose] noncomputable def ch2 (u : Nat) : Nat := Nat.div (Nat.mul u (Nat.sub u 1)) 2

@[expose] noncomputable def colsK (rs : List (List Nat)) : List Nat :=
  List.rec (motive := fun _ => List Nat) (List.replicate 12 0)
    (fun r _ ih => List.zipWith (fun d c => Nat.add d (Nat.mul 64 c)) r ih) rs

@[expose] noncomputable def zpre (k : Nat) (ds : List Nat) : List Nat :=
  List.rec (motive := fun _ => Nat → List Nat) (fun _ => [])
    (fun d _ ih m => Nat.rec (motive := fun _ => List Nat) (List.cons d (ih 0))
      (fun m' _ => List.cons 0 (ih m')) m) ds k

@[expose] noncomputable def upDiag (gs : List (List Nat)) (j : Nat) : List Nat × List Nat :=
  List.rec (motive := fun _ => Nat → List Nat × List Nat) (fun _ => ([], []))
    (fun g _ ih k => (fun p => (List.cons (enc (zpre (Nat.succ k) g)) p.1,
      List.cons (List.getD g k 0) p.2)) (ih (Nat.succ k))) gs j

abbrev PD := List Nat × List Nat × Nat

@[expose] noncomputable def oneK : PD :=
  ((List.range 12).map (fun i => Nat.pow 64 i), List.replicate 12 0, 1)

@[expose] noncomputable def compK (Lp : List Nat) (D D' : PD) : PD :=
  (fun (Gd : List (List Nat)) => (fun (UD : List Nat × List Nat) =>
    (D.1.map (fun r => red (vm (dig3 r) D'.1)),
     List.zipWith (fun r ci => (fun u => Nat.mod (Nat.add (Nat.add (Nat.mul D'.2.2 ci) (dot u D'.2.1))
        (Nat.add (dot (u.map ch2) UD.2) (dot u (dig (vm u UD.1))))) 3) (dig3 r)) D.1 D.2.1,
     Nat.mod (Nat.mul D.2.2 D'.2.2) 3)) (upDiag Gd 0))
    ((fun (MT : List Nat) => D'.1.map (fun r => dig3 (vm (dig3 (red (vm (dig3 r) Lp))) MT)))
      (colsK (D'.1.map dig3)))

@[expose] noncomputable def powK (Lp : List Nat) (D : PD) (k : Nat) : PD :=
  Nat.rec (motive := fun _ => PD) oneK (fun _ acc => compK Lp acc D) k

@[expose] noncomputable def adOfK (Lp : List Nat) (L : List PD) (t : WT) : PD :=
  WT.rec (motive := fun _ => PD) (fun i => L.getD i oneK) (fun _ _ a b => compK Lp a b)
    (fun _ k a => powK Lp a k) t

@[expose] noncomputable def pdEq (D D' : PD) : Bool :=
  D.1 == D'.1 && D.2.1 == D'.2.1 && D.2.2 == D'.2.2

@[expose] noncomputable def LpM : List Nat :=
  (List.range 12).map fun a => enc ((Timmesfeld.M3B.mRows.getD a []).take a)

@[expose] noncomputable def ofRows (R : List (List Nat)) (c : List Nat) (lam : Nat) : PD :=
  (R.map enc, c, lam)

@[expose] noncomputable def qK (j : Nat) : PD :=
  ((List.range 12).map (fun i => Nat.pow 64 i),
    (List.range 12).map (fun i => (Timmesfeld.M3B.mRows.getD i []).getD j 0), 1)

@[expose] noncomputable def DaK : PD := ofRows Timmesfeld.M3B.xRows Timmesfeld.M3B.c1 2

@[expose] noncomputable def DbK : PD := ofRows Timmesfeld.M3B.yRows Timmesfeld.M3B.c2 1

@[expose] noncomputable def LK : List PD :=
  [DaK, DbK, powK LpM DaK 55, powK LpM DbK 21] ++ (List.range 12).map qK

end CFSG.KC.M3BF

end
