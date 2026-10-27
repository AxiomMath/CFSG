module

public import Certificates.Data.Kernel.Misc.G24
public import Certificates.Data.Kernel.M24G.Replay

public section

namespace CFSG.KC.EvenSporSuz.Syl

open CFSG.KC.ONanSmall CFSG.KC.M24G CFSG.KC.Misc.G24

@[expose] def bal {α : Type} : Nat → Nat → List α → KTree α × List α
  | 0, _, L => (.leaf, L)
  | _ + 1, 0, L => (.leaf, L)
  | d + 1, n + 1, L =>
    match bal d (n / 2) L with
    | (l, []) => (l, [])
    | (l, x :: L') =>
      match bal d (n - n / 2) L' with
      | (r, R) => (.node l x r, R)

@[expose] def treeOf (L : List (Nat × Nat)) : KTree (Nat × Nat) := (bal 20 L.length L).1

@[expose] def incK : List (Nat × Nat) → Bool
  | [] => true
  | [_] => true
  | a :: b :: L => Nat.blt a.1 b.1 && incK (b :: L)

@[expose] noncomputable def canonK (X : Nat) : Bool :=
  Nat.beq (Nat.shiftRight X 1152) 0 && Nat.beq (Nat.land X (Nat.mul laneOnes 252)) 0 &&
    Nat.beq (Nat.land (Nat.land X (Nat.shiftRight X 1)) laneOnes) 0

@[expose] noncomputable def letQ (y : Nat) (k : Nat → Bool) : Bool :=
  Nat.rec (motive := fun _ => Bool) (k (nat_lit 0)) (fun m _ => k (Nat.succ m)) y

@[expose] noncomputable def elemK (T OT : KTree (Nat × Nat)) (G GI : List Nat) (z e cd q : Nat) :
    Bool :=
  canonK e && G.all (fun g => (findK (mulF3 e g) T).isSome) &&
    (bif Nat.beq (cd / 4) 0 then Nat.beq e one3 else
      match findK (mulF3 e (GI.getD (cd % 4) 0)) T with
      | some c => Nat.beq (c / 4 + 1) (cd / 4)
      | none => false) &&
    (!(Nat.beq q one3 && !Nat.beq e one3 && !Nat.beq e z) || (findK e OT).isSome)

@[expose] def slice {α : Type} (L : List α) (c : Nat) : List α := (L.drop (1024 * c)).take 1024

@[expose] def ind (a b : Nat) : Nat := bif Nat.beq a b then 1 else 0

@[expose] noncomputable def chunkGo (T OT : KTree (Nat × Nat)) (G GI : List Nat) (z x1 x2 : Nat) :
    List (Nat × Nat) → Nat → Nat → Nat → Bool
  | [], a, b, c => Nat.beq a 0 && Nat.beq b 0 && Nat.beq c 0
  | p :: L, a, b, c => letQ (mulF3 p.1 p.1) fun q =>
    elemK T OT G GI z p.1 p.2 q &&
      chunkGo T OT G GI z x1 x2 L (a - ind q z) (b - ind q x1) (c - ind q x2) &&
      Nat.ble (ind q z) a && Nat.ble (ind q x1) b && Nat.ble (ind q x2) c

@[expose] noncomputable def chunkK (T OT : KTree (Nat × Nat)) (G GI : List Nat) (z x1 x2 : Nat)
    (ED : List (Nat × Nat)) (sz s1 s2 : List Nat) (c : Nat) : Bool :=
  chunkGo T OT G GI z x1 x2 (slice ED c) (sz.getD c 0) (s1.getD c 0) (s2.getD c 0)

@[expose] noncomputable def orbK (OT : KTree (Nat × Nat)) (G GI R : List Nat) (v cd : Nat) : Bool :=
  canonK v && Nat.blt (cd / 256) 14 &&
    bif Nat.beq (cd / 4 % 64) 0 then Nat.beq v (R.getD (cd / 256) 0) else
      match findK (mulF3 (mulF3 (GI.getD (cd % 4) 0) v) (G.getD (cd % 4) 0)) OT with
      | some c => Nat.beq (c / 4 + 1) (cd / 4)
      | none => false

@[expose] def tgtL (x1 x2 t : Nat) : Nat := bif Nat.beq t 1 then x1 else x2

@[expose] noncomputable def globK (G GI : List Nat) (z x1 x2 : Nat) (R C TG : List Nat)
    (ED : List (Nat × Nat)) (sz s1 s2 : List Nat) : Bool :=
  Nat.beq G.length 4 && Nat.beq GI.length 4 &&
    (List.range 4).all (fun k => canonK (G.getD k 0) && canonK (GI.getD k 0) &&
      Nat.beq (mulF3 (G.getD k 0) (GI.getD k 0)) one3) &&
    canonK z && canonK x1 && canonK x2 &&
    G.all (fun g => Nat.beq (mulF3 g x1) (mulF3 x1 g) && Nat.beq (mulF3 g x2) (mulF3 x2 g) &&
      Nat.beq (mulF3 g z) (mulF3 z g)) &&
    Nat.beq z (Nat.mul 2 one3) && Nat.beq x2 (mulF3 z x1) &&
    Nat.beq R.length 14 && Nat.beq C.length 14 && Nat.beq TG.length 14 &&
    (List.range 14).all (fun k => canonK (R.getD k 0) && canonK (C.getD k 0) &&
      (Nat.beq (TG.getD k 0) 1 || Nat.beq (TG.getD k 0) 2) &&
      Nat.beq (mulF3 (R.getD k 0) (C.getD k 0)) (mulF3 (C.getD k 0) (tgtL x1 x2 (TG.getD k 0)))) &&
    Nat.beq ED.length 16384 && incK ED && ED.any (fun p => Nat.beq p.1 one3) &&
    Nat.beq sz.length 16 && Nat.beq s1.length 16 && Nat.beq s2.length 16 &&
    Nat.beq sz.sum 1056 && Nat.beq s1.sum 384 && Nat.beq s2.sum 352

@[expose] def lanesL : List Nat → Nat
  | [] => 0
  | a :: l => a + 256 * lanesL l

@[expose] noncomputable def evalL (M I : List Nat) (w : List Nat) : Nat :=
  w.foldl (fun acc c => mulF3 acc (bif Nat.beq (c % 2) 0 then M.getD (c / 2) one3
    else I.getD (c / 2) one3)) one3

end CFSG.KC.EvenSporSuz.Syl
