module

public import Certificates.Data.SmithL6Coll

public section

namespace CFSG.SmithL6.CollK

open CFSG.SmithL6

@[expose] def apK : List Nat → Nat → Nat
  | [], _ => 0
  | c :: l, x => if x % 2 = 1 then c ^^^ apK l (x / 2) else apK l (x / 2)

@[expose] def ptMask : Nat := uco.toList.foldl (fun m q => m ||| 2 ^ q) 0

@[expose] def apN (l : List Nat) (p x : Nat) : Nat :=
  apK l (x % 2 ^ l.length) ^^^ (if x.testBit l.length then p else 0)

@[expose] def pruneK (l : List Nat) (p : Nat) : Bool :=
  (List.range l.length).all (fun m => !decide (l.getD m 0 < 2 ^ (l.length + 1)) ||
      apN l p (l.getD m 0) == 2 ^ m) &&
    (!decide (p < 2 ^ (l.length + 1)) || apN l p p == 2 ^ l.length)

@[expose] def QK (l : List Nat) (p : Nat) : Bool :=
  (collNewPts l.length).all (fun q => ptMask.testBit (apN l p q)) && pruneK l p &&
    !(List.range (2 ^ l.length)).any fun s => apK l s == p

@[expose] def goG (Q : List Nat → Nat → Bool) : Nat → List Nat → List (List Nat)
  | 0, l => [l]
  | n + 1, l => (uco.toList.filter (Q l)).flatMap fun p => goG Q n (l ++ [p])

@[expose] def invK (x : List Nat) : Bool :=
  (List.range 9).all (fun m => apK x (x.getD m 0) == 2 ^ m) &&
    (List.range 9).any fun m => x.getD m 0 != 2 ^ m

@[expose] def fld (T s : Nat) : Nat := (T >>> (9 * s)) % 512

@[expose] def packF : List Nat → Nat
  | [] => 0
  | a :: r => a + 512 * packF r

@[expose] def rep (n : Nat) : Nat := (2 ^ (9 * n) - 1) / 511

@[expose] def tab (l : List Nat) : Nat := packF ((List.range (2 ^ l.length)).map (apK l))

@[expose] def tabStep (T j p : Nat) : Nat := T + (T ^^^ p * rep (2 ^ j)) * 2 ^ (9 * 2 ^ j)

@[expose] def apNT (T j p x : Nat) : Nat := fld T (x % 2 ^ j) ^^^ (if x.testBit j then p else 0)

@[expose] def pruneT (l : List Nat) (T j p : Nat) : Bool :=
  (List.range j).all (fun m => !decide (l.getD m 0 < 2 ^ (j + 1)) ||
      apNT T j p (l.getD m 0) == 2 ^ m) &&
    (!decide (p < 2 ^ (j + 1)) || apNT T j p p == 2 ^ j)

@[expose] def QT (np l : List Nat) (T j p : Nat) : Bool :=
  np.all (fun q => ptMask.testBit (apNT T j p q)) && pruneT l T j p &&
    !(List.range (2 ^ j)).any fun s => fld T s == p

@[expose] def invT (x : List Nat) (T : Nat) : Bool :=
  (List.range 9).all (fun m => fld T (x.getD m 0) == 2 ^ m) &&
    (List.range 9).any fun m => x.getD m 0 != 2 ^ m

@[expose] def goT : List (List Nat) → List Nat → Nat → List (List Nat)
  | [], l, T => if invT l T then [l] else []
  | np :: nps, l, T =>
    (uco.toList.filter (QT np l T l.length)).flatMap fun p =>
      goT nps (l ++ [p]) (tabStep T l.length p)

@[expose] def topT (R : List (List (List Nat))) (i : Nat) : Bool :=
  goT ((List.range' 1 8).map collNewPts) [uco.toList.getD i 0] (512 * uco.toList.getD i 0) ==
    R.getD i []

@[expose] def bitsOf {α : Type} (f : α → Bool) : List α → Nat
  | [] => 0
  | a :: l => (if f a then 1 else 0) + 2 * bitsOf f l

@[expose] def tab9 (A : List Nat) : Nat :=
  (List.range 9).foldl (fun T j => tabStep T j (A.getD j 0)) 0

@[expose] def commT (A : List Nat) (TA : Nat) (B : List Nat) (TB : Nat) : Bool :=
  (List.range 9).all fun m => fld TA (B.getD m 0) == fld TB (A.getD m 0)

@[expose] def atMost : Nat → Nat → Bool
  | 0, x => x == 0
  | k + 1, x => x == 0 || atMost k (x &&& (x - 1))

@[expose] def tripK (P : List ((List Nat × Nat × Nat × Nat) × Nat)) (a b G D : Nat)
    (AB : List Nat) : Bool :=
  P.all fun r => !D.testBit r.2 || r.2 == a || r.2 == b || r.1.1 == AB ||
    (atMost 16 (G &&& r.1.2.2.1) && atMost 23 (D &&& r.1.2.2.2))

@[expose] def rowK (LM : List (List Nat × Nat × Nat × Nat)) (a : Nat) : Bool :=
  let r := LM.getD a ([], 0, 0, 0)
  let A := r.1
  let TA := r.2.1
  let Fa := r.2.2.1
  let Ma := r.2.2.2
  let P := LM.zipIdx.filter fun s => Ma.testBit s.2
  A.length == 9 && A.all (· < 512) && TA == tab9 A && Fa == bitsOf (fun v => fld TA v == v) (List.range 512) &&
    Ma == bitsOf (fun s => commT A TA s.1 s.2.1) LM && atMost 64 Fa &&
    P.all fun s => s.2 == a ||
      (atMost 16 (Fa &&& s.1.2.2.1) && atMost 23 (Ma &&& s.1.2.2.2)) ||
        tripK P a s.2 (Fa &&& s.1.2.2.1) (Ma &&& s.1.2.2.2) (s.1.1.map (fld TA))

@[expose] def rowsK (LM : List (List Nat × Nat × Nat × Nat)) (lo n : Nat) : Bool :=
  (List.range n).all fun i => rowK LM (lo + i)

end CFSG.SmithL6.CollK
