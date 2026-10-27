module

public import Certificates.Data.Kernel.D4PlaneP

public section

namespace CFSG.KC.D42Cls

open CFSG.KC.D4PlaneP

abbrev N3 := Nat × Nat × Nat

@[expose] def x3 (a b : N3) : N3 := (a.1 ^^^ b.1, a.2.1 ^^^ b.2.1, a.2.2 ^^^ b.2.2)

@[expose] def red5 (c0 c1 c2 c3 c4 : Nat) : N3 := (c0 ^^^ c3, c1 ^^^ c3 ^^^ c4, c2 ^^^ c4)

@[expose] def m3 (a b : N3) : N3 :=
  red5 (a.1 &&& b.1) ((a.1 &&& b.2.1) ^^^ (a.2.1 &&& b.1))
    ((a.1 &&& b.2.2) ^^^ (a.2.1 &&& b.2.1) ^^^ (a.2.2 &&& b.1))
    ((a.2.1 &&& b.2.2) ^^^ (a.2.2 &&& b.2.1)) (a.2.2 &&& b.2.2)

@[expose] def s3k (s0 s1 s2 b0 b1 b2 : Nat) : N3 :=
  (s0 * b0 ^^^ s1 * b2 ^^^ s2 * b1, s0 * b1 ^^^ s1 * (b0 ^^^ b2) ^^^ s2 * (b1 ^^^ b2),
    s0 * b2 ^^^ s1 * b1 ^^^ s2 * (b0 ^^^ b2))

@[expose] def s3 (s : Nat) (b : N3) : N3 := s3k (s % 2) (s / 2 % 2) (s / 4 % 2) b.1 b.2.1 b.2.2

@[expose] def dotS : List Nat → List N3 → N3
  | s :: l, b :: m => x3 (s3 s b) (dotS l m)
  | _, _ => (0, 0, 0)

@[expose] def dotM : List N3 → List N3 → N3
  | a :: l, b :: m => x3 (m3 a b) (dotM l m)
  | _, _ => (0, 0, 0)

@[expose] def cLanes (CR : List (List N3)) (u : List N3) : List N3 :=
  CR.map fun crow => dotM crow u

@[expose] def fLanes (CR : List (List N3)) (W : List N3) (r : List (List Nat)) : List N3 :=
  cLanes CR (r.map fun row => dotS row W)

@[expose] def neq1 (O : Nat) (a : N3) (e : Nat) : Nat :=
  (a.1 ^^^ (e % 2) * O) ||| (a.2.1 ^^^ (e / 2 % 2) * O) ||| (a.2.2 ^^^ (e / 4 % 2) * O)

@[expose] def neqL (O : Nat) : List N3 → List Nat → Nat
  | a :: l, e :: m => neq1 O a e ||| neqL O l m
  | _, _ => 0

@[expose] def planes : List N3 → List Nat
  | a :: l => a.2.2 :: a.2.1 :: a.1 :: planes l
  | [] => []

@[expose] def minS : List Nat → Nat → Nat → Nat
  | p :: ps, M, acc =>
    bif M ^^^ (M &&& p) == 0 then minS ps M (2 * acc + 1) else minS ps (M ^^^ (M &&& p)) (2 * acc)
  | [], _, acc => acc

@[expose] def fldT (T : List Nat) (c : Nat) : Nat := (T.getD (c / 64) 0 >>> (192 * (c % 64))) &&& m192

@[expose] def entP (x t : Nat) : Nat :=
  ((x >>> t) &&& 1) ||| (((x >>> (64 + t)) &&& 1) <<< 1) ||| (((x >>> (128 + t)) &&& 1) <<< 2)

@[expose] def rowsP (x : Nat) : List (List Nat) :=
  (List.range 8).map fun i => (List.range 8).map fun j => entP x (8 * i + j)

@[expose] def colsP (x : Nat) : List Nat :=
  (List.range 8).map (fun i => entP x (8 * i)) ++ (List.range 8).map (fun i => entP x (8 * i + 1))

@[expose] def byteD (D c : Nat) : Nat := (D >>> (8 * c)) &&& 255

@[expose] def rowOK (N : Nat) (T TW : List Nat) (DP Vm : Nat) (S : List Nat)
    (row : Nat × Nat × Nat × List Nat) : Bool :=
  decide (row.1 < N) && decide (row.2.1 < N) && decide (row.2.2.1 < S.length) &&
  (row.1 + 1 == N || decide (fldT T row.1 < fldT T (row.1 + 1))) &&
  (bif byteD DP row.1 == 0 then fldT T row.1 == oneP
   else decide (byteD DP row.2.1 < byteD DP row.1) &&
     mulP (fldT T row.2.1) (S.getD row.2.2.1 oneP) == fldT T row.1) &&
  mulP (fldT T row.1) (fldT TW row.1) == Vm &&
  row.2.2.2.length == S.length &&
  (List.zip S row.2.2.2).all fun q => decide (q.2 < N) && mulP (fldT T row.1) q.1 == fldT T q.2

@[expose] def rowsAt (N : Nat) (T TW : List Nat) (DP Vm : Nat) (S : List Nat) :
    Nat → List (Nat × Nat × Nat × List Nat) → Bool
  | _, [] => true
  | b, row :: l => row.1 == b && rowOK N T TW DP Vm S row && rowsAt N T TW DP Vm S (b + 1) l

@[expose] def rowsOK (N : Nat) (T TW : List Nat) (DP Vm : Nat) (S : List Nat)
    (rows : List (List (Nat × Nat × Nat × List Nat))) (j : Nat) : Bool :=
  (rows.getD j []).length == min 64 (N - 64 * j) && rowsAt N T TW DP Vm S (64 * j) (rows.getD j [])

@[expose] def pieceT (X o : Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat) 0 (fun q acc => acc ||| (((X >>> (192 * q + o)) &&& 1) <<< q)) 64

@[expose] def laneT (T : List Nat) (o : Nat) : Nat :=
  T.foldr (fun X acc => pieceT X o ||| (acc <<< 64)) 0

@[expose] def laneOK (T : List Nat) (t : Nat) (a : N3) : Bool :=
  a.1 >>> 64 == laneT T t && a.2.1 >>> 64 == laneT T (64 + t) && a.2.2 >>> 64 == laneT T (128 + t)

@[expose] def crOK (T : List Nat) (CR : List (List N3)) (i : Nat) : Bool :=
  (CR.getD i []).length == 8 && ((List.range 8).zip (CR.getD i [])).all fun q => laneOK T (8 * i + q.1) q.2

@[expose] def wOK (TW : List Nat) (W : List N3) (col : Nat) : Bool :=
  W.length == 8 && ((List.range 8).zip W).all fun q => laneOK TW (8 * q.1 + col) q.2

@[expose] def maskOf (P : List Nat) : Nat := P.foldr (fun p acc => acc ||| (1 <<< (64 + p))) 0

@[expose] def strictL : List Nat → Bool
  | a :: b :: l => decide (a < b) && strictL (b :: l)
  | _ => true

@[expose] def evalW (sym : List Nat) (w : List Nat) : Nat :=
  w.foldr (fun e A => mulP (sym.getD e oneP) A) oneP

@[expose] def sweepK (O : Nat) (P : List Nat) (key : Nat) (F : List N3) (fr : List Nat) : Bool :=
  ((O ^^^ neqL O F fr) &&& (O ^^^ maskOf P)) == 0 && minS (planes F) O 0 == key

@[expose] def fBoth (CR : List (List N3)) (W1 W2 : List N3) (R : List (List Nat)) : List N3 :=
  fLanes CR W1 R ++ fLanes CR W2 R

@[expose] def rootR (k Vm N O gx gy : Nat) (S S' : List Nat) (CR : List (List N3))
    (W1 W2 : List N3) (D D' r : Nat) (rt : List Nat × List Nat × Nat × List Nat × List Nat) :
    Bool :=
  mulP D D' == oneP && strictL rt.2.1 && rt.2.1.all (fun p => decide (p < N)) &&
  sweepK O rt.2.1 rt.2.2.1 (fBoth CR W1 W2 (rowsP r)) (colsP (mulP r Vm)) &&
  (r == k || r == mulP k k ||
    (rt.2.2.2.1.all (fun e => decide (e < 8)) && rt.2.2.2.2.all (fun e => decide (e < 8)) &&
      evalW (S ++ [D] ++ S' ++ [D']) rt.2.2.2.1 == gx &&
      evalW (S ++ [D] ++ S' ++ [D']) rt.2.2.2.2 == gy))

@[expose] def rootD (ls : List Nat) (k Vm N O gx gy : Nat) (S S' : List Nat)
    (CR : List (List N3)) (W1 W2 : List N3) (D D' : Nat)
    (rt : List Nat × List Nat × Nat × List Nat × List Nat) : Bool :=
  rootR k Vm N O gx gy S S' CR W1 W2 D D' (mulP (mulP D k) D') rt

@[expose] def rootK (ls : List Nat) (k Vm N O gx gy : Nat) (S S' : List Nat)
    (CR : List (List N3)) (W1 W2 : List N3)
    (rt : List Nat × List Nat × Nat × List Nat × List Nat) : Bool :=
  rootD ls k Vm N O gx gy S S' CR W1 W2 (wordP ls rt.1) (wordP ls rt.1.reverse) rt

@[expose] def rootsOK (ls : List Nat) (k Vm N gx gy : Nat) (S S' : List Nat)
    (CR : List (List N3)) (W1 W2 : List N3)
    (roots : List (List Nat × List Nat × Nat × List Nat × List Nat)) (j : Nat) : Bool :=
  ((roots.drop (16 * j)).take 16).all
    (rootK ls k Vm N (((1 <<< N) - 1) <<< 64) gx gy S S' CR W1 W2)

@[expose] def classOK (k n N : Nat) (S S' : List Nat)
    (roots : List (List Nat × List Nat × Nat × List Nat × List Nat)) : Bool :=
  S.length == 3 && S'.length == 3 && S.all (commP k) &&
  (List.zip S S').all (fun q => mulP q.1 q.2 == oneP) && strictL (roots.map fun rt => rt.2.2.1) &&
  (roots.map fun rt => N / rt.2.1.length).sum == n &&
  roots.all fun rt => N % rt.2.1.length == 0

@[expose] def xyOK (ls : List Nat) (gx gy gx' gy' : Nat) (ws : List (List Nat)) : Bool :=
  mulP gx gx' == oneP && mulP gy gy' == oneP && ws.length == 18 &&
  ((List.range 18).zip ws).all fun q =>
    q.2.all (fun e => decide (e < 4)) && evalW [gx, gy, gx', gy'] q.2 == letP ls q.1

end CFSG.KC.D42Cls

end
