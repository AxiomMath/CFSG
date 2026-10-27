module

public import Certificates.Data.GGWitExcModel
public import Certificates.Data.Kernel.TWLK6

public section

namespace Certificates.WEMK

open Certificates.ExcModel Certificates.TWLK

abbrev NMat := List (List Nat)

abbrev KPair := List Nat × List Nat

@[expose] def kP0 : KPair := ([], [])

@[expose] def ndot : List Nat → List Nat → Nat
  | a :: l, b :: m => a * b + ndot l m
  | _, _ => 0

@[expose] def nlin (n : Nat) : List Nat → NMat → List Nat
  | a :: l, b :: m => List.zipWith (fun x y => a * x + y) b (nlin n l m)
  | _, _ => List.replicate n 0

@[expose] def nmv (A : NMat) (v : List Nat) : List Nat := A.map fun r => ndot r v % 13

@[expose] def nvm (n : Nat) (v : List Nat) (A : NMat) : List Nat := (nlin n v A).map (· % 13)

@[expose] def nmul (n : Nat) (A B : NMat) : NMat := A.map fun r => nvm n r B

@[expose] def idN (n : Nat) : NMat := (List.range n).map fun r => (List.range n).map fun c => if r = c then 1 else 0

@[expose] def isOneN (n : Nat) (A : NMat) : Bool := decide (A = idN n)

@[expose] def mat (n : Nat) (q : KPair) : NMat :=
  (List.range n).map fun r => (List.range n).map fun c =>
    ((if r = c then 1 else 0) + 13 - q.1.getD r 0 * q.2.getD c 0 % 13) % 13

@[expose] def wfM (n : Nat) (A : NMat) : Bool := decide (A.length = n) && A.all fun r => decide (r.length = n)

@[expose] def fnz : List Nat → Nat
  | [] => 0
  | x :: l => if x % 13 = 0 then fnz l else x % 13

@[expose] def ninv (x : Nat) : Nat := [0, 1, 7, 9, 10, 8, 11, 2, 5, 3, 4, 6, 12].getD (x % 13) 0

@[expose] def normP (q : KPair) : KPair :=
  (q.1.map (· * ninv (fnz q.1) % 13), q.2.map (· * fnz q.1 % 13))

@[expose] def conjP (n : Nat) (s : NMat) (q : KPair) : KPair := normP (nmv s q.1, nvm n q.2 s)

@[expose] def kTab (n : Nat) (S : List NMat) (V : List KPair) (tab : List (List Nat)) : Bool :=
  decide (tab.length = V.length) &&
  (List.range V.length).all fun i =>
    decide ((tab.getD i []).length = S.length) &&
    (List.range S.length).all fun s =>
      decide ((tab.getD i []).getD s 0 < V.length) &&
      decide ((tab.getD ((tab.getD i []).getD s 0) []).getD s 0 = i) &&
      (!decide (i ≤ (tab.getD i []).getD s 0) ||
        decide (conjP n (S.getD s []) (V.getD i kP0) = V.getD ((tab.getD i []).getD s 0) kP0))

@[expose] def kPar (S : List NMat) (V : List KPair) (tab : List (List Nat)) (par : List (Nat × Nat)) : Bool :=
  (List.range V.length).all fun i => decide (i = 0) ||
    (decide ((par.getD i (0, 0)).1 < i) && decide ((par.getD i (0, 0)).2 < S.length) &&
      decide ((tab.getD (par.getD i (0, 0)).1 []).getD (par.getD i (0, 0)).2 0 = i))

@[expose] def walk (tab : List (List Nat)) (u : Nat × Nat) (w : List Nat) : Nat × Nat :=
  w.foldl (fun u s => ((tab.getD u.1 []).getD s 0, (tab.getD u.2 []).getD s 0)) u

@[expose] def a2N (n : Nat) (A B : NMat) : Bool :=
  !isOneN n (nmul n A B) && isOneN n (nmul n (nmul n (nmul n A B) (nmul n A B)) (nmul n A B))

@[expose] def kWit (n : Nat) (S : List NMat) (V : List KPair) (tab : List (List Nat)) (wd : List (List Nat))
    (x0 : Nat) : Bool :=
  decide (x0 < V.length) &&
  (List.range V.length).all fun i =>
    !a2N n (mat n (V.getD 0 kP0)) (mat n (V.getD i kP0)) ||
      ((wd.getD i []).all (fun s => decide (s < S.length)) && decide (walk tab (0, x0) (wd.getD i []) = (0, i)))

@[expose] def kReplay (n : Nat) (G : List NMat) (tr : List (Nat × Nat)) : List NMat :=
  tr.foldl (fun E e => E ++ [nmul n (E.getD e.1 (idN n)) (G.getD e.2 (idN n))]) [idN n]

@[expose] def kBig (n : Nat) (V : List KPair) (x0 t0 : Nat) (tr : List (Nat × Nat)) (ord : List Nat) : Bool :=
  decide (t0 < V.length) &&
  !(decide (nmul n (mat n (V.getD t0 kP0)) (mat n (V.getD 0 kP0)) =
      nmul n (mat n (V.getD 0 kP0)) (mat n (V.getD t0 kP0))) &&
    decide (nmul n (mat n (V.getD t0 kP0)) (mat n (V.getD x0 kP0)) =
      nmul n (mat n (V.getD x0 kP0)) (mat n (V.getD t0 kP0)))) &&
  decide (ord.length = 49) &&
  kIncr (ord.map fun k =>
    kVKey 13 ((kReplay n [mat n (V.getD 0 kP0), mat n (V.getD x0 kP0), mat n (V.getD t0 kP0)] tr).getD k (idN n)))

@[expose] def kCore (n : Nat) (S : List NMat) (V : List KPair) (tab : List (List Nat)) (par : List (Nat × Nat))
    (wd : List (List Nat)) (x0 t0 : Nat) (tr : List (Nat × Nat)) (ord : List Nat) : Bool :=
  S.all (wfM n) && S.all (fun s => isOneN n (nmul n s s)) && decide (0 < V.length) &&
  decide (mat n (V.getD 0 kP0) = S.getD 0 []) &&
  kTab n S V tab && kPar S V tab par && kWit n S V tab wd x0 && kBig n V x0 t0 tr ord

@[expose] def toN {n : Nat} (A : M13 n) : NMat := List.ofFn fun i : Fin n => List.ofFn fun j : Fin n => (A.val i j).val

@[expose] def kCovN (n : Nat) (S G : List NMat) (V : List KPair) (cov : List Nat) : Bool :=
  decide (S = G) && decide (cov.length = S.length) &&
  (List.range S.length).all fun j =>
    decide (cov.getD j 0 < V.length) && decide (mat n (V.getD (cov.getD j 0) kP0) = S.getD j [])

@[expose] def pairN (w : (Fin 6 → ZMod 13) × (Fin 6 → ZMod 13)) : KPair :=
  (List.ofFn fun i => (w.1 i).val, List.ofFn fun i => (w.2 i).val)

@[expose] def ct6N (_ : Unit := ()) : List KPair := (ctList ()).map pairN

@[expose] def ct5N (_ : Unit := ()) : List KPair :=
  ((ctList ()).filter fun w => decide (w.1 0 - w.1 1 = 0)).map pairN

@[expose] def rootP (q : KPair) : KPair := normP (q.1.map (· * (2 * ninv (ndot q.1 q.2) % 13) % 13), q.2)

@[expose] def kCovK (n : Nat) (S : List NMat) (roots V : List KPair) (cov sidx : List Nat) : Bool :=
  decide (cov.length = roots.length) &&
  (List.range roots.length).all (fun j =>
    decide (cov.getD j 0 < V.length) && decide (rootP (roots.getD j kP0) = V.getD (cov.getD j 0) kP0)) &&
  decide (sidx.length = S.length) &&
  (List.range S.length).all fun j =>
    decide (sidx.getD j 0 < roots.length) && decide (S.getD j [] = mat n (V.getD (cov.getD (sidx.getD j 0) 0) kP0))

end Certificates.WEMK

end
