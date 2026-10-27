module

public import CFSG.Certificates.Kernel.Common.Loop

public section

namespace CFSG.KC.Co1RankCoord

open CFSG.KC.Loop

@[expose] noncomputable def mask (n : Nat) : Nat := Nat.sub (Nat.shiftLeft 1 n) 1

@[expose] noncomputable def strictB (y : Nat) (k : Nat → Bool) : Bool :=
  Nat.rec (motive := fun _ => Bool) (k 0) (fun n _ => k (Nat.succ n)) y

structure Dat where
  d : Nat
  Kt : Nat
  NCt : Nat
  PHt : Nat
  T2A : Nat
  reps : List (List Nat × List (Nat × Nat × List Nat × List Nat))

@[expose] noncomputable def getL (L : List Nat) (k : Nat) : Nat :=
  List.rec (motive := fun _ => Nat → Nat) (fun _ => 0)
    (fun a _ ih k => Nat.rec (motive := fun _ => Nat) a (fun k' _ => ih k') k) L k

@[expose] noncomputable def lenL (L : List Nat) : Nat :=
  List.rec (motive := fun _ => Nat) 0 (fun _ _ ih => Nat.succ ih) L

@[expose] noncomputable def phi (d PH i b : Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat) 0 (fun s acc =>
    nIf(Nat.beq (Nat.land (Nat.shiftRight b s) 1) 1,
      Nat.xor acc (fld(PH, Nat.mul d (Nat.add (Nat.mul d i) s), mask d)), acc)) d

@[expose] noncomputable def kt (KT i j : Nat) : Nat := fld(KT, Nat.mul 7 (Nat.add (Nat.mul 128 i) j), 127)

@[expose] noncomputable def nc (d NC i j : Nat) : Nat :=
  fld(NC, Nat.mul d (Nat.add (Nat.mul 128 i) j), mask d)

@[expose] noncomputable def mulC (D : Dat) (x y : Nat) : Nat :=
  strictN (Nat.shiftRight x D.d) fun i => strictN (Nat.shiftRight y D.d) fun j =>
  Nat.lor (Nat.shiftLeft (kt D.Kt i j) D.d)
    (Nat.xor (Nat.xor (Nat.land x (mask D.d)) (phi D.d D.PHt i (Nat.land y (mask D.d))))
      (nc D.d D.NCt i j))

@[expose] noncomputable def dbl (D : Dat) (g : Nat) (L : List Nat) : List Nat :=
  List.rec (motive := fun _ => List Nat → List Nat) (fun T => T)
    (fun a _ ih T => List.cons a (ih T)) L
    (List.rec (motive := fun _ => List Nat) [] (fun a _ ih => List.cons (mulC D a g) ih) L)

@[expose] noncomputable def spanL (D : Dat) (gs : List Nat) : List Nat :=
  List.rec (motive := fun _ => List Nat → List Nat) (fun acc => acc)
    (fun g _ ih acc => ih (dbl D g acc)) gs [0]

@[expose] noncomputable def rankRC (r W A : Nat) : Nat :=
  strictN (mask W) fun F => strictN (Nat.div (mask (Nat.mul r W)) F) fun R =>
  Nat.rec (motive := fun _ => Nat → Nat → Nat) (fun _ r => r)
    (fun k ih A r => strictN (Nat.land (Nat.shiftRight A k) R) fun C =>
      Bool.rec (motive := fun _ => Nat)
        (strictN (Nat.xor C (Nat.land C (Nat.sub C 1))) fun lo =>
          strictN (Nat.land (Nat.div A lo) F) fun m =>
          strictN (Nat.xor A (Nat.mul C m)) fun A' => ih A' (Nat.succ r))
        (ih A r) (Nat.beq C 0)) W A 0

@[expose] noncomputable def lhs (D : Dat) (j : Nat) (gs : List Nat) (u : Nat) : Nat :=
  Nat.lor (Nat.xor u (phi D.d D.PHt j u))
    (Nat.shiftLeft (List.rec (motive := fun _ => Nat) 0 (fun x _ ih =>
      Nat.lor (Nat.xor u (phi D.d D.PHt (Nat.shiftRight x D.d) u)) (Nat.shiftLeft ih D.d)) gs) D.d)

@[expose] noncomputable def rhs (D : Dat) (j : Nat) (gs : List Nat) : Nat :=
  Nat.lor (nc D.d D.NCt j j)
    (Nat.shiftLeft (List.rec (motive := fun _ => Nat) 0 (fun x _ ih =>
      strictN (Nat.shiftRight x D.d) fun i => strictN (Nat.land x (mask D.d)) fun v =>
      Nat.lor (Nat.xor (Nat.xor v (phi D.d D.PHt j v)) (Nat.xor (nc D.d D.NCt j i) (nc D.d D.NCt i j)))
        (Nat.shiftLeft ih D.d)) gs) D.d)

@[expose] noncomputable def rowsF (D : Dat) (j : Nat) (gs : List Nat) (W : Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat) 0 (fun s acc =>
    Nat.lor acc (Nat.shiftLeft (lhs D j gs (Nat.shiftLeft 1 s)) (Nat.mul W s))) D.d

@[expose] noncomputable def packL (W : Nat) (L : List Nat) : Nat :=
  List.rec (motive := fun _ => Nat) 0 (fun a _ ih => Nat.lor a (Nat.shiftLeft ih W)) L

@[expose] noncomputable def spanK (K : List Nat) (q0 idx : Nat) : Nat :=
  List.rec (motive := fun _ => Nat → Nat → Nat) (fun acc _ => acc)
    (fun k _ ih acc idx => ih (nIf(Nat.beq (Nat.land idx 1) 1, Nat.xor acc k, acc))
      (Nat.shiftRight idx 1)) K q0 idx

@[expose] noncomputable def codeOK (D : Dat) (El : List Nat) (nE y c : Nat) : Bool :=
  bIf(Nat.blt c nE, Nat.beq (getL El c) y,
    Nat.beq (fld(D.T2A, mulC D (getL El (Nat.sub c nE)) y, 1)) 1)

@[expose] noncomputable def codesOK (D : Dat) (El : List Nat) (nE j : Nat) (K : List Nat) (q0 : Nat)
    (cs : List Nat) : Bool :=
  List.rec (motive := fun _ => Nat → Bool)
    (fun idx => Nat.beq idx (Nat.shiftLeft 1 (lenL K)))
    (fun c _ ih idx => bAnd(codeOK D El nE (Nat.lor (Nat.shiftLeft j D.d) (spanK K q0 idx)) c,
      ih (Nat.succ idx))) cs 0

@[expose] noncomputable def entryOK (D : Dat) (gs El : List Nat) (nE j : Nat)
    (e : Nat × Nat × List Nat × List Nat) : Bool :=
  Prod.rec (motive := fun _ => Bool) (fun mode r => Prod.rec (motive := fun _ => Bool) (fun a r =>
    Prod.rec (motive := fun _ => Bool) (fun K cs =>
      bIf(Nat.beq mode 3, bIf(Nat.beq (kt D.Kt j j) 0, false, true),
      bIf(Nat.beq mode 0,
        strictB (Nat.shiftRight (getL gs a) D.d) fun i =>
          bIf(Nat.beq (kt D.Kt i j) (kt D.Kt j i), false, Nat.blt a (lenL gs)),
      bAnd(Nat.beq (kt D.Kt j j) 0,
      strictB (Nat.mul D.d (Nat.succ (lenL gs))) fun W =>
      strictB (rowsF D j gs W) fun A =>
      strictB (rhs D j gs) fun B =>
      strictB (rankRC D.d W A) fun rk =>
      bIf(Nat.beq mode 2,
        Nat.beq (rankRC (Nat.succ D.d) W (Nat.lor A (Nat.shiftLeft B (Nat.mul W D.d)))) (Nat.succ rk),
      bAnd(Nat.beq mode 1,
      bAnd(Nat.beq (lhs D j gs a) B,
      bAnd(List.rec (motive := fun _ => Bool) true (fun k _ ih => bAnd(Nat.beq (lhs D j gs k) 0, ih)) K,
      bAnd(Nat.beq (Nat.add rk (lenL K)) D.d,
      bAnd(Nat.beq (rankRC (lenL K) D.d (packL D.d K)) (lenL K),
        codesOK D El nE j K a cs)))))))))) r) r) e

@[expose] noncomputable def entriesOK (D : Dat) (gs El : List Nat) (nE : Nat)
    (es : List (Nat × Nat × List Nat × List Nat)) : Bool :=
  List.rec (motive := fun _ => Nat → Bool) (fun j => Nat.beq j 128)
    (fun e _ ih j => bAnd(entryOK D gs El nE j e, ih (Nat.succ j))) es 0

@[expose] noncomputable def chk (D : Dat) : Bool :=
  List.rec (motive := fun _ => Bool) true (fun p _ ih =>
    Prod.rec (motive := fun _ => Bool) (fun gs es =>
      bAnd((fun El => entriesOK D gs El (lenL El) es) (spanL D gs), ih)) p) D.reps

end CFSG.KC.Co1RankCoord

end
