module

public import CFSG.Certificates.Kernel.Common.Loop
public import Certificates.Data.RouteP.M24Defect

public section

namespace CFSG.KC.M24Def

open CFSG.KC.Loop

@[expose] noncomputable def ln (w P j : Nat) : Nat :=
  Nat.land (Nat.shiftRight P (Nat.mul w j)) (Nat.sub (Nat.shiftLeft 1 w) 1)

@[expose] noncomputable def strictB (y : Nat) (k : Nat → Bool) : Bool :=
  Nat.rec (motive := fun _ => Bool) (k 0) (fun n _ => k (Nat.succ n)) y

@[expose] noncomputable def strictP (y : Nat) (k : Nat → Nat × Nat) : Nat × Nat :=
  Nat.rec (motive := fun _ => Nat × Nat) (k 0) (fun n _ => k (Nat.succ n)) y

@[expose] noncomputable def allLt (n : Nat) (f : Nat → Bool) : Bool :=
  Nat.rec (motive := fun _ => Bool) true (fun j ih => bAnd(f j, ih)) n

@[expose] noncomputable def dapp (D m : Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat) 0 (fun j acc =>
    Bool.rec (motive := fun _ => Nat) acc (Nat.xor acc (ln 11 D j))
      (Nat.blt 0 (Nat.land m (Nat.shiftLeft 1 j)))) 11

section Walk

variable (LD LI GQ : Nat → Nat)

@[expose] noncomputable def emit (x S : Nat) : Nat :=
  strictN (Nat.land S 2097151) fun sm =>
    strictN (Nat.add (Nat.mul 24 (Nat.land sm 31)) (Nat.land (Nat.shiftRight sm 5) 31)) fun q =>
      strictN (dapp (GQ q) (Nat.shiftRight sm 10)) fun cov =>
        Nat.xor S (Nat.shiftLeft cov (Nat.add 21 (Nat.mul 11 (Nat.add (Nat.mul 2 q) x))))

@[expose] noncomputable def move (code S : Nat) : Nat :=
  strictN (Nat.land S 2097151) fun sm =>
    strictN (ln 5 (LI code) (Nat.land sm 31)) fun u =>
      strictN (ln 5 (LI code) (Nat.land (Nat.shiftRight sm 5) 31)) fun v =>
        strictN (dapp (LD code) (Nat.shiftRight sm 10)) fun c =>
          Nat.add (Nat.sub S sm) (Nat.add u (Nat.add (Nat.mul 32 v) (Nat.mul 1024 c)))

@[expose] noncomputable def letK (code S : Nat) : Nat :=
  Bool.rec (motive := fun _ => Nat) (emit GQ (Nat.shiftRight code 1) (move LD LI code S))
    (move LD LI code (emit GQ (Nat.shiftRight code 1) S)) (Nat.beq (Nat.land code 1) 0)

@[expose] noncomputable def walkK (W S : Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat → Nat) (fun S => S)
    (fun k ih S => strictN (letK LD LI GQ (ln 6 W (Nat.sub (ln 6 W 0) k)) S) ih) (ln 6 W 0) S

variable (FP RW : Nat → Nat)

@[expose] noncomputable def entK (e A : Nat) : Nat :=
  strictN (Nat.land e 1023) fun p => strictN (Nat.land (Nat.shiftRight e 10) 7) fun i =>
    strictN (dapp (FP p) (Nat.shiftRight e 13)) fun c0 =>
      Nat.shiftRight (walkK LD LI GQ (RW i) (Nat.add (Nat.shiftLeft A 21)
        (Nat.add (Nat.div p 24) (Nat.add (Nat.mul 32 (Nat.mod p 24)) (Nat.mul 1024 c0))))) 21

@[expose] noncomputable def runE (C lo len A : Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat → Nat) (fun A => A)
    (fun k ih A => strictN (entK LD LI GQ FP RW (ln 24 C (Nat.sub (Nat.add lo len) k)) A) ih)
    len A

@[expose] noncomputable def comboK (C : Nat) : Bool :=
  Nat.beq (runE LD LI GQ FP RW C 0 (ln 24 C 0) 0) 0

end Walk

@[expose] noncomputable def lanesIs (D : Nat) (f : Nat → Nat) : Bool :=
  allLt 11 fun j => Nat.beq (ln 11 D j) (f j)

@[expose] noncomputable def isId (D : Nat) : Bool := lanesIs D fun j => Nat.shiftLeft 1 j

@[expose] noncomputable def treeQ (TW PA GQ FP LD LI : Nat → Nat) (q : Nat) : Bool :=
  strictB (Nat.div q 24) fun u => strictB (Nat.mod q 24) fun v =>
  bIf(Nat.beq u v, true,
    strictB (TW q) fun t =>
    bIf(Nat.beq (Nat.land t 31) 0, bAnd(Nat.beq q 1, bAnd(isId (GQ q), isId (FP q))),
      strictB (PA q) fun p => strictB (TW p) fun tp =>
      strictB (Nat.land (Nat.shiftRight t (Nat.add (Nat.land tp 31) 5)) 1) fun x =>
      bAnd(Nat.blt p 576,
      bAnd(bIf(Nat.beq (Nat.div p 24) (Nat.mod p 24), false, true),
      bAnd(Nat.beq t (Nat.add (Nat.add tp 1) (Nat.shiftLeft x (Nat.add (Nat.land tp 31) 5))),
      bAnd(Nat.beq (ln 5 (LI (Nat.mul 2 x)) (Nat.div p 24)) u,
      bAnd(Nat.beq (ln 5 (LI (Nat.mul 2 x)) (Nat.mod p 24)) v,
      bAnd(lanesIs (FP q) (fun j => dapp (LD (Nat.mul 2 x)) (ln 11 (FP p) j)),
        lanesIs (GQ q) (fun j => dapp (GQ p) (ln 11 (LD (Nat.add (Nat.mul 2 x) 1)) j))))))))))

@[expose] noncomputable def relPt (LI : Nat → Nat) (W k : Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat) k
    (fun j acc => ln 5 (LI (Nat.xor (ln 6 W (Nat.sub (ln 6 W 0) j)) 1)) acc) (ln 6 W 0)

@[expose] noncomputable def relQ (LI : Nat → Nat) (W : Nat) : Bool :=
  allLt 24 fun k => Nat.beq (relPt LI W k) k

@[expose] noncomputable def runF (FP : Nat → Nat) (C lo len : Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat)  0
    (fun k acc => strictN (ln 24 C (Nat.add lo k)) fun e =>
      Nat.xor acc (Nat.shiftLeft (dapp (FP (Nat.land e 1023)) (Nat.shiftRight e 13))
        (Nat.mul 11 (Nat.land (Nat.shiftRight e 10) 7)))) len

@[expose] noncomputable def fsQ (FP : Nat → Nat) (C F : Nat) : Bool :=
  Nat.beq (runF FP C 1 (ln 24 C 0)) F

@[expose] noncomputable def lamStep (LM : Nat → Nat) (code : Nat) (MA : Nat × Nat) : Nat × Nat :=
  Prod.rec (motive := fun _ => Nat × Nat) (fun M A =>
    strictP M fun M => strictP A fun A =>
    Bool.rec (motive := fun _ => Nat × Nat)
      (strictP (Nat.rec (motive := fun _ => Nat) 0 (fun j acc =>
          Nat.lor acc (Nat.shiftLeft (dapp M (ln 11 (LM code) j)) (Nat.mul 11 j))) 11) fun M' =>
        (M', Nat.xor A (Nat.shiftLeft M' (Nat.mul 121 (Nat.shiftRight code 1)))))
      (strictP (Nat.rec (motive := fun _ => Nat) 0 (fun j acc =>
          Nat.lor acc (Nat.shiftLeft (dapp M (ln 11 (LM code) j)) (Nat.mul 11 j))) 11) fun M' =>
        (M', Nat.xor A (Nat.shiftLeft M (Nat.mul 121 (Nat.shiftRight code 1)))))
      (Nat.beq (Nat.land code 1) 0)) MA

@[expose] noncomputable def idCols : Nat :=
  Nat.rec (motive := fun _ => Nat) 0 (fun j acc => Nat.lor acc (Nat.shiftLeft 1 (Nat.mul 12 j))) 11

@[expose] noncomputable def lamOf (LM : Nat → Nat) (W : Nat) : Nat :=
  Prod.rec (motive := fun _ => Nat) (fun _ A => A)
    (Nat.rec (motive := fun _ => Nat × Nat) (idCols, 0)
      (fun j acc => lamStep LM (ln 6 W (Nat.add j 1)) acc) (ln 6 W 0))

@[expose] noncomputable def lamK (L z : Nat) : Nat :=
  Nat.xor (dapp L (Nat.land z 2047)) (dapp (Nat.shiftRight L 121) (Nat.shiftRight z 11))

@[expose] noncomputable def bezQ (LA FS SD TD : Nat → Nat) (κ i : Nat) : Bool :=
  Nat.beq (Nat.xor (lamK (LA i) (SD κ))
      (Nat.rec (motive := fun _ => Nat) 0 (fun r acc =>
        Bool.rec (motive := fun _ => Nat) acc (Nat.xor acc (ln 11 (TD r) i))
          (Nat.blt 0 (Nat.land (FS r) (Nat.shiftLeft 1 κ)))) 67))
    (Bool.rec (motive := fun _ => Nat) 0 (Nat.shiftLeft 1 (Nat.mod κ 11))
      (Nat.beq (Nat.div κ 11) i))

@[expose] def decW (t : Nat) : List (Nat × Bool) :=
  (List.range (t % 32)).map fun k => ((t / 32 / 2 ^ k) % 2, true)

@[expose] def tabOf (TW : Nat → Nat) : Array (List (Nat × Bool)) :=
  ((List.range 576).map fun q => decW (TW q)).toArray

@[expose] def decC (C : Nat) : List (Nat × Nat × Nat) :=
  (List.range (C % 2 ^ 24)).map fun k =>
    let e := C / 2 ^ (24 * (k + 1)) % 2 ^ 24
    (e % 1024, e / 1024 % 8, e / 8192)

@[expose] def csOf (CB : Nat → Nat) : List (List (Nat × Nat × Nat)) :=
  (List.range 67).map fun r => decC (CB r)

@[expose] def sOf (SD : Nat → Nat) : List (Nat × Nat) :=
  (List.range 77).map fun k => (SD k % 2048, SD k / 2048)

@[expose] def tOf (TD : Nat → Nat) : List (List Nat) :=
  (List.range 67).map fun r => (List.range 7).map fun i => TD r / 2 ^ (11 * i) % 2048

@[expose] def decR (W : Nat) : List (Nat × Bool) :=
  (List.range (W % 64)).map fun k =>
    let c := W / 2 ^ (6 * (k + 1)) % 64
    (c / 2, c % 2 == 0)

open Certificates.RouteP.M24Defect CFSG.Quasithin.H.Mathieu

@[expose] noncomputable def lettersTabOK (LI LD LM : Nat → Nat) : Bool :=
  (List.range 4).all fun c =>
    ((List.range 24).all fun k => ln 5 (LI c) k == (letArr (c / 2) (c % 2 != 0))[k]!) &&
    ((List.range 11).all fun j => ln 11 (LD c) j == dualAct (matA (letArr (c / 2) (c % 2 == 0))) (2 ^ j)) &&
    ((List.range 11).all fun j => ln 11 (LM c) j == act11 (letArr (c / 2) (c % 2 == 0)) (2 ^ j))

end CFSG.KC.M24Def

end
