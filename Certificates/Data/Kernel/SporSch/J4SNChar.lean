module

public import Certificates.Data.Kernel.SporSch.J4SCols

public section

namespace CFSG.KS.SporSch.C11

open CFSG.KC.Enum CFSG.KS

@[expose] noncomputable def quadK (P Q v : Nat) : Bool :=
  strictB (Nat.xor (appK Q v) v) (fun x => Nat.beq (Nat.xor (appK P x) x) (nat_lit 0))

@[expose] noncomputable def t1 (t : Nat × Nat × Nat) : Nat :=
  Prod.rec (motive := fun _ => Nat) (fun a _ => a) t

@[expose] noncomputable def t2 (t : Nat × Nat × Nat) : Nat :=
  Prod.rec (motive := fun _ => Nat) (fun _ q => Prod.rec (motive := fun _ => Nat) (fun b _ => b) q) t

@[expose] noncomputable def t3 (t : Nat × Nat × Nat) : Nat :=
  Prod.rec (motive := fun _ => Nat) (fun _ q => Prod.rec (motive := fun _ => Nat) (fun _ c => c) q) t

@[expose] noncomputable def nthT (L : List (Nat × Nat × Nat)) : Nat → Nat × Nat × Nat :=
  List.rec (motive := fun _ => Nat → Nat × Nat × Nat) (fun _ => (0, 0, 0))
    (fun x _ ih k => Nat.rec (motive := fun _ => Nat × Nat × Nat) x (fun k' _ => ih k') k) L

@[expose] noncomputable def lenT (L : List (Nat × Nat × Nat)) : Nat :=
  List.rec (motive := fun _ => Nat) (nat_lit 0) (fun _ _ ih => Nat.succ ih) L

@[expose] noncomputable def forestK (CJ : Nat → Nat) (L : List (Nat × Nat × Nat)) : Bool :=
  bAnd(Nat.blt (nat_lit 0) (lenT L),
    allN (lenT L) (fun k => strictB (t1 (nthT L k)) (fun x => bAnd(Nat.blt x (nat_lit 1024),
      bIf(Nat.beq k (nat_lit 0), true,
        strictB (t2 (nthT L k)) (fun p => strictB (t3 (nthT L k)) (fun g =>
          bAnd(Nat.blt p k, bAnd(Nat.blt g (nat_lit 4),
            Nat.beq x (ent (nat_lit 10) (CJ g) (t1 (nthT L p))))))))))))

@[expose] noncomputable def k3K (L : List (Nat × Nat × Nat)) : Bool :=
  List.rec (motive := fun _ => Bool) true (fun x _ ih => strictB (t1 x) (fun e =>
    bAnd(bIf(Nat.beq e (nat_lit 118), true, bIf(Nat.beq e (nat_lit 448), true,
      Nat.beq e (nat_lit 502))), ih))) L

@[expose] noncomputable def witK (E : Nat → Nat) (L : List (Nat × Nat × Nat))
    (w : Option (Nat × Nat × Nat)) : Bool :=
  Option.rec (motive := fun _ => Bool) (k3K L) (fun t =>
    strictB (t1 t) (fun a => strictB (t2 t) (fun b => strictB (t3 t) (fun v =>
      bAnd(Nat.blt a (lenT L), bAnd(Nat.blt b (lenT L), bAnd(Nat.blt v (nat_lit 2048),
      strictB (t1 (nthT L a)) (fun ea => strictB (t1 (nthT L b)) (fun eb =>
        bAnd(Nat.blt ea (nat_lit 1024), bAnd(Nat.blt eb (nat_lit 1024),
          Bool.not (quadK (E ea) (E eb) v)))))))))))) w

@[expose] noncomputable def memK (e : Nat) (LL : List (List (Nat × Nat × Nat))) : Bool :=
  List.rec (motive := fun _ => Bool) false (fun L _ ih =>
    bIf(List.rec (motive := fun _ => Bool) false (fun x _ ih2 => bIf(Nat.beq (t1 x) e, true, ih2))
      L, true, ih)) LL

@[expose] noncomputable def coverK (E : Nat → Nat) (LL : List (List (Nat × Nat × Nat))) : Bool :=
  allN (nat_lit 1024) (fun e => bIf(Nat.beq e (nat_lit 0), true, bIf(memK e LL, true,
    Bool.not (allN (nat_lit 2048) (fun v => quadK (E e) (E e) v)))))

@[expose] noncomputable def k4 (a : Nat) : Nat :=
  nIf(Nat.beq a (nat_lit 0), nat_lit 0, nIf(Nat.beq a (nat_lit 1), nat_lit 118,
    nIf(Nat.beq a (nat_lit 2), nat_lit 448, nat_lit 502)))

@[expose] noncomputable def fix2CntK (P Q : Nat) : Nat :=
  foldN (nat_lit 2048) (fun a s => nIf(bAnd(Nat.beq (appK P a) a, Nat.beq (appK Q a) a),
    Nat.succ s, s)) (nat_lit 0)

end CFSG.KS.SporSch.C11

end
