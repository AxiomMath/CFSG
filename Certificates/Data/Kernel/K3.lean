module

public import Certificates.Data.Kernel.Spor.Raw
public import Certificates.Data.Kernel.Spor.Prim
public import Certificates.Data.Kernel.Child3
public import Certificates.Data.Kernel.SurjK

public section

namespace CFSG.KC.K3

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Prim

structure K3C where
  n : Nat
  w : Nat
  R : Nat
  g : Nat
  N : Nat
  OP : Nat → Nat
  A1 : Nat → Nat
  A2 : Nat → Nat
  A3 : Nat → Nat
  W : Nat → Nat
  S1 : Nat → Nat
  S2 : Nat → Nat
  FR : Nat → Nat
  GP : Nat → Nat
  sy : Nat
  SY : Nat → Nat
  AI : Nat → Nat
  ord : Nat
  E : Nat → Nat
  EP : Nat → Nat
  EL : Nat → Nat
  EK : Nat → Nat
  EKI : Nat → Nat
  ES : Nat → Nat
  ESI : Nat → Nat
  NC : Nat
  CS : List Nat
  OFF : List Nat
  RE : List Nat
  CI : Nat → Nat
  CE : Nat → Nat
  CP : Nat → Nat
  CL : Nat → Nat
  CK : Nat → Nat
  CO : Nat → Nat
  COI : Nat → Nat
  MW : Nat → Nat
  nw : Nat
  WT : Nat → Nat
  WU : Nat → Nat
  WV : Nat → Nat

namespace K3C

variable (K : K3C)

@[expose] noncomputable def pc (p q : Nat) : Nat := pcomp K.n K.w (mask K.w) p q

@[expose] noncomputable def one : Nat := pidn K.n K.w

@[expose] noncomputable def can (p : Nat) : Bool := canonK K.n K.w (mask K.w) (Nat.mul K.n K.w) p

@[expose] noncomputable def pw (P : Nat) (e : Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat) K.one (fun _ acc => strictN acc fun a => K.pc P a) e

@[expose] noncomputable def hk (P : Nat) : Nat :=
  foldN K.n (fun i h => Nat.mod (Nat.mul (Nat.xor h (pg K.w (mask K.w) P (Nat.sub (Nat.sub K.n 1) i)))
    1099511628211) 18446744073709551616) 14695981039346656037

@[expose] noncomputable def tg (t : Nat) : Nat := nIf(Nat.beq (K.OP t) 1, K.A3 t, nIf(Nat.beq (K.OP t) 2, K.A2 t, K.A3 t))

@[expose] noncomputable def r1 (t : Nat) : Nat := nIf(Nat.beq (K.OP t) 1, K.A2 t, K.A1 t)

@[expose] noncomputable def val (v : Nat) : Nat :=
  nIf(Nat.blt v K.R, nIf(Nat.blt v K.g, K.GP v, K.one), K.W (Nat.sub v K.R))

@[expose] noncomputable def srcOK (r t s : Nat) : Bool :=
  bIf(Nat.blt s K.R,
    bAnd(Nat.beq s r, allN t fun v => bIf(Nat.beq (K.tg v) r, false, true)),
    strictB (Nat.sub s K.R) fun u => bAnd(Nat.blt u t, bAnd(Nat.beq (K.tg u) r,
      allN (Nat.sub (Nat.sub t u) 1) fun d => bIf(Nat.beq (K.tg (Nat.add (Nat.succ u) d)) r, false,
        true))))

@[expose] noncomputable def stepK (t : Nat) : Bool :=
  strictB (K.OP t) fun op =>
  bAnd(K.can (K.W t),
  bAnd(Nat.blt op 3,
  bAnd(Nat.blt (K.tg t) K.R, bAnd(Nat.blt (K.r1 t) K.R,
  bAnd(K.srcOK (K.r1 t) t (K.S1 t),
  bIf(Nat.beq op 0,
    bAnd(Nat.blt (K.A2 t) K.R, bAnd(K.srcOK (K.A2 t) t (K.S2 t),
      Nat.beq (K.W t) (K.pc (K.val (K.S1 t)) (K.val (K.S2 t))))),
  bIf(Nat.beq op 1, Nat.beq (K.W t) (K.pw (K.val (K.S1 t)) (K.A1 t)),
    permOK K.n K.w (mask K.w) (Nat.mul K.n K.w) (K.val (K.S1 t)) (K.W t))))))))

@[expose] noncomputable def finK (r : Nat) : Bool := K.srcOK r K.N (K.FR r)

@[expose] noncomputable def A (a : Nat) : Nat := K.val (K.FR (K.SY a))

@[expose] noncomputable def eK (k : Nat) : Bool :=
  strictB (K.E k) fun e =>
  bAnd(K.can e,
  bAnd(bIf(Nat.beq k 0, Nat.beq e K.one,
    bAnd(Nat.blt (K.EP k) k, bAnd(Nat.blt (K.EL k) K.sy,
      Nat.beq e (K.pc (K.E (K.EP k)) (K.A (K.EL k)))))),
  bAnd(bIf(Nat.beq k 0, true, bIf(Nat.blt (Nat.succ k) K.ord,
    lexLtK (K.EP k) (K.EL k) (K.EP (Nat.succ k)) (K.EL (Nat.succ k)), true)),
  bAnd(allN K.sy fun l => strictB (K.EK (Nat.add (Nat.mul K.sy k) l)) fun q =>
    bAnd(Nat.blt q K.ord, bAnd(Nat.beq (K.E q) (K.pc e (K.A l)),
      bIf(Nat.beq q 0, true, bIf(lexLtK k l (K.EP q) (K.EL q), false, true)))),
  bAnd(allN K.sy fun l => strictB (K.EKI (Nat.add (Nat.mul K.sy k) l)) fun q =>
    bAnd(Nat.blt q K.ord, Nat.beq (K.E q) (K.pc e (K.AI l))),
  bAnd(Nat.blt (K.ES k) K.ord, bAnd(Nat.blt (K.ESI k) K.ord, bAnd(Nat.beq (K.ES (K.ESI k)) k,
    bIf(Nat.blt (Nat.succ k) K.ord, Nat.blt (K.hk (K.E (K.ES k))) (K.hk (K.E (K.ES (Nat.succ k)))),
      true)))))))))

@[expose] noncomputable def cj (l Y : Nat) : Nat := K.pc (K.pc (K.A l) Y) (K.AI l)

@[expose] noncomputable def cK (p : Nat) : Bool :=
  strictB (K.CI p) fun c => strictB (lget K.OFF c) fun o => strictB (lget K.CS c) fun s =>
  strictB (Nat.sub p o) fun k => strictB (K.CE p) fun x =>
  bAnd(Nat.blt c K.CS.length, bAnd(Nat.ble o p, bAnd(Nat.blt k s, bAnd(K.can x,
  bAnd(bIf(Nat.beq k 0, Nat.beq x (K.E (lget K.RE c)),
    bAnd(Nat.blt (K.CP p) k, bAnd(Nat.blt (K.CL p) K.sy,
      Nat.beq x (K.cj (K.CL p) (K.CE (Nat.add o (K.CP p))))))),
  bAnd(bIf(Nat.beq k 0, true, bIf(Nat.blt (Nat.succ k) s,
    lexLtK (K.CP p) (K.CL p) (K.CP (Nat.succ p)) (K.CL (Nat.succ p)), true)),
  bAnd(allN K.sy fun l => strictB (K.CK (Nat.add (Nat.mul K.sy p) l)) fun q =>
    bAnd(Nat.blt q s, bAnd(Nat.beq (K.CE (Nat.add o q)) (K.cj l x),
      bIf(Nat.beq q 0, true, bIf(lexLtK k l (K.CP (Nat.add o q)) (K.CL (Nat.add o q)), false,
        true)))),
  bAnd(Nat.blt (K.CO p) K.NC, bAnd(Nat.blt (K.COI p) K.NC, bAnd(Nat.beq (K.CO (K.COI p)) p,
    bIf(Nat.blt (Nat.succ p) K.NC,
      Nat.blt (Nat.add (Nat.mul (K.CI (K.CO p)) 18446744073709551616) (K.hk (K.CE (K.CO p))))
        (Nat.add (Nat.mul (K.CI (K.CO (Nat.succ p))) 18446744073709551616)
          (K.hk (K.CE (K.CO (Nat.succ p))))), true)))))))))))

@[expose] noncomputable def memK (k : Nat) : Bool :=
  strictB (K.E k) fun e =>
  bIf(bAnd(bIf(Nat.beq e K.one, false, true), Nat.beq (K.pc e (K.pc e e)) K.one),
    strictB (Nat.div (K.MW k) 2) fun p => bAnd(Nat.blt p K.NC,
      bIf(Nat.beq (Nat.mod (K.MW k) 2) 0, Nat.beq (K.CE p) e, Nat.beq (K.CE p) (K.pc e e))),
    true)

@[expose] noncomputable def reg (r : Nat) : Nat := K.val (K.FR r)

@[expose] noncomputable def witK (j : Nat) : Bool :=
  strictB (K.E (lget K.RE j)) fun x =>
  bIf(Nat.beq (K.WT j) 0,
    strictB (K.reg (K.WU j)) fun u => bAnd(Nat.blt (K.WU j) K.R,
      bAnd(Nat.beq (K.pc u x) (K.pc x u), bAnd(bIf(Nat.beq (K.pc u u) K.one, false, true),
        Nat.beq (K.pw u 4) K.one))),
    strictB (K.reg (K.WU j)) fun u => strictB (K.reg (K.WV j)) fun v =>
    bAnd(Nat.blt (K.WU j) K.R, bAnd(Nat.blt (K.WV j) K.R,
    bAnd(Nat.beq (K.pc u u) K.one, bAnd(bIf(Nat.beq u K.one, false, true),
    bAnd(Nat.beq (K.pc v v) K.one, bAnd(bIf(Nat.beq v K.one, false, true),
    bAnd(bIf(Nat.beq u v, false, true), bAnd(Nat.beq (K.pc u v) (K.pc v u),
    bAnd(Nat.beq (K.pc u x) (K.pc x u), Nat.beq (K.pc v x) (K.pc x v)))))))))))

@[expose] noncomputable def headK : Bool :=
  bAnd(szOK K.n K.w, bAnd(Nat.ble K.g K.R, bAnd(Nat.blt 0 K.ord,
  bAnd(allN K.g fun i => K.can (K.GP i),
  bAnd(allN K.sy fun a => bAnd(Nat.blt (K.SY a) K.R,
    bAnd(K.can (K.AI a), permOK K.n K.w (mask K.w) (Nat.mul K.n K.w) (K.A a) (K.AI a))),
  bAnd(CFSG.KC.Child3.offOK K.CS K.OFF K.NC,
  bAnd(Nat.beq K.RE.length K.CS.length, bAnd(Nat.beq K.nw K.CS.length,
    K.RE.all fun r => Nat.blt r K.ord))))))))

@[expose] noncomputable def arg (t i : Nat) : Nat := nIf(Nat.beq i 0, K.A1 t, nIf(Nat.beq i 1, K.A2 t, K.A3 t))

@[expose] noncomputable def nargs (t : Nat) : Nat := nIf(Nat.beq (K.OP t) 2, 2, 3)

@[expose] noncomputable def opOf (c : Nat) : Nat :=
  nIf(Nat.beq c 109, 0, nIf(Nat.beq c 112, 1, nIf(Nat.beq c 118, 2, 3)))

@[expose] noncomputable def progRun (cs : List Char) : Nat → Nat → Nat → Nat → Nat → Bool :=
  List.rec (motive := fun _ => Nat → Nat → Nat → Nat → Nat → Bool)
    (fun t ph _ _ _ => bAnd(Nat.beq ph 0, Nat.beq t K.N))
    (fun ch _ ih t ph i v dg => strictB (Char.toNat ch) fun c =>
      bIf(Nat.beq ph 0, bAnd(Nat.blt t K.N, bAnd(Nat.beq (opOf c) (K.OP t), ih t 1 0 0 0)),
      bIf(Nat.beq ph 1, bAnd(Nat.beq c 32, ih t 2 0 0 0),
      bIf(Nat.blt (CFSG.KC.SurjK.digV c) 10, ih t 2 i (Nat.add (Nat.mul v 10) (CFSG.KC.SurjK.digV c)) 1,
      bIf(Nat.beq c 32, bAnd(Nat.beq dg 1, bAnd(Nat.beq v (K.arg t i),
        bAnd(Nat.blt (Nat.succ i) (K.nargs t), ih t 2 (Nat.succ i) 0 0))),
      bIf(Nat.beq c 10, bAnd(Nat.beq dg 1, bAnd(Nat.beq v (K.arg t i),
        bAnd(Nat.beq (Nat.succ i) (K.nargs t), ih (Nat.succ t) 0 0 0 0))),
        false))))))
    cs

@[expose] noncomputable def progK (cs : List Char) : Bool := K.progRun cs 0 0 0 0 0

end K3C

end CFSG.KC.K3

end
