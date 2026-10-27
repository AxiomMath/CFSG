module

public import Certificates.Data.Kernel.Q47K
public import Certificates.Data.Kernel.BfsPinBase

public section

namespace CFSG.KC.HeModelK

open CFSG.KC.Enum CFSG.KS CFSG.KC.HexaK CFSG.KC.HeAutK
open CFSG.KC.Q47K (bn)
open CFSG.KLie.CT (anyN sumN andB orB notB)

@[expose] noncomputable def normsK (n w : Nat) (NF : Nat) (TF : Nat → Nat) (g : Nat) (GF : Nat → Nat)
    (x : Nat) : Bool :=
  allN g fun k => inL NF TF (conj n w x (GF k))

@[expose] noncomputable def stabWK (w k x : Nat) : Bool :=
  allN (Nat.shiftLeft 1 k) fun v => Nat.blt (pg w (mask w) x v) (Nat.shiftLeft 1 k)

@[expose] noncomputable def unipWK (w k x : Nat) : Bool :=
  CFSG.KLie.CT.andB (allN (Nat.shiftLeft 1 k) fun v => Nat.beq (pg w (mask w) x v) v)
    (allN 32 fun v => Nat.blt (Nat.xor (pg w (mask w) x v) v) (Nat.shiftLeft 1 k))

@[expose] noncomputable def zetaK (w NT : Nat) (TT : Nat → Nat) (NM : Nat) (TM : Nat → Nat) (Z : Nat) :
    Bool :=
  CFSG.KLie.CT.andB (allN NT fun i => strictB (TT i) fun t => CFSG.KLie.CT.orB (CFSG.KLie.CT.notB (inL NM TM t)) (Nat.beq t (pidn 64 w)))
  (CFSG.KLie.CT.andB (inL NM TM Z) (CFSG.KLie.CT.andB (Nat.beq (pw 64 w Z 3) (pidn 64 w)) (CFSG.KLie.CT.andB (CFSG.KLie.CT.notB (Nat.beq Z (pidn 64 w)))
  (CFSG.KLie.CT.andB (allN NT fun i => strictB (TT i) fun t => CFSG.KLie.CT.orB (CFSG.KLie.CT.notB (comm 64 w Z t)) (Nat.beq t (pidn 64 w)))
    (allN NM fun i => strictB (conj 64 w (TM i) Z) fun c =>
      CFSG.KLie.CT.orB (Nat.beq c Z) (Nat.beq c (pw 64 w Z 2)))))))

@[expose] noncomputable def orbAt (w : Nat) (TT : Nat → Nat) (NM : Nat) (TM : Nat → Nat) (t0 : Nat)
    (W : List Nat) (i : Nat) : Bool :=
  strictB (TT i) fun t => CFSG.KLie.CT.orB (Nat.beq t (pidn 64 w))
    (strictB (W.getD i 0) fun c => strictB (Nat.shiftRight c 1) fun j => CFSG.KLie.CT.andB (Nat.blt j NM)
      (strictB (TM j) fun m => Bool.rec (motive := fun _ => Bool)
        (Nat.beq (conj 64 w m t) t0)
        (CFSG.KLie.CT.andB (comm 64 w m t) (CFSG.KLie.CT.andB (Nat.beq (pw 64 w m 5) (pidn 64 w)) (CFSG.KLie.CT.notB (Nat.beq m (pidn 64 w)))))
        (Nat.beq (Nat.land c 1) 1)))

structure D64 where
  gT : Nat
  GT : Nat → Nat
  NT : Nat
  TT : Nat → Nat
  NM : Nat
  TM : Nat → Nat
  gC : Nat
  GC : Nat → Nat
  NP : Nat
  TP : Nat → Nat
  gB : Nat
  GB : Nat → Nat
  NB : Nat
  TB : Nat → Nat
  gF : Nat
  GF : Nat → Nat
  NF : Nat
  TF : Nat → Nat
  gP23 : Nat
  GP23 : Nat → Nat
  t0 : Nat
  FB : Nat

@[expose] noncomputable def b0K (d : D64) : Bool :=
  CFSG.KLie.CT.andB (allN d.gT fun a => allN d.gT fun b => comm 64 7 (d.GT a) (d.GT b))
  (CFSG.KLie.CT.andB (inL d.NT d.TT d.t0) (CFSG.KLie.CT.andB (allN d.gC fun k => inL d.NM d.TM (d.GC k))
  (CFSG.KLie.CT.andB (allN d.gC fun k => comm 64 7 (d.GC k) d.t0) (CFSG.KLie.CT.andB (allN d.gB fun k => inL d.NP d.TP (d.GB k))
  (CFSG.KLie.CT.andB (allN d.gT fun k => inL d.NB d.TB (d.GT k)) (CFSG.KLie.CT.andB (allN d.gF fun k => inL d.NB d.TB (d.GF k))
  (CFSG.KLie.CT.andB (allN d.NF fun i => strictB (d.TF i) fun x => Nat.beq (mul 64 7 x x) (pidn 64 7))
  (CFSG.KLie.CT.andB (anyN d.NF fun i => CFSG.KLie.CT.notB (inL d.NT d.TT (d.TF i)))
  (CFSG.KLie.CT.andB (allN d.gB fun k => normsK 64 7 d.NF d.TF d.gF d.GF (d.GB k))
  (CFSG.KLie.CT.andB (allN d.gP23 fun k => strictB (d.GP23 k) fun g =>
      anyN d.NT fun i => inL d.NM d.TM (mul 64 7 (inv 64 7 (d.TT i)) g))
  (CFSG.KLie.CT.andB (allN d.gP23 fun k => normsK 64 7 d.NF d.TF d.gF d.GF (d.GP23 k))
  (CFSG.KLie.CT.andB (allN d.gP23 fun k => Nat.beq (pw 64 7 (d.GP23 k) 8) (pidn 64 7))
    (Nat.beq (cntR (fun i => normsK 64 7 d.NF d.TF d.gF d.GF (d.TM i)) 0 d.NM) 144)))))))))))))

structure D32 where
  NC : Nat
  TC : Nat → Nat
  gPC : Nat
  GPC : Nat → Nat
  TCa : Nat
  gBC : Nat
  GBC : Nat → Nat
  NBC : Nat
  TBC : Nat → Nat
  N0 : Nat
  T0 : Nat → Nat
  N1 : Nat
  T1 : Nat → Nat
  g12 : Nat
  G12 : Nat → Nat
  g13 : Nat
  G13 : Nat → Nat
  gE : Nat
  GE : Nat → Nat
  NU0 : Nat
  TU0 : Nat → Nat
  gF : Nat
  GF : Nat → Nat
  NU1 : Nat
  TU1 : Nat → Nat
  FBC : Nat

@[expose] noncomputable def cK (d : D32) : Bool :=
  CFSG.KLie.CT.andB (inL d.NC d.TC d.TCa)
  (CFSG.KLie.CT.andB (allN d.gBC fun k => CFSG.KLie.CT.andB (inL d.N0 d.T0 (d.GBC k)) (inL d.N1 d.T1 (d.GBC k)))
  (CFSG.KLie.CT.andB (allN d.g12 fun k => inL d.NC d.TC (d.G12 k)) (CFSG.KLie.CT.andB (allN d.g13 fun k => inL d.NC d.TC (d.G13 k))
  (CFSG.KLie.CT.andB (allN d.gE fun k => CFSG.KLie.CT.andB (inL d.N0 d.T0 (d.GE k)) (inL d.NBC d.TBC (d.GE k)))
  (CFSG.KLie.CT.andB (allN d.gF fun k => CFSG.KLie.CT.andB (inL d.N1 d.T1 (d.GF k)) (inL d.NBC d.TBC (d.GF k)))
  (CFSG.KLie.CT.andB (allN d.NU0 fun i => strictB (d.TU0 i) fun x => Nat.beq (mul 32 6 x x) (pidn 32 6))
  (CFSG.KLie.CT.andB (allN d.NU1 fun i => strictB (d.TU1 i) fun x => Nat.beq (mul 32 6 x x) (pidn 32 6))
  (CFSG.KLie.CT.andB (inL d.NU0 d.TU0 d.TCa) (CFSG.KLie.CT.andB (inL d.NU1 d.TU1 d.TCa)
  (CFSG.KLie.CT.andB (anyN d.g12 fun g => anyN d.gF fun f => CFSG.KLie.CT.notB (inL d.NU1 d.TU1 (conj 32 6 (d.G12 g) (d.GF f))))
  (CFSG.KLie.CT.andB (anyN d.g13 fun g => anyN d.gE fun f => CFSG.KLie.CT.notB (inL d.NU0 d.TU0 (conj 32 6 (d.G13 g) (d.GE f))))
  (CFSG.KLie.CT.andB (allN d.g12 fun k => normsK 32 6 d.NU0 d.TU0 d.gE d.GE (d.G12 k))
    (allN d.g13 fun k => normsK 32 6 d.NU1 d.TU1 d.gF d.GF (d.G13 k))))))))))))))

@[expose] noncomputable def cAt (d : D32) (i : Nat) : Bool :=
  strictB (d.TC i) fun x =>
    CFSG.KLie.CT.andB (CFSG.KLie.CT.orB (CFSG.KLie.CT.notB (allN d.gPC fun k => comm 32 6 x (d.GPC k)))
        (CFSG.KLie.CT.orB (Nat.beq x (pidn 32 6)) (Nat.beq x d.TCa)))
      (CFSG.KLie.CT.andB (CFSG.KLie.CT.orB (CFSG.KLie.CT.notB (allN d.gE fun k => comm 32 6 x (d.GE k))) (inL d.NU0 d.TU0 x))
        (CFSG.KLie.CT.orB (CFSG.KLie.CT.notB (allN d.gF fun k => comm 32 6 x (d.GF k))) (inL d.NU1 d.TU1 x)))

@[expose] noncomputable def cntAt (d : D32) (i : Nat) : Nat :=
  strictN (d.TC i) fun x =>
    Nat.add (bn (stabWK 6 2 x)) (Nat.add (Nat.mul 65536 (bn (stabWK 6 3 x)))
    (Nat.add (Nat.mul 4294967296 (bn (unipWK 6 2 x)))
    (Nat.add (Nat.mul 281474976710656 (bn (unipWK 6 3 x)))
    (Nat.add (Nat.mul 18446744073709551616 (bn (allN d.gE fun k => unipWK 6 2 (conj 32 6 x (d.GE k)))))
      (Nat.mul 1208925819614629174706176 (bn (allN d.gF fun k => unipWK 6 3 (conj 32 6 x (d.GF k)))))))))

@[expose] noncomputable def cntRange (d : D32) (lo len : Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat) 0
    (fun k acc => strictN acc fun a => Nat.add a (cntAt d (Nat.add lo k))) len

@[expose] noncomputable def countK (d : D32) : Bool :=
  CFSG.KLie.CT.andB (allN d.N0 fun i => stabWK 6 2 (d.T0 i)) (CFSG.KLie.CT.andB (allN d.N1 fun i => stabWK 6 3 (d.T1 i))
  (CFSG.KLie.CT.andB (Nat.beq (cntR (fun i => stabWK 6 3 (d.T0 i)) 0 d.N0) 1024)
  (CFSG.KLie.CT.andB (allN d.NU0 fun i => unipWK 6 2 (d.TU0 i)) (allN d.NU1 fun i => unipWK 6 3 (d.TU1 i)))))

end CFSG.KC.HeModelK

end
