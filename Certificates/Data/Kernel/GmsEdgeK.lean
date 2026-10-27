module

public import Certificates.Data.Kernel.GmsPathK
public import Certificates.Data.CFSGNative.Co1.S365U

public section

namespace CFSG.KC.GmsPath

open CFSG.KLie.CT CFSG.KC.Loop CFSG.KC.M1F2

@[expose] noncomputable def anyPar (YL : List Nat) (a : Nat) : Bool :=
  List.rec (motive := fun _ => Bool) false (fun y _ ih => orB (parF (Nat.land a y)) ih) YL

@[expose] noncomputable def memFst (ALP : List (Nat × Nat)) (a : Nat) : Bool :=
  List.rec (motive := fun _ => Bool) false
    (fun e _ ih => orB (Prod.rec (motive := fun _ => Bool) (fun x _ => Nat.beq x a) e) ih) ALP

@[expose] noncomputable def crdOK (D : Nat) (ALP : List (Nat × Nat)) : Bool :=
  List.rec (motive := fun _ => Bool) true
    (fun e _ ih => andB (Prod.rec (motive := fun _ => Bool)
      (fun a c => Nat.beq (vmF (nat_lit 24) D a) c) e) ih) ALP

@[expose] noncomputable def pairsK (FM cb : Nat) (g : Nat → Bool) (ALP : List (Nat × Nat)) : Bool :=
  List.rec (motive := fun _ => Bool) true
    (fun e _ ih => andB (Prod.rec (motive := fun _ => Bool)
      (fun a c => orB (notB (bit FM (Nat.xor c cb))) (g a)) e) ih) ALP

@[expose] noncomputable def bChk (T F0 FM : Nat) (BA : List (Nat × Nat)) (ALP : List (Nat × Nat))
    (b cb : Nat) : Bool :=
  orB (pairsK FM cb (fun _ => false) ALP)
    (Option.rec (motive := fun _ => Bool) false
      (fun y => andB (Nat.beq (Nat.xor y (vmF (nat_lit 24) T y)) b)
        (strictB (vmF (nat_lit 24) F0 y) fun z => pairsK FM cb (fun a => parF (Nat.land a z)) ALP))
      (CFSG.Sporadic.Co1.S365UNative.memPre BA b))

@[expose] noncomputable def edgeV (T D F0 FM : Nat) (YL : List Nat) (BA ALP : List (Nat × Nat))
    (v : Nat) : Bool :=
  orB (notB (Nat.beq (vmF (nat_lit 24) T v) v))
    (strictB (vmF (nat_lit 24) D v) fun cb => andB (bit FM cb)
      (andB (orB (anyPar YL v) (memFst ALP v)) (bChk T F0 FM BA ALP v cb)))

end CFSG.KC.GmsPath

end
