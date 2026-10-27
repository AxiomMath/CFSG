module

public import Certificates.Data.Kernel.Spor.PChain
public import Certificates.Data.CFSGNative.J1.Vec

public section

namespace CFSG.KS.VO

open CFSG.KC.Enum CFSG.KS CFSG.KS.PEnum CFSG.KS.PC CFSG.Sporadic.J1.Native

@[expose] noncomputable def codeV (v : List Nat) : Nat :=
  List.rec (motive := fun _ => Nat → Nat) (fun _ => nat_lit 0)
    (fun x _ ih s => Nat.lor (Nat.shiftLeft x s) (ih (Nat.add s (nat_lit 4)))) v (nat_lit 0)

@[expose] noncomputable def decV (d c : Nat) : List Nat :=
  List.map (fun k => Nat.land (Nat.shiftRight c (Nat.mul (nat_lit 4) k)) (nat_lit 15)) (List.range d)

@[expose] noncomputable def vorbPtK (p d N : Nat) (key : List Nat → List Nat) (A B : List (List Nat))
    (PT AL BE : Nat → Nat) (i : Nat) : Bool :=
  strictB (PT i) fun c => strictB (r32 AL i) fun a => strictB (r32 BE i) fun b =>
    bAnd(Nat.blt c (Nat.shiftLeft (nat_lit 1) (Nat.mul (nat_lit 4) d)),
    bAnd(List.all (decV d c) (fun x => Nat.blt x p),
    bAnd(Nat.blt a N, bAnd(Nat.blt b N,
    bAnd(listEqK (key (mvL p A (decV d c))) (decV d (PT a)),
      listEqK (key (mvL p B (decV d c))) (decV d (PT b)))))))

@[expose] noncomputable def vstep (PA LA : Nat → Nat) (h g c a : Nat) : Nat :=
  nIf(Nat.beq c (nat_lit 0), nat_lit 0, nIf(Nat.blt a c, c,
    nIf(bAnd(Nat.beq a c, bAnd(Nat.beq (r32 PA c) h, Nat.beq (r32 LA c) g)), Nat.succ c, nat_lit 0)))

@[expose] noncomputable def vorbCnt (N : Nat) (AL BE PA LA : Nat → Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat) (nat_lit 1)
    (fun h c => strictN c (fun c' => nIf(Nat.blt h c',
      strictN (vstep PA LA h (nat_lit 1) c' (r32 AL h)) (fun c2 =>
        vstep PA LA h (nat_lit 2) c2 (r32 BE h)), nat_lit 0))) N

@[expose] noncomputable def vorbHdK (p d N cap : Nat) (A B : List (List Nat)) (root : List Nat)
    (PT AL BE PA LA : Nat → Nat) : Bool :=
  bAnd(Nat.ble p (nat_lit 16), bAnd(Nat.ble d (nat_lit 16), bAnd(Nat.blt (nat_lit 0) N,
  bAnd(Nat.ble N cap, bAnd(Nat.blt N (nat_lit 4294967296),
  bAnd(Nat.beq (List.length A) d, bAnd(Nat.beq (List.length B) d,
  bAnd(List.all A (fun r => Nat.beq (List.length r) d), bAnd(List.all B (fun r => Nat.beq (List.length r) d),
  bAnd(listEqK root (decV d (PT (nat_lit 0))),
  bAnd(Nat.beq (r32 PA (nat_lit 0)) (nat_lit 0), bAnd(Nat.beq (r32 LA (nat_lit 0)) (nat_lit 0),
    Nat.beq (vorbCnt N AL BE PA LA) N))))))))))))

@[expose] noncomputable def vorbSortK (N : Nat) (PT SO : Nat → Nat) (s : Nat) : Bool :=
  strictB (r32 SO s) fun x => bAnd(Nat.blt x N,
    bIf(Nat.blt (Nat.succ s) N, Nat.blt (PT x) (PT (r32 SO (Nat.succ s))), true))

@[expose] noncomputable def projV (p : Nat) (v : List Nat) : List Nat :=
  List.map (fun x => Nat.mod (Nat.mul x (Nat.mod (Nat.pow (firstNZ v) (Nat.sub p (nat_lit 2))) p))
    p) v

@[expose] noncomputable def projSortK (p d N : Nat) (PT SP : Nat → Nat) (s : Nat) : Bool :=
  strictB (r32 SP s) fun x => bAnd(Nat.blt x N, bAnd(Bool.not (Nat.beq (PT x) (nat_lit 0)),
    bIf(Nat.blt (Nat.succ s) N,
      Nat.blt (codeV (projV p (decV d (PT x))))
        (codeV (projV p (decV d (PT (r32 SP (Nat.succ s)))))), true)))

end CFSG.KS.VO

end
