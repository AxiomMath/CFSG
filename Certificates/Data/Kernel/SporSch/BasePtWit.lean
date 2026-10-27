module

public import Certificates.Data.Kernel.Spor.Chain

public section

namespace CFSG.KS.SporSch.BPW

open CFSG.KC.Enum CFSG.KS

@[expose] noncomputable def itP (f : Nat → Nat) (e i : Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat) i (fun _ ih => strictN ih f) e

@[expose] noncomputable def movB (f : Nat → Nat) (bs : List Nat) : Bool :=
  List.rec (motive := fun _ => Bool) false (fun b _ ih => bIf(Nat.beq (f b) b, ih, true)) bs

@[expose] noncomputable def fixB (f : Nat → Nat) (e : Nat) (bs : List Nat) : Bool :=
  List.rec (motive := fun _ => Bool) true (fun b _ ih => bAnd(Nat.beq (itP f e b) b, ih)) bs

@[expose] noncomputable def xP (w U S i : Nat) : Nat := pg w (mask w) U (pg w (mask w) S i)

@[expose] noncomputable def y1P (w U S C CI i : Nat) : Nat :=
  xP w U S (pg w (mask w) C (xP w U S (pg w (mask w) CI i)))

@[expose] noncomputable def y2P (w U S C1 C1I C2 C2I i : Nat) : Nat :=
  y1P w U S C1 C1I (pg w (mask w) C2 (xP w U S (pg w (mask w) C2I i)))

@[expose] noncomputable def witB (w U S e : Nat) (bs : List Nat) (OG : List (Nat × Nat)) : Bool :=
  bIf(List.rec (motive := fun _ => Bool) false (fun c _ ih =>
      Prod.rec (motive := fun _ => Bool) (fun C CI =>
        bIf(movB (itP (y1P w U S C CI) e) bs, true, ih)) c) OG, true,
    List.rec (motive := fun _ => Bool) false (fun c₁ _ ih =>
      Prod.rec (motive := fun _ => Bool) (fun C1 C1I =>
        bIf(List.rec (motive := fun _ => Bool) false (fun c₂ _ ih2 =>
          Prod.rec (motive := fun _ => Bool) (fun C2 C2I =>
            bIf(movB (itP (y2P w U S C1 C1I C2 C2I) e) bs, true, ih2)) c₂) OG, true, ih)) c₁) OG)

@[expose] noncomputable def rowsB (w U S : Nat) (bs : List Nat)
    (rows : List (Nat × Nat × List (Nat × Nat))) : Bool :=
  List.rec (motive := fun _ => Bool) true (fun r _ ih =>
    Prod.rec (motive := fun _ => Bool) (fun p r2 =>
      Prod.rec (motive := fun _ => Bool) (fun e OG =>
        bAnd(bIf(bAnd(fixB (xP w U S) p bs, movB (xP w U S) bs), witB w U S e bs OG, true), ih))
        r2) r) rows

@[expose] noncomputable def candB (w U : Nat) (bs : List Nat)
    (rows : List (Nat × Nat × List (Nat × Nat))) (T : Nat → Nat) (cnt b len : Nat) : Bool :=
  allBlk b (fun k => bIf(Nat.blt k cnt, rowsB w U (T k) bs rows, true)) len

@[expose] noncomputable def wordK (n w : Nat) (gP gIP : List Nat) (wd : List Int) : Nat :=
  List.rec (motive := fun _ => Nat) (pidn n w) (fun z _ ih =>
    pcomp n w (mask w)
      (if 0 < z then gP.getD (z.toNat - 1) 0 else gIP.getD ((-z).toNat - 1) 0) ih) wd

end CFSG.KS.SporSch.BPW

end
