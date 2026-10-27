module

public import Certificates.Data.Kernel.SporSch.PairClT
public import Certificates.Data.Kernel.SporSch.PairJ3Cnt
public import Certificates.Data.Kernel.HeLoc.Tree

public section

namespace CFSG.KC.HeLoc

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.SporSch

@[expose] noncomputable def relK (rels : List (Nat × Nat × Nat)) (xm : Nat → Nat) (img : Nat → Nat)
    (i : Nat) : Bool :=
  List.rec (motive := fun _ => Bool) true
    (fun r _ ih => bAnd(bIf(Nat.beq (Nat.max r.1 r.2.1) i,
      Nat.beq (img r.2.1) (powF xm r.2.2 (img r.1)), true), ih)) rels

@[expose] noncomputable def bsK (KE SK : Nat → Nat) (key : Nat) : Nat → Nat → Nat → Bool :=
  Nat.rec (motive := fun _ => Nat → Nat → Bool) (fun _ _ => false)
    (fun _ ih lo hi => bIf(Nat.blt lo hi,
      strictB (Nat.div (Nat.add lo hi) 2) (fun mid => strictB (KE (SK mid)) (fun v =>
        bIf(Nat.beq v key, true, bIf(Nat.blt v key, ih (Nat.succ mid) hi, ih lo mid)))), false))

@[expose] noncomputable def imgExt (img : Nat → Nat) (i p m : Nat) : Nat := nIf(Nat.blt m i, img m, p)

@[expose] noncomputable def ptK (n w kS NR NL : Nat) (LT PT QT LR FR : Nat → Nat)
    (rels : List (Nat × Nat × Nat)) (xm : Nat → Nat) (cb ps : List Nat) (KE SK : Nat → Nat)
    (NE : Nat) : Nat → Nat → (Nat → Nat) → (Nat → Nat) → (Nat → Nat) → Bool :=
  Nat.rec (motive := fun _ => Nat → (Nat → Nat) → (Nat → Nat) → (Nat → Nat) → Bool)
    (fun _ acc _ _ => bIf(eqOnL cb (fun y => acc (xm y)) (fun y => xm (acc y)),
      bsK KE SK (keyV n ps acc) (nat_lit 20) (nat_lit 0) NE, true))
    (fun _ ih i acc accI img =>
      strictB (rcnt (LR i)) fun c =>
      strictB (FR i) fun fr =>
        bIf(Nat.beq fr 0,
          allN c fun k => strictB (acc (rpt w (mask w) (LR i) k)) fun p =>
            bIf(relK rels xm (imgExt img i p) i,
              ih (Nat.succ i) (fun y => acc (trPtT w NR NL LT PT i k y))
                (fun y => trInvPtT w kS NR NL LT PT i k (accI y)) (imgExt img i p), true),
          strictB (accI (powF xm (Nat.mod (Nat.sub fr 1) 8) (img (Nat.div (Nat.sub fr 1) 8))))
            fun q => strictB (lvT NL w QT i q) fun k =>
            bIf(Nat.blt k c, strictB (acc (rpt w (mask w) (LR i) k)) fun p =>
              bIf(relK rels xm (imgExt img i p) i,
                ih (Nat.succ i) (fun y => acc (trPtT w NR NL LT PT i k y))
                  (fun y => trInvPtT w kS NR NL LT PT i k (accI y)) (imgExt img i p), true),
              true)))

end CFSG.KC.HeLoc

end
