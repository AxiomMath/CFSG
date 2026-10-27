module

public import Certificates.Data.Kernel.He7222.Fib
public import Certificates.Data.Kernel.Spor.Raw

public section

namespace CFSG.KC.HeChain

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Mathieu CFSG.KC.OrbRow

@[expose] noncomputable def letT (S SI : Nat → Nat) (c : Nat) : Nat :=
  nIf(Nat.beq (Nat.land c (nat_lit 1)) (nat_lit 0), S (Nat.sub (Nat.shiftRight c (nat_lit 1)) (nat_lit 1)),
    SI (Nat.sub (Nat.shiftRight c (nat_lit 1)) (nat_lit 1)))

@[expose] noncomputable def letTI (S SI : Nat → Nat) (c : Nat) : Nat :=
  nIf(Nat.beq (Nat.land c (nat_lit 1)) (nat_lit 0), SI (Nat.sub (Nat.shiftRight c (nat_lit 1)) (nat_lit 1)),
    S (Nat.sub (Nat.shiftRight c (nat_lit 1)) (nat_lit 1)))

@[expose] noncomputable def wpK (w m : Nat) (S SI : Nat → Nat) (wd : List Int) : Nat → Nat :=
  List.rec (motive := fun _ => Nat → Nat) (fun p => p)
    (fun z _ ih p => strictN (ih p) (fun q => strictN (icode z) (fun c => pg w m (letT S SI c) q))) wd

@[expose] noncomputable def wpIK (w m : Nat) (S SI : Nat → Nat) (wd : List Int) : Nat → Nat :=
  List.rec (motive := fun _ => Nat → Nat) (fun p => p)
    (fun z _ ih p => strictN (icode z) (fun c => ih (pg w m (letTI S SI c) p))) wd

@[expose] noncomputable def powF (f : Nat → Nat) (e q : Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat → Nat) (fun q => q) (fun _ ih q => strictN (f q) ih) e q

@[expose] noncomputable def oK (w m : Nat) (f : Nat → Nat) (tau p i q : Nat) : Nat :=
  powF f i (pg w m tau (powF f (Nat.sub p i) q))

@[expose] noncomputable def prodO (w m : Nat) (f : Nat → Nat) (tau p mk q : Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat → Nat) (fun q => q)
    (fun i ih q => ih (nIf(Nat.beq (Nat.land (Nat.shiftRight mk i) (nat_lit 1)) (nat_lit 1),
      oK w m f tau p i q, q))) p q

@[expose] noncomputable def getWI (L : List (List Int)) : Nat → List Int :=
  List.rec (motive := fun _ => Nat → List Int) (fun _ => List.nil)
    (fun x _ ih j => Nat.rec (motive := fun _ => List Int) x (fun i _ => ih i) j) L

@[expose] noncomputable def lenWI (L : List (List Int)) : Nat :=
  List.rec (motive := fun _ => Nat) (nat_lit 0) (fun _ _ ih => Nat.succ ih) L

@[expose] noncomputable def basK (w m : Nat) (f : Nat → Nat) (tau p : Nat) (S SI : Nat → Nat)
    (d : List Int) (rec : List Nat) : List (List Int) → Nat → Bool :=
  List.rec (motive := fun _ => Nat → Bool) (fun _ => true)
    (fun b _ ih q => strictB (getS rec q) (fun mk => bAnd(lettersK (nat_lit 2) b,
      bAnd(allN (nat_lit 5) (fun x =>
          Nat.beq (wpK w m S SI d (wpK w m S SI b (wpIK w m S SI d x))) (prodO w m f tau p mk x)),
        ih (Nat.succ q)))))

@[expose] noncomputable def selB (k : Nat) (R5 R7 : List (List Int)) : List (List Int) :=
  Bool.rec (motive := fun _ => List (List Int)) R7 R5 (Nat.beq k (nat_lit 0))

@[expose] noncomputable def lenLN (L : List (List Nat)) : Nat :=
  List.rec (motive := fun _ => Nat) (nat_lit 0) (fun _ _ ih => Nat.succ ih) L

@[expose] noncomputable def goodK (w m : Nat) (f : Nat → Nat) (tau : Nat) (S SI : Nat → Nat)
    (DW R5 R7 : List (List Int)) (rec : List Nat) : Bool :=
  strictB (getS rec (nat_lit 0)) (fun p => bAnd(Nat.blt (nat_lit 0) p,
    bAnd(allN (nat_lit 5) (fun q => Nat.beq (powF f p q) q),
      bIf(Nat.beq (getS rec (nat_lit 1)) (nat_lit 0),
        strictB (getS rec (nat_lit 2)) (fun j => strictB (getS rec (nat_lit 3)) (fun q =>
          bAnd(Nat.blt j p, bAnd(Nat.blt q (nat_lit 5),
            bIf(Nat.beq (oK w m f tau p j (pg w m tau q)) (pg w m tau (oK w m f tau p j q)),
              false, true))))),
        bAnd(Nat.beq (getS rec (nat_lit 1)) (nat_lit 1),
          strictB (getS rec (nat_lit 3)) (fun k => bAnd(Nat.ble k (nat_lit 1),
            strictB (getS rec (nat_lit 2)) (fun c => bAnd(Nat.blt c (lenWI DW),
              bAnd(lettersK (nat_lit 3) (getWI DW c),
                bAnd(Nat.beq (lenS rec) (Nat.add (nat_lit 4) (lenWI (selB k R5 R7))),
                  basK w m f tau p S SI (getWI DW c) rec (selB k R5 R7) (nat_lit 4))))))))))))

@[expose] noncomputable def goodLK (w m : Nat) (KTs : List (List Nat)) (gs : List Nat) (tau : Nat)
    (S SI : Nat → Nat) (DW R5 R7 : List (List Int)) (FT GD : List (List Nat)) : Bool :=
  List.rec (motive := fun _ => Nat → Bool)
    (fun t => Nat.beq t (lenLN GD))
    (fun kt _ ih t => bAnd(goodK w m (fun q => evK w m gs (evK w m (stkK KTs kt) q)) tau S SI DW R5 R7
      (getLs GD t), strictB (Nat.succ t) ih))
    FT (nat_lit 0)

end CFSG.KC.HeChain

end
