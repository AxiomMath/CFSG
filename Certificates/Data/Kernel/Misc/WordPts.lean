module

public import CFSG.Certificates.Kernel.Enum.Defs
public import Certificates.Data.Kernel.Spor.Chain
public import Certificates.Data.Kernel.M1F2

public section

namespace CFSG.KC.WordPts

open CFSG.KS CFSG.KLie.CT
open CFSG.KC.Enum (pg strictN)

@[expose] noncomputable def letP (G GI : Nat → Nat) (z : Int) : Nat :=
  Int.rec (motive := fun _ => Nat) (fun k => G (Nat.sub k (nat_lit 1))) (fun k => GI k) z

@[expose] noncomputable def imgP (n w t q : Nat) : Nat := nIf(Nat.blt q n, pg w (mask w) t q, nat_lit 0)

@[expose] noncomputable def evW (n w : Nat) (G GI : Nat → Nat) (wd : List Int) (p : Nat) : Nat :=
  List.rec (motive := fun _ => Nat → Nat) (fun p => p)
    (fun z _ ih p => strictN (ih p) fun q => imgP n w (letP G GI z) q) wd p

@[expose] noncomputable def evIW (n w : Nat) (G GI : Nat → Nat) (wd : List Int) (p : Nat) : Nat :=
  List.rec (motive := fun _ => Nat → Nat) (fun p => p)
    (fun z _ ih p => strictN (imgP n w (letP GI G z) p) fun q => ih q) wd p

@[expose] noncomputable def evWs (n w : Nat) (G GI : Nat → Nat) (ws : List (List Int)) (p : Nat) :
    Nat :=
  List.rec (motive := fun _ => Nat → Nat) (fun p => p)
    (fun wd _ ih p => strictN (ih p) fun q => evW n w G GI wd q) ws p

@[expose] noncomputable def eqPtsK (n w : Nat) (G GI : Nat → Nat) (bs : List Nat)
    (xs ys : List (List Int)) : Bool :=
  List.rec (motive := fun _ => Bool) true
    (fun b _ ih => andB (Nat.beq (evWs n w G GI xs b) (evWs n w G GI ys b)) ih) bs

@[expose] noncomputable def fixPtsK (n w : Nat) (G GI : Nat → Nat) (bs : List Nat)
    (xs : List (List Int)) : Bool :=
  List.rec (motive := fun _ => Bool) true
    (fun b _ ih => andB (Nat.beq (evWs n w G GI xs b) b) ih) bs

@[expose] noncomputable def selW (B : List (List Int)) (c : Nat) : List (List Int) :=
  List.rec (motive := fun _ => Nat → List (List Int)) (fun _ => [])
    (fun b _ ih r => Bool.rec (motive := fun _ => List (List Int)) (ih (Nat.succ r))
      (b :: ih (Nat.succ r)) (bit c r)) B (nat_lit 0)

@[expose] noncomputable def colF (d M i : Nat) : Nat :=
  orN d fun r => Nat.shiftLeft (Nat.land (Nat.shiftRight M (Nat.add (Nat.mul d r) i)) (nat_lit 1)) r

@[expose] noncomputable def ebK (n w : Nat) (G GI : Nat → Nat) (bs : List Nat)
    (B : List (List Int)) (k : Nat) : Bool :=
  andB (Nat.beq B.length k) (
  andB (allN k fun i => fixPtsK n w G GI bs [B.getD i [], B.getD i []]) (
  andB (allN k fun i => allN k fun j =>
    eqPtsK n w G GI bs [B.getD i [], B.getD j []] [B.getD j [], B.getD i []])
    (allN (Nat.sub (pw2 k) (nat_lit 1)) fun c =>
      notB (fixPtsK n w G GI bs (selW B (Nat.succ c))))))

@[expose] noncomputable def conjPtsK (n w : Nat) (G GI : Nat → Nat) (bs : List Nat)
    (g b : List Int) (ys : List (List Int)) : Bool :=
  List.rec (motive := fun _ => Bool) true
    (fun p _ ih => andB (Nat.beq (evW n w G GI g (evW n w G GI b (evIW n w G GI g p)))
      (evWs n w G GI ys p)) ih) bs

@[expose] noncomputable def matK (n w : Nat) (G GI : Nat → Nat) (bs : List Nat)
    (B : List (List Int)) (k : Nat) (g : List Int) (M : Nat) : Bool :=
  allN k fun i => conjPtsK n w G GI bs g (B.getD i []) (selW B (colF k M i))

end CFSG.KC.WordPts

end
