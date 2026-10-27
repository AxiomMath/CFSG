module

public import Certificates.Data.Kernel.Spor.Prim
public import Certificates.Data.Kernel.OrbRow.Defs

public section

namespace CFSG.KC.HeChain

open CFSG.KC.Enum CFSG.KS CFSG.KC.OrbRow

@[expose] noncomputable def evK (w m : Nat) (ys : List Nat) (p : Nat) : Nat :=
  List.rec (motive := fun _ => Nat) p (fun t _ ih => pg w m t ih) ys

@[expose] noncomputable def keyN (w m : Nat) (ys : List Nat) (nf : Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat) (nat_lit 0)
    (fun k ih => Nat.lor ih (Nat.shiftLeft (evK w m ys k) (Nat.mul w k))) nf

@[expose] noncomputable def invP (w m : Nat) (ys : List Nat) (nf : Nat) : Bool :=
  allN nf (fun k => Nat.beq (evK w m ys (evK w m ys k)) k)

@[expose] noncomputable def leafK (w m nf kt k1 ncl : Nat) (CK : List (List Nat)) (ys : List Nat)
    (st : List Nat) (k : List Nat → Bool) : Bool :=
  bIf(invP w m ys nf,
    strictB (keyN w m ys nf) (fun key =>
      bIf(Nat.beq key kt, k st, bIf(Nat.beq key k1, k st,
        List.rec (motive := fun _ => Bool) false
          (fun r rest _ => bAnd(Nat.blt (Nat.land r (nat_lit 255)) ncl,
            bAnd(Nat.beq key (getS (getLs CK (Nat.land r (nat_lit 255))) (Nat.shiftRight r (nat_lit 8))),
              k rest)))
          st))),
    k st)

@[expose] noncomputable def walkK (w m nf kt k1 ncl : Nat) (CK : List (List Nat)) (t0 c : Nat) :
    List (List Nat) → Nat → List Nat → List Nat → (List Nat → Bool) → Bool :=
  List.rec (motive := fun _ => Nat → List Nat → List Nat → (List Nat → Bool) → Bool)
    (fun q stack st k => bIf(Nat.beq q c, leafK w m nf kt k1 ncl CK (List.cons t0 stack) st k, k st))
    (fun lvl _ ih q stack st k =>
      List.rec (motive := fun _ => List Nat → (List Nat → Bool) → Bool)
        (fun st k => k st)
        (fun t _ ihT st k => strictB (pg w m t q) (fun q' =>
          ih q' (List.cons t stack) st (fun st' => ihT st' k)))
        lvl st k)

@[expose] noncomputable def covK (w m nf ncl : Nat) (tau : Nat) (CK : List (List Nat)) (b0 : Nat)
    (T0 : List Nat) (Ls : List (List Nat)) (Cc : List Nat) (Cov : List (List Nat)) (i : Nat) :
    Bool :=
  strictB (keyN w m (List.cons tau List.nil) nf) (fun kt =>
  strictB (keyN w m List.nil nf) (fun k1 =>
  strictB (getS T0 i) (fun t0 => strictB (getS Cc i) (fun c =>
    bAnd(Nat.beq (pg w m t0 c) b0,
      walkK w m nf kt k1 ncl CK t0 c Ls (pg w m t0 b0) List.nil (getLs Cov i)
        (fun st => List.rec (motive := fun _ => Bool) true (fun _ _ _ => false) st))))))

@[expose] noncomputable def setLs (L : List (List Nat)) (i : Nat) (x : List Nat) : List (List Nat) :=
  List.rec (motive := fun _ => Nat → List (List Nat)) (fun _ => List.nil)
    (fun y t ih j => Nat.rec (motive := fun _ => List (List Nat)) (List.cons x t)
      (fun j' _ => List.cons y (ih j')) j) L i

end CFSG.KC.HeChain

end
