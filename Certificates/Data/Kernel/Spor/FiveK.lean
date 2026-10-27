module

public import Certificates.Data.Kernel.Spor.HKeyB

public section

namespace CFSG.KS.MulH

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw

@[expose] noncomputable def keyMemK (x : Nat) (L : List Nat) : Bool :=
  List.rec (motive := fun _ => Bool) false (fun a _ ih => bIf(Nat.beq a x, true, ih)) L

@[expose] noncomputable def appK (L L' : List Nat) : List Nat :=
  List.rec (motive := fun _ => List Nat) L' (fun a _ ih => List.cons a ih) L

@[expose] noncomputable def cntD (L : List Nat) : List Nat → Nat :=
  List.rec (motive := fun _ => List Nat → Nat) (fun _ => nat_lit 0)
    (fun a _ ih seen => nIf(keyMemK a seen, ih seen, Nat.succ (ih (List.cons a seen)))) L

@[expose] noncomputable def anyNewK (kk ck : List Nat) : Bool :=
  List.rec (motive := fun _ => Bool) false (fun a _ ih => bIf(keyMemK a kk, ih, true)) ck

@[expose] noncomputable def cjK (n w m : Nat) (G GI : Nat → Nat) (l y : Nat) : Nat :=
  pcomp n w m (pcomp n w m (G l) y) (GI l)

@[expose] noncomputable def extK (n w m : Nat) (G GI : Nat → Nat) (c r : Nat) :
    Nat → List Nat → List Nat → (List Nat → List Nat → Bool) → Bool :=
  Nat.rec (motive := fun _ => Nat → List Nat → List Nat → (List Nat → List Nat → Bool) → Bool)
    (fun _ cs ck kont => kont cs ck)
    (fun _ ih l cs ck kont => strictB (cjK n w m G GI l c) (fun y =>
      strictB (hkeyB n w m y) (fun hy =>
        ih (Nat.succ l) (appK cs (List.cons y List.nil)) (appK ck (List.cons hy List.nil)) kont)))
    r

@[expose] noncomputable def kidsK (n w m : Nat) (G GI : Nat → Nat) (k : Nat)
    (nx : List Nat → List Nat → List Nat → Bool) (kk cs0 ck0 : List Nat) (cs : List Nat) :
    List Nat → Bool :=
  List.rec (motive := fun _ => List Nat → Bool) (fun _ => true)
    (fun c _ ihc ck => List.rec (motive := fun _ => Bool) true
      (fun kc ckt _ => bAnd(bIf(keyMemK kc kk, true,
          extK n w m G GI c k (nat_lit 0) cs0 ck0
            (fun cs' ck' => nx (appK kk (List.cons kc List.nil)) cs' ck')),
        ihc ckt)) ck) cs

@[expose] noncomputable def fiveK (n w m : Nat) (G GI : Nat → Nat) (k : Nat) (f : Nat) :
    List Nat → List Nat → List Nat → Bool :=
  Nat.rec (motive := fun _ => List Nat → List Nat → List Nat → Bool)
    (fun kk _ ck => Nat.ble (nat_lit 5) (cntD (appK kk ck) List.nil))
    (fun _ ih kk cs ck => bIf(Nat.ble (nat_lit 5) (cntD (appK kk ck) List.nil), true,
      bAnd(anyNewK kk ck, kidsK n w m G GI k ih kk cs ck cs ck)))
    f

@[expose] noncomputable def fiveTopK (n w m : Nat) (G GI : Nat → Nat) (k f S : Nat) : Bool :=
  strictB (hkeyB n w m S) (fun hs => extK n w m G GI S k (nat_lit 0) List.nil List.nil
    (fun cs ck => fiveK n w m G GI k f (List.cons hs List.nil) cs ck))

end CFSG.KS.MulH

end
