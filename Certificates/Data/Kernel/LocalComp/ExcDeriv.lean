module

public import Certificates.Data.Kernel.Spor.Prim
public import Certificates.Data.Kernel.Griess13.Packed

public section

namespace CFSG.KC.LocalComp.ExcDeriv

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Prim CFSG.KC.G13

@[expose] noncomputable def fixCntK (w m p : Nat) (k : Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat) (nat_lit 0)
    (fun i ih => Nat.add ih (nIf(Nat.beq (pg w m p i) i, nat_lit 1, nat_lit 0))) k

@[expose] noncomputable def memK (x : Nat) (L : List Nat) : Bool :=
  List.rec (motive := fun _ => Bool) false (fun y _ ih => bIf(Nat.beq x y, true, ih)) L

@[expose] noncomputable def anyL (f : Nat → Bool) (L : List Nat) : Bool :=
  List.rec (motive := fun _ => Bool) false (fun y _ ih => bIf(f y, true, ih)) L

@[expose] noncomputable def anyN (k : Nat) (f : Nat → Bool) : Bool :=
  Nat.rec (motive := fun _ => Bool) false (fun i ih => bIf(f i, true, ih)) k

@[expose] noncomputable def lenK (L : List Nat) : Nat :=
  List.rec (motive := fun _ => Nat) (nat_lit 0) (fun _ _ ih => Nat.succ ih) L

@[expose] noncomputable def snocK (L : List Nat) (x : Nat) : List Nat :=
  List.rec (motive := fun _ => List Nat) [x] (fun y _ ih => y :: ih) L

@[expose] noncomputable def maskProdK (n w m idn : Nat) (cur : List Nat) : Nat → Nat :=
  List.rec (motive := fun _ => Nat → Nat) (fun _ => idn)
    (fun g _ ih mm => strictN (ih (Nat.shiftRight mm (nat_lit 1))) (fun r =>
      nIf(Nat.beq (Nat.land mm (nat_lit 1)) (nat_lit 1), pcomp n w m g r, r))) cur

@[expose] noncomputable def neCK (n w m nw a b : Nat) : Bool :=
  bAnd(canonK n w m nw a, bAnd(canonK n w m nw b, bIf(Nat.beq a b, false, true)))

@[expose] noncomputable def badK (n w m nw idn : Nat) (Z F cur : List Nat) : Bool :=
  bIf(anyL (fun g => neCK n w m nw (pcomp n w m g g) idn) cur, true,
  bIf(anyL (fun g => anyL (fun h => neCK n w m nw (pcomp n w m g h) (pcomp n w m h g)) cur) cur,
    true,
  anyN (Nat.shiftLeft (nat_lit 1) (lenK cur)) (fun mm => strictB (maskProdK n w m idn cur mm)
    (fun p => bAnd(neCK n w m nw p idn,
      bIf(memK p Z, true, memK (fixCntK w m p n) F))))))

@[expose] noncomputable def stepK (n w m nw idn : Nat) (AL AI : Nat → Nat) (kA : Nat)
    (okW : List Int → Bool) (cur : List Nat) (mm : Nat) (wd : List Int) (i : Nat)
    (k : List Nat → Bool) : Bool :=
  strictB (maskProdK n w m idn cur mm) (fun p => strictB (wordK n w m idn AL AI wd) (fun c =>
  strictB (pinvS n w m c) (fun ci =>
    bAnd(neCK n w m nw p idn, bAnd(okW wd, bAnd(lettersK kA wd, bAnd(permOK n w m nw c ci,
    bAnd(Nat.beq (pcomp n w m c p) (pcomp n w m p c), bAnd(Nat.blt i (lenK cur),
      k (snocK cur (pcomp n w m (pcomp n w m c (lget cur i)) ci)))))))))))

@[expose] noncomputable def derivK (n w m nw idn : Nat) (AL AI : Nat → Nat) (kA : Nat)
    (okW : List Int → Bool) (Z F : List Nat) (steps : List (Nat × List Int × Nat)) :
    List Nat → Bool :=
  List.rec (motive := fun _ => List Nat → Bool) (fun cur => badK n w m nw idn Z F cur)
    (fun st _ ih cur => bIf(badK n w m nw idn Z F cur, true,
      Prod.rec (motive := fun _ => Bool) (fun mm r => Prod.rec (motive := fun _ => Bool)
        (fun wd i => stepK n w m nw idn AL AI kA okW cur mm wd i ih) r) st)) steps

@[expose] noncomputable def stepC (s : Nat × List Int × Nat) : List Char :=
  [':'].intercalate [natC s.1, [','].intercalate (s.2.1.map intC), natC s.2.2]

@[expose] noncomputable def derivC (d : List (Nat × List Int × Nat)) : List Char :=
  [';'].intercalate (d.map stepC)

@[expose] noncomputable def derivsC (ds : List (List (Nat × List Int × Nat))) : List Char :=
  ['|'].intercalate (ds.map derivC)

end CFSG.KC.LocalComp.ExcDeriv

end
