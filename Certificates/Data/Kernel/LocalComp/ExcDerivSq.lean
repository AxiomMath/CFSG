module

public import Certificates.Data.Kernel.LocalComp.ExcDeriv

public section

namespace CFSG.KC.LocalComp.ExcDeriv

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Prim

@[expose] noncomputable def stepSqK (n w m nw idn : Nat) (AL AI : Nat → Nat) (kA : Nat)
    (cur : List Nat) (mm : Nat) (wd : List Int) (i : Nat) (k : List Nat → Bool) : Bool :=
  strictB (maskProdK n w m idn cur mm) (fun p => strictB (wordK n w m idn AL AI wd) (fun c =>
  strictB (pcomp n w m c c) (fun c2 => strictB (pinvS n w m c2) (fun ci =>
    bAnd(neCK n w m nw p idn, bAnd(lettersK kA wd, bAnd(permOK n w m nw c2 ci,
    bAnd(Nat.beq (pcomp n w m c p) (pcomp n w m p c), bAnd(Nat.blt i (lenK cur),
      k (snocK cur (pcomp n w m (pcomp n w m c2 (lget cur i)) ci)))))))))))

@[expose] noncomputable def derivSqK (n w m nw idn : Nat) (AL AI : Nat → Nat) (kA : Nat)
    (F : List Nat) (steps : List (Nat × List Int × Nat)) : List Nat → Bool :=
  List.rec (motive := fun _ => List Nat → Bool) (fun cur => badK n w m nw idn [] F cur)
    (fun st _ ih cur => bIf(badK n w m nw idn [] F cur, true,
      Prod.rec (motive := fun _ => Bool) (fun mm r => Prod.rec (motive := fun _ => Bool)
        (fun wd i => stepSqK n w m nw idn AL AI kA cur mm wd i ih) r) st)) steps

@[expose] def unzigK (z : Nat) : Int :=
  Bool.rec (motive := fun _ => Int) (Int.negSucc (Nat.div (Nat.sub z 1) 2)) (Int.ofNat (Nat.div z 2))
    (Nat.beq (Nat.mod z 2) 0)

@[expose] def decStep (l : List Nat) : Nat × List Int × Nat :=
  (l.headD 0, (l.drop 2).map unzigK, (l.drop 1).headD 0)

@[expose] def decDerivs (L : List (List (List Nat))) : List (List (Nat × List Int × Nat)) :=
  L.map fun d => (d.drop 1).map decStep

end CFSG.KC.LocalComp.ExcDeriv

end
