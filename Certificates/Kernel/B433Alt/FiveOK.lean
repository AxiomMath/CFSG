module

public import Certificates.Data.Kernel.B433Alt.Five
public import Certificates.Data.Kernel.B433Alt.Chain
public import Certificates.Kernel.B433Alt.Data.St
import CFSG.Certificates.Kernel.Common.JsonGz
import CFSG.Certificates.Kernel.Common.Repo

public section

#kc_repo #kc_json_gz CFSG.KD.B4AF "Certificates/Kernel/B433Alt/Data/five.json.gz" 36919 2438735406664452503
  (FJ : List Nat) (FA : List Nat) (FB : List Nat) (TW : List (List (List Nat)))
  (TR : List (List (List Nat))) (PX : List (List (List Nat))) (PQ : List (List Nat))
  (NB : List (List Nat)) (NG : List (List (List (List Nat)))) (NE : List (List (List (List Nat))))
  (NP : List (List (List Nat))) (NQ : List (List (List Nat))) (NI : List (List (List Nat)))
  (EQ : List (List Nat)) (EW : List (List (List Nat))) (EE : List (List (List Nat)))
  (EF : List (List (List Nat))) (EP : List (List (List Nat)))

namespace CFSG.KD.B4AF

open CFSG.KC.B4A CFSG.KC.Y333

@[expose] noncomputable def tW (k t : Nat) : List Nat := (TW.getD k []).getD t []

@[expose] noncomputable def ev (k : Nat) (refs : List Nat) (x : Nat) : Nat :=
  evT CFSG.KD.B4A.LP (tW k) refs x

@[expose] noncomputable def evI (k : Nat) (refs : List Nat) (x : Nat) : Nat :=
  evTI CFSG.KD.B4A.LP (tW k) refs x

@[expose] noncomputable def evRecI (refs : List Nat) (x : Nat) : Nat :=
  List.rec (motive := fun _ => Nat → Nat) (fun x => x)
    (fun r _ ih x => ih (ev1 CFSG.KD.B4A.LP (Bool.rec (motive := fun _ => Nat)
      (wRev (CFSG.KD.B4A.RW (Nat.div r 2))) (CFSG.KD.B4A.RW (Nat.div r 2))
      (Nat.beq (Nat.mod r 2) 1)) x)) refs x

@[expose] noncomputable def pg (k i : Nat) : List Nat := (PX.getD k []).getD i []

@[expose] noncomputable def powI (k : Nat) (g : List Nat) (e p : Nat) : Nat :=
  Bool.rec (motive := fun _ => Nat) (iter (ev k g) (Nat.sub 5 e) p) (iter (evI k g) e p)
    (Nat.ble e 2)

@[expose] noncomputable def normB (k : Nat) (n es : List Nat) : Bool :=
  belowAll (FA.getD k 0) fun i => fix5 fun p =>
    ev k n (ev k (pg k i) (evI k n (powI k (pg k 1) (es.getD (Nat.add (Nat.mul 2 i) 1) 0)
      (powI k (pg k 0) (es.getD (Nat.mul 2 i) 0) p))))

@[expose] noncomputable def fixB (k : Nat) (n bs : List Nat) (m : Nat) : Bool :=
  belowAll m fun i => Nat.beq (ev k n (bs.getD i 0)) (bs.getD i 0)

@[expose] noncomputable def refsOK (j : Nat) (refs : List Nat) : Bool :=
  List.rec (motive := fun _ => Bool) true
    (fun r _ acc => andB (andB (isStab (dKind (CFSG.KD.B4A.RD (Nat.div r 2))))
      (Nat.beq (dN2 (CFSG.KD.B4A.RD (Nat.div r 2))) j)) acc) refs

@[expose] noncomputable def tChk (k : Nat) : Bool :=
  belowAll (TW.getD k []).length fun t =>
    andB (lettersOK (tW k t)) (andB (refsOK (FJ.getD k 0) ((TR.getD k []).getD t []))
      (fix5 fun x => evL CFSG.KD.B4A.LP (tW k t) (evRecI ((TR.getD k []).getD t []) x)))

@[expose] noncomputable def pChk (k : Nat) : Bool :=
  andB (fix5 (iter (ev k (pg k 0)) 5))
  (andB (notB (Nat.beq (ev k (pg k 0) ((PQ.getD k []).getD 0 0)) ((PQ.getD k []).getD 0 0)))
  (Bool.rec (motive := fun _ => Bool) (Nat.beq (FA.getD k 0) 1)
    (andB (fix5 (iter (ev k (pg k 1)) 5))
    (andB (fix5 fun p => ev k (pg k 0) (ev k (pg k 1) (evI k (pg k 0) (evI k (pg k 1) p))))
      (belowAll 5 fun i => notB (Nat.beq
        (ev k (pg k 1) (iter (evI k (pg k 0)) i ((PQ.getD k []).getD (Nat.succ i) 0)))
        ((PQ.getD k []).getD (Nat.succ i) 0)))))
    (Nat.beq (FA.getD k 0) 2)))

@[expose] noncomputable def lg (k l : Nat) : List (List Nat) := (NG.getD k []).getD l []

@[expose] noncomputable def levelChk (k l : Nat) : Bool :=
  andB (belowAll (lg k l).length fun g =>
      andB (normB k ((lg k l).getD g []) (((NE.getD k []).getD l []).getD g []))
        (fixB k ((lg k l).getD g []) (NB.getD k []) l))
    (orbListChk (ev k) (lg k l) ((NB.getD k []).getD l 0) ((NP.getD k []).getD l [])
      ((NQ.getD k []).getD l []) ((NI.getD k []).getD l []))

@[expose] noncomputable def ew (k e : Nat) : List Nat := (EW.getD k []).getD e []

@[expose] noncomputable def finChk (k e : Nat) : Bool :=
  andB (normB k (ew k e) ((EE.getD k []).getD e []))
  (andB (fixB k (ew k e) (NB.getD k []) (NB.getD k []).length)
  (andB (fix5 (iter (ev k (ew k e)) ((EQ.getD k []).getD e 0)))
    (belowAll ((EF.getD k []).getD e []).length fun i =>
      notB (Nat.beq
        (iter (ev k (ew k e)) (Nat.div ((EQ.getD k []).getD e 0) (((EF.getD k []).getD e []).getD i 0))
          (((EP.getD k []).getD e []).getD i 0))
        (((EP.getD k []).getD e []).getD i 0)))))

@[expose] noncomputable def orbProd (k : Nat) : Nat :=
  ((NP.getD k []).map List.length).foldr Nat.mul 1

@[expose] noncomputable def ordLcm (k : Nat) : Nat := (EQ.getD k []).foldr Nat.lcm 1

@[expose] noncomputable def nodeChk (k : Nat) : Bool :=
  andB (tChk k) (andB (pChk k)
  (andB (belowAll (NB.getD k []).length fun l => levelChk k l)
  (andB (belowAll (EQ.getD k []).length fun e => finChk k e)
    (Nat.beq (FB.getD k 0) (Nat.mul (orbProd k) (ordLcm k))))))

end CFSG.KD.B4AF

end
