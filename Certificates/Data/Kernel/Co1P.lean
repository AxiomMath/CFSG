module

public import Certificates.Data.Kernel.Co1BW
public import Certificates.Data.Kernel.TreeK
public import CFSG.Certificates.Kernel.Common.Loop
public import Certificates.Data.Kernel.Griess13.Packed

public section

namespace CFSG.KC.Co1P

open CFSG.KC.Loop CFSG.KC.Co1B CFSG.KC.Co1F2 CFSG.KLie.CT

@[expose] noncomputable def fieldsK (w per c : Nat) : List Nat :=
  Nat.rec (motive := fun _ => Nat → List Nat) (fun _ => List.nil)
    (fun _ ih c => List.cons (Nat.mod c (Nat.shiftLeft (nat_lit 1) w)) (ih (Nat.shiftRight c w))) per c

@[expose] noncomputable def masksK (w per : Nat) (chunks : List Nat) : List Nat :=
  List.rec (motive := fun _ => List Nat) List.nil (fun c _ ih => List.append (fieldsK w per c) ih)
    chunks

@[expose] noncomputable def bitsK (h m : Nat) (k : Nat) : Nat → List (Nat × Nat) :=
  Nat.rec (motive := fun _ => Nat → List (Nat × Nat)) (fun _ => List.nil)
    (fun _ ih l => Bool.rec (motive := fun _ => List (Nat × Nat)) (ih (Nat.succ l))
      (List.cons (Prod.mk h l) (ih (Nat.succ l))) (Nat.beq (Nat.land (Nat.shiftRight m l) 1) 1)) k

@[expose] noncomputable def recsFrom (w : Nat) (ms : List Nat) : Nat → List (Nat × Nat) :=
  List.rec (motive := fun _ => Nat → List (Nat × Nat)) (fun _ => List.nil)
    (fun m _ ih h => List.append (bitsK h m w (nat_lit 0))
      (Nat.rec (motive := fun _ => List (Nat × Nat)) (ih (nat_lit 0)) (fun n _ => ih (Nat.succ n))
        (Nat.succ h))) ms

@[expose] noncomputable def recsK (w : Nat) (ms : List Nat) : List (Nat × Nat) :=
  recsFrom w ms (nat_lit 0)

@[expose] noncomputable def hsAct (G : List Nat) (l h : Nat) : Nat := mulWK (getL (nat_lit 0) G l) h

@[expose] noncomputable def hisAct (Gi : List Nat) (l h : Nat) : Nat := mulWK h (getL (nat_lit 0) Gi l)

@[expose] noncomputable def walkAt (act : Nat → Nat → Nat) (ng root : Nat) (rs : List (Nat × Nat))
    (i : Nat) : Nat :=
  ((CFSG.KC.TreeK.treePts act ng root rs).1)[i]?.getD 0

@[expose] noncomputable def conjL (R : Nat) (HS : List Nat) : List Nat → List Nat :=
  List.rec (motive := fun _ => List Nat → List Nat) (fun _ => List.nil)
    (fun h _ ih HIS => List.rec (motive := fun _ => List Nat) List.nil
      (fun hi HIS' _ => List.cons (mulWK (mulWK h R) hi) (ih HIS')) HIS) HS

@[expose] noncomputable def ptsL (G Gi : List Nat) (ng R : Nat) (rs : List (Nat × Nat)) : List Nat :=
  conjL R (CFSG.KC.TreeK.treePts (hsAct G) ng oneK rs).1 (CFSG.KC.TreeK.treePts (hisAct Gi) ng oneK rs).1

@[expose] noncomputable def invsOK (G : List Nat) : List Nat → Bool :=
  List.rec (motive := fun _ => List Nat → Bool)
    (fun Gi => List.rec (motive := fun _ => Bool) true (fun _ _ _ => false) Gi)
    (fun g _ ih Gi => List.rec (motive := fun _ => Bool) false
      (fun gi Gi' _ => CFSG.KLie.CT.andB (Nat.beq (mulWK g gi) oneK) (ih Gi')) Gi) G

@[expose] noncomputable def modL (xs : List Nat) : List Nat :=
  List.rec (motive := fun _ => List Nat) List.nil
    (fun x _ ih => List.cons (Nat.mod x (Nat.shiftLeft (nat_lit 1) (nat_lit 576))) ih) xs

@[expose] noncomputable def orbChk (G Gi : List Nat) (ng R np : Nat) (rs : List (Nat × Nat)) : Bool :=
  Prod.rec (motive := fun _ => Bool) (fun HS okH => Prod.rec (motive := fun _ => Bool)
    (fun HIS okHi => CFSG.KLie.CT.andB (CFSG.KLie.CT.andB okH okHi) (CFSG.KLie.CT.andB (CFSG.KLie.CT.andB (Nat.beq (lenL G) ng) (invsOK G Gi))
      (CFSG.KC.TreeK.distinctK np (modL (conjL R HS HIS)))))
    (CFSG.KC.TreeK.treePts (hisAct Gi) ng oneK rs)) (CFSG.KC.TreeK.treePts (hsAct G) ng oneK rs)

inductive KT where
  | leaf : KT
  | node : KT → Nat → KT → KT

@[expose] noncomputable def memKT (x : Nat) (t : KT) : Bool :=
  KT.rec (motive := fun _ => Bool) false
    (fun _ k _ ihl ihr => Bool.rec (motive := fun _ => Bool)
      (Bool.rec (motive := fun _ => Bool) ihr true (Nat.beq x k)) ihl (Nat.blt x k)) t

@[expose] noncomputable def buildKT (d : Nat) : List Nat → KT × List Nat :=
  Nat.rec (motive := fun _ => List Nat → KT × List Nat) (fun xs => Prod.mk KT.leaf xs)
    (fun _ ih xs => Prod.rec (motive := fun _ => KT × List Nat)
      (fun L ys => List.rec (motive := fun _ => KT × List Nat) (Prod.mk L List.nil)
        (fun y zs _ => Prod.rec (motive := fun _ => KT × List Nat)
          (fun R rest => Prod.mk (KT.node L y R) rest) (ih zs)) ys) (ih xs)) d

@[expose] noncomputable def treeOf (d : Nat) (xs : List Nat) : KT :=
  Prod.rec (motive := fun _ => KT) (fun t _ => t) (buildKT d xs)

@[expose] noncomputable def treeAll (d : Nat) (xs : List Nat) : Bool :=
  Prod.rec (motive := fun _ => Bool)
    (fun _ rest => List.rec (motive := fun _ => Bool) true (fun _ _ _ => false) rest) (buildKT d xs)

@[expose] noncomputable def wordsC (W : List (List Int)) : List Char :=
  [';'].intercalate (W.map fun w => [','].intercalate (w.map CFSG.KC.G13.intC))

end CFSG.KC.Co1P

end
