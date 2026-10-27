module

public import Certificates.Data.Kernel.LocalQT.R9
public import Certificates.Data.Kernel.LocalQT.Small

public section

namespace CFSG.KC.LQT.R

open CFSG.KC.Ord CFSG.KC.LQT.P CFSG.KC.LQT.S

@[expose] noncomputable def fst20 (w : Nat) : Nat := Nat.land w 1048575

@[expose] noncomputable def snd20 (w : Nat) : Nat := Nat.shiftRight w 20

@[expose] noncomputable def commK (x y : Nat) : Bool := Nat.beq (mulK x y) (mulK y x)

@[expose] noncomputable def invoK (x : Nat) : Bool :=
  andB (notB (Nat.beq x oneK)) (Nat.beq (mulK x x) oneK)

@[expose] noncomputable def headL (l : List Nat) : Nat :=
  List.rec (motive := fun _ => Nat) 0 (fun x _ _ => x) l

@[expose] noncomputable def tailL (l : List Nat) : List Nat :=
  List.rec (motive := fun _ => List Nat) [] (fun _ xs _ => xs) l

@[expose] noncomputable def allLL (l : List (List Nat)) (f : List Nat → Bool) : Bool :=
  List.rec (motive := fun _ => Bool) true (fun x _ ih => andB (f x) ih) l

@[expose] noncomputable def anyLL (l : List (List Nat)) (f : List Nat → Bool) : Bool :=
  List.rec (motive := fun _ => Bool) false (fun x _ ih => orB (f x) ih) l

@[expose] noncomputable def c4041 (X1 U0 D2 : Nat) (TL w2 : List Nat) (cent : List (List Nat)) :
    Bool := allBs
  [allL w2 (fun w => andB (slOK (snd20 w)) (Nat.beq (mulK (fst20 w) (cofK (snd20 w))) (snd20 w))),
   allLL cent (fun e => allLL cent fun e2 => impB (commK (headL e) (headL e2))
     (anyL (tailL e) fun bw => Nat.beq (fst20 bw) (headL e2))),
   allLL cent (fun e => andB (invoK (headL e)) (allL (tailL e) fun bw => invoK (fst20 bw))),
   allLL cent (fun e => allL (tailL e) fun bw => allL (tailL e) fun cw =>
     impB (commK (fst20 bw) (fst20 cw)) (impB (notB (Nat.beq (headL e) (fst20 bw)))
       (impB (notB (Nat.beq (fst20 cw) (headL e))) (impB (notB (Nat.beq (fst20 cw) (fst20 bw)))
         (Nat.beq (fst20 cw) (mulK (headL e) (fst20 bw))))))),
   allLL cent (fun e => allL (tailL e) fun bw => impB (notB (Nat.beq (headL e) (fst20 bw)))
     (andB (slOK (snd20 bw)) (andB (Nat.beq (mulK (snd20 bw) U0) (mulK (headL e) (snd20 bw)))
       (Nat.beq (mulK (snd20 bw) D2) (mulK (fst20 bw) (snd20 bw)))))),
   Nat.beq (mulK D2 D2) oneK, commK U0 D2, notB (Nat.beq D2 oneK), notB (Nat.beq U0 D2),
   Nat.beq (cofK U0) U0, Nat.beq (cofK D2) D2]

@[expose] noncomputable def sl4041 (X1 U0 D2 : Nat) (TL w2 : List Nat) (cent : List (List Nat))
    (r : Nat) : Bool := allBs
  [notB (Nat.beq (mulK r X1) (mulK (cofK X1) r)),
   impB (Nat.beq (mulK r (cofK r)) oneK) (anyL w2 fun w => Nat.beq (fst20 w) r),
   impB (allL TL fun t => Nat.beq (mulK r (cofK t)) (mulK t r)) (Nat.beq (mulK r (cofK r)) U0),
   impB (invoK r) (anyLL cent fun e => Nat.beq (headL e) r),
   impB (commK r U0) (impB (commK r D2) (memL r [oneK, U0, D2, mulK U0 D2]))]

@[expose] noncomputable def evBK (A B : Nat) (w : List Bool) : Nat :=
  List.rec (motive := fun _ => Nat) oneK
    (fun c _ ih => mulK (Bool.rec (motive := fun _ => Nat) A B c) ih) w

@[expose] noncomputable def anyW (l : List (List Bool)) (f : List Bool → Bool) : Bool :=
  List.rec (motive := fun _ => Bool) false (fun x _ ih => orB (f x) ih) l

@[expose] noncomputable def c4145 (U0 A B : Nat) (TL : List Nat) (W : List (List Bool))
    (wu : List Nat) : Bool := allBs
  [notB (Nat.beq U0 oneK), Nat.beq (mulK U0 U0) oneK, Nat.beq cntSL 5616,
   allL wu (fun w => andB (slOK (snd20 w)) (Nat.beq (mulK (snd20 w) U0) (mulK (fst20 w) (snd20 w)))),
   allL TL (fun t => anyW W fun w => Nat.beq t (evBK A B w)),
   Nat.beq U0 (evBK A B [true, false, true, false]),
   notB (Nat.beq A oneK), notB (Nat.beq B oneK), notB (Nat.beq (pwK (mulK A B) 2) oneK),
   Nat.beq (pwK (mulK A B) 4) oneK,
   Nat.ble (List.rec (motive := fun _ => Nat) 0 (fun p _ ih => Nat.add ih
       (List.rec (motive := fun _ => Nat) 0 (fun q _ ih2 => Nat.add ih2
         (Bool.rec (motive := fun _ => Nat) 0 1 (allBs [notB (Nat.beq p oneK),
           notB (Nat.beq q oneK), notB (Nat.beq (pwK (mulK p q) 2) oneK),
           Nat.beq (pwK (mulK p q) 4) oneK]))) TL)) TL) 24]

@[expose] noncomputable def sl4145 (U0 : Nat) (TL wu : List Nat) (r : Nat) : Bool := allBs
  [iffB (andB (commK r U0) (Nat.beq (mulK r (mulK r r)) oneK)) (memL r TL),
   impB (commK r U0) (impB (allL TL fun t => commK t r) (orB (Nat.beq r oneK) (Nat.beq r U0))),
   impB (allL TL fun t => commK r t) (orB (Nat.beq r oneK) (Nat.beq r U0)),
   impB (invoK r) (anyL wu fun w => Nat.beq (fst20 w) r)]

@[expose] noncomputable def transK (x : Nat) : Nat :=
  mk9 fun k => ent x (Nat.add (Nat.mul 3 (Nat.mod k 3)) (Nat.div k 3))

@[expose] noncomputable def conjK (g x : Nat) : Nat := mulK (mulK g x) (transK (cofK g))

@[expose] noncomputable def filterL (l : List Nat) (f : Nat → Bool) : List Nat :=
  List.rec (motive := fun _ => List Nat) []
    (fun x _ ih => Bool.rec (motive := fun _ => List Nat) ih (List.cons x ih) (f x)) l

@[expose] noncomputable def eqL (l m : List Nat) : Bool :=
  List.rec (motive := fun _ => List Nat → Bool)
    (fun m => List.rec (motive := fun _ => Bool) true (fun _ _ _ => false) m)
    (fun x _ ih m => List.rec (motive := fun _ => Bool) false
      (fun y ys _ => andB (Nat.beq x y) (ih ys)) m) l m

@[expose] noncomputable def getL (l : List Nat) (i : Nat) : Nat :=
  List.rec (motive := fun _ => Nat → Nat) (fun _ => 0)
    (fun x _ ih j => Bool.rec (motive := fun _ => Nat) (ih (Nat.sub j 1)) x (Nat.beq j 0)) l i

@[expose] noncomputable def maskL (l : List Nat) (f : Nat → Bool) : Nat :=
  List.rec (motive := fun _ => Nat → Nat) (fun _ => 0)
    (fun x _ ih i => Nat.add (Bool.rec (motive := fun _ => Nat) 0 (Nat.shiftLeft 1 i) (f x))
      (ih (Nat.succ i))) l 0

@[expose] noncomputable def c4048 (SA SB : Nat) (LP LI LW PR : List Nat) : Bool := allBs
  [Nat.beq (detK SA) 1, Nat.beq (detK SB) 1, Nat.beq (pwK SA 8) oneK, Nat.beq (mulK SB SB) oneK,
   Nat.beq (mulK SB SA) (mulK (pwK SA 3) SB), distinctL LP, Nat.beq (lenL LP) 16,
   memL oneK LP, memL SA LP, memL SB LP,
   allL LP (fun x => allL LP fun y => memL (mulK x y) LP), allL LP (fun x => Nat.beq (pwK x 16) oneK),
   allL LW (fun w => Nat.beq (detK w) 1),
   eqL LI (filterL LP invoK), Nat.blt (lenL LI) 9,
   allN (lenL LI) (fun i => allN (lenL LI) fun j =>
     iffB (andB (notB (Nat.beq (getL LI i) (getL LI j))) (commK (getL LI i) (getL LI j)))
       (memL (Nat.add i (Nat.mul 8 j)) PR)),
   allL PR (fun p => letB (getL LI (Nat.mod p 8)) fun t => letB (getL LI (Nat.div p 8)) fun s =>
     anyL LW fun w => allBs [Nat.beq (pwK w 3) oneK, notB (Nat.beq w oneK),
       anyL [oneK, t, s, mulK t s] (fun u => Nat.beq (mulK w t) (mulK u w)),
       anyL [oneK, t, s, mulK t s] (fun u => Nat.beq (mulK w s) (mulK u w))])]

@[expose] noncomputable def sl4048 (SA SB : Nat) (LP LI PR : List Nat) (g : Nat) : Bool :=
   letB (cofK SA) fun CA => letB (cofK SB) fun CB => letB (transK (cofK g)) fun gi =>
     letB (maskL LI fun t => commK g t) fun cm =>
     letB (maskL LI fun t => Nat.beq (mulK (mulK g (cofK t)) gi) t) fun fm =>
     letB (mulK (mulK g CA) gi) fun a2 => letB (mulK (mulK g CB) gi) fun b2 =>
     allBs
     [impB (memL (mulK (mulK g SA) gi) LP) (impB (memL (mulK (mulK g SB) gi) LP) (memL g LP)),
      allL PR (fun p => letB (Nat.mod p 8) fun i => letB (Nat.div p 8) fun j =>
        impB (andB (Nat.blt 0 (Nat.land cm (Nat.shiftLeft 1 i)))
          (Nat.blt 0 (Nat.land cm (Nat.shiftLeft 1 j))))
          (memL g [oneK, getL LI i, getL LI j, mulK (getL LI i) (getL LI j)])),
      allL PR (fun p => letB (Nat.mod p 8) fun i => letB (Nat.div p 8) fun j =>
        impB (andB (Nat.blt 0 (Nat.land fm (Nat.shiftLeft 1 i)))
          (Nat.blt 0 (Nat.land fm (Nat.shiftLeft 1 j))))
          (andB (memL a2 LP) (memL b2 LP))),
      notB (andB (Nat.beq a2 SA) (Nat.beq b2 SB))]

@[expose] noncomputable def pwB (x e nb : Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat) oneK
    (fun k acc => CFSG.KC.Loop.strictN (mulK acc acc) fun a2 =>
      Bool.rec (motive := fun _ => Nat) a2 (mulK a2 x)
        (Nat.blt 0 (Nat.land e (Nat.shiftLeft 1 (Nat.sub (Nat.sub nb 1) k))))) nb

@[expose] noncomputable def getLL (l : List (List Nat)) (i : Nat) : List Nat :=
  List.rec (motive := fun _ => Nat → List Nat) (fun _ => [])
    (fun x _ ih j => Bool.rec (motive := fun _ => List Nat) (ih (Nat.sub j 1)) x (Nat.beq j 0)) l i

@[expose] noncomputable def sl4056 (G R WO : List Nat) (CI : List (List Nat)) (T0 : Nat)
    (WT S0 C0 : List Nat) (x : Nat) : Bool := allBs
  [orB (Nat.beq x oneK) (anyL G fun g => notB (commK x g)),
   impB (andB (notB (Nat.beq x oneK)) (Nat.beq (pwB x 351 9) oneK))
     (anyL WO fun w => Nat.beq (fst20 w) x),
   allN (lenL R) (fun i => impB (commK x (getL R i)) (andB
     (impB (invoK x) (memL x (getLL CI i)))
     (notB (andB (Nat.beq (pwK x 4) oneK) (notB (Nat.beq (pwK x 2) oneK)))))),
   impB (invoK x) (anyL WT fun w => Nat.beq (fst20 w) x),
   impB (Nat.beq (mulK x x) T0) (memL x S0),
   impB (commK x T0) (memL x C0)]

@[expose] noncomputable def c4056 (G R WO : List Nat) (CI : List (List Nat)) (T0 : Nat)
    (WT S0 C0 : List Nat) : Bool := allBs
  [allL G slOK,
   allL WO (fun w => andB (slOK (Nat.land (snd20 w) 1048575))
     (Nat.beq (conjK (Nat.land (snd20 w) 1048575) (getL R (Nat.shiftRight w 40))) (fst20 w))),
   allL R (fun r => andB (notB (Nat.beq r oneK)) (Nat.beq (pwB r 351 9) oneK)),
   Nat.beq (lenL R) (List.rec (motive := fun _ => Nat) 0 (fun _ _ ih => Nat.succ ih) CI),
   allLL CI (fun l => allL l fun t => allL l fun s => impB (notB (Nat.beq t s)) (notB (commK t s))),
   invoK T0, slOK T0,
   allL WT (fun w => andB (slOK (snd20 w)) (Nat.beq (conjK (snd20 w) T0) (fst20 w))),
   allL S0 (fun y => andB (slOK y) (Nat.beq (mulK y y) T0)),
   notB (Nat.beq (lenL S0) 0), distinctL (oneK :: T0 :: S0), Nat.ble 3 (lenL S0),
   allL S0 (fun y => allL S0 fun y' => letB (mulK y y') fun p =>
     orB (Nat.beq p oneK) (orB (Nat.beq p T0) (Nat.beq (mulK p p) T0))),
   allL C0 (fun c => andB (slOK c) (commK c T0)),
   allL C0 (fun c => orB (orB (Nat.beq c oneK) (orB (Nat.beq c T0) (Nat.beq (mulK c c) T0)))
     (anyL C0 fun w => notB (Nat.beq (pwB (mulK (transK (cofK c)) (mulK (mulK w c)
       (transK (cofK w)))) 16 5) oneK)))]

end CFSG.KC.LQT.R

end
