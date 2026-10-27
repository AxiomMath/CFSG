module

public import CFSG.Certificates.Kernel.Orders.Cert

public section

namespace CFSG.KC.HNLocal

open CFSG.KC.Ord CFSG.KC.Loop

@[expose] noncomputable def letB (y : Nat) (k : Nat → Bool) : Bool :=
  Nat.rec (motive := fun _ => Bool) (k 0) (fun n _ => k (Nat.succ n)) y

@[expose] noncomputable def recC (M C r : Nat) : Nat :=
  Nat.land (Nat.shiftRight C (Nat.mul (nat_lit 400) r)) M

@[expose] noncomputable def recX (XC : Nat → Nat) (M k : Nat) : Nat :=
  recC M (XC (Nat.div k (nat_lit 133))) (Nat.mod k (nat_lit 133))

@[expose] noncomputable def rowL (RM Y r : Nat) : Nat :=
  Nat.land (Nat.shiftRight Y (Nat.mul (nat_lit 1729) r)) RM

@[expose] noncomputable def leafA (M C c : Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat) (nat_lit 0)
    (fun r acc => Nat.lor acc (Nat.shiftLeft (recC M C r) (Nat.mul (nat_lit 1729) r))) c

@[expose] noncomputable def mulC (L H CM3 RM A G : Nat) : Nat :=
  redP (nat_lit 13) L H (nat_lit 5) (nat_lit 9)
    (Nat.rec (motive := fun _ => Nat) (nat_lit 0)
      (fun k acc => Nat.add acc (Nat.mul (Nat.land (Nat.shiftRight A (Nat.mul (nat_lit 3) k)) CM3)
        (Nat.land (Nat.shiftRight G (Nat.mul (nat_lit 1729) k)) RM))) (nat_lit 133))

@[expose] noncomputable def sp1 (x m s : Nat) : Nat :=
  strictN (Nat.land x m) (fun a => Nat.lor (Nat.xor x a) (Nat.shiftLeft a s))

@[expose] noncomputable def mask (MS i : Nat) : Nat :=
  Nat.land (Nat.shiftRight MS (Nat.mul (nat_lit 1729) i))
    (Nat.sub (Nat.shiftLeft (nat_lit 1) (nat_lit 1729)) (nat_lit 1))

@[expose] noncomputable def spread (MS x : Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat) x
    (fun i acc => strictN acc (fun a => sp1 a (mask MS i)
      (Nat.mul (nat_lit 10) (Nat.shiftLeft (nat_lit 1) (Nat.sub (nat_lit 7) i))))) (nat_lit 8)

@[expose] noncomputable def maskB (i : Nat) : Nat :=
  (fun t => Nat.rec (motive := fun _ => Nat) (nat_lit 0)
    (fun j acc => nIf(Nat.beq (Nat.land (Nat.shiftRight j t) (nat_lit 1)) (nat_lit 1),
      Nat.lor acc (Nat.shiftLeft (nat_lit 7) (Nat.add (Nat.mul (nat_lit 3) j)
        (Nat.mul (nat_lit 10) (Nat.shiftLeft (Nat.shiftRight j (Nat.succ t)) (Nat.succ t))))), acc))
    (nat_lit 133)) (Nat.sub (nat_lit 7) i)

@[expose] noncomputable def masksOK (MS : Nat) : Bool :=
  bAnd(Nat.beq (Nat.shiftRight MS (Nat.mul (nat_lit 1729) (nat_lit 8))) (nat_lit 0),
    Nat.rec (motive := fun _ => Bool) true
      (fun i ih => bAnd(Nat.beq (mask MS i) (maskB i), ih)) (nat_lit 8))

@[expose] noncomputable def cmOK (CM3 M : Nat) : Bool :=
  bAnd(Nat.beq CM3 (Nat.rec (motive := fun _ => Nat) (nat_lit 0)
      (fun r acc => Nat.lor acc (Nat.shiftLeft (nat_lit 7) (Nat.mul (nat_lit 1729) r))) (nat_lit 133)),
    Nat.beq M (Nat.sub (Nat.shiftLeft (nat_lit 1) (nat_lit 399)) (nat_lit 1)))

@[expose] noncomputable def childF (h t : Nat) : Nat :=
  Nat.land (Nat.shiftRight h (Nat.add (nat_lit 30) (Nat.mul (nat_lit 9) t))) (nat_lit 511)

@[expose] noncomputable def childrenOK (h j c : Nat) : Nat → Nat → Bool :=
  Nat.rec (motive := fun _ => Nat → Bool) (fun _ => true)
    (fun _ ih t => letB (Nat.shiftRight (childF h t) (nat_lit 1)) (fun r =>
      bAnd(Nat.blt r (nat_lit 133),
        bAnd(Nat.blt (Nat.add (Nat.mul (nat_lit 133) j) r) (Nat.add c t), ih (Nat.succ t)))))

@[expose] noncomputable def gat (M C CH h : Nat) (fin : Nat → Nat → Nat → Nat → Bool) :
    Nat → Nat → Nat → Nat → Nat → Nat → Nat → Nat → Bool :=
  Nat.rec (motive := fun _ => Nat → Nat → Nat → Nat → Nat → Nat → Nat → Bool)
    (fun _ PA CA _ PB CB _ => fin PA CA PB CB)
    (fun _ ih t PA CA nA PB CB nB => letB (childF h t) (fun e =>
      letB (recC M C (Nat.shiftRight e (nat_lit 1))) (fun p => letB (recC M CH t) (fun x =>
      Bool.rec (motive := fun _ => Bool)
        (letB (Nat.lor PA (Nat.shiftLeft p (Nat.mul (nat_lit 1729) nA))) (fun PA' =>
          letB (Nat.lor CA (Nat.shiftLeft x (Nat.mul (nat_lit 1729) nA))) (fun CA' =>
            ih (Nat.succ t) PA' CA' (Nat.succ nA) PB CB nB)))
        (letB (Nat.lor PB (Nat.shiftLeft p (Nat.mul (nat_lit 1729) nB))) (fun PB' =>
          letB (Nat.lor CB (Nat.shiftLeft x (Nat.mul (nat_lit 1729) nB))) (fun CB' =>
            ih (Nat.succ t) PA CA nA PB' CB' (Nat.succ nB))))
        (Nat.beq (Nat.land e (nat_lit 1)) (nat_lit 1))))))

@[expose] noncomputable def chunk3 (XC : Nat → Nat) (c : Nat) : Nat :=
  (fun a => Nat.shiftRight (Nat.lor (XC a) (Nat.lor (Nat.shiftLeft (XC (Nat.succ a)) (nat_lit 53200))
      (Nat.shiftLeft (XC (Nat.succ (Nat.succ a))) (nat_lit 106400))))
    (Nat.mul (nat_lit 400) (Nat.sub c (Nat.mul (nat_lit 133) a))))
  (Nat.div c (nat_lit 133))

@[expose] noncomputable def spreadM (MSF : Nat → Nat) (x : Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat) x
    (fun i acc => strictN acc (fun a => sp1 a (MSF i)
      (Nat.mul (nat_lit 10) (Nat.shiftLeft (nat_lit 1) (Nat.sub (nat_lit 7) i))))) (nat_lit 8)

@[expose] noncomputable def msfOK (MS : Nat) (MSF : Nat → Nat) : Bool :=
  Nat.rec (motive := fun _ => Bool) true
    (fun i ih => bAnd(Nat.beq (MSF i) (Nat.rec (motive := fun _ => Nat) (nat_lit 0)
      (fun r acc => Nat.lor acc (Nat.shiftLeft (mask MS i) (Nat.mul (nat_lit 1729) r))) (nat_lit 133)), ih))
    (nat_lit 8)

@[expose] noncomputable def fixRows (RM Y nr : Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat) (nat_lit 0)
    (fun r acc => strictN (rowL RM Y r) (fun y => Nat.add acc (Nat.add
      (nIf(Nat.beq (Nat.land y (Nat.sub (Nat.shiftLeft (nat_lit 1) (nat_lit 728)) (nat_lit 1))) (nat_lit 0),
        nat_lit 1, nat_lit 0))
      (nIf(Nat.beq (Nat.land (Nat.shiftRight y (nat_lit 728))
          (Nat.sub (Nat.shiftLeft (nat_lit 1) (nat_lit 832)) (nat_lit 1))) (nat_lit 0),
        Nat.shiftLeft (nat_lit 1) (nat_lit 24), nat_lit 0))))) nr

@[expose] noncomputable def treeLeaf (XC TD MSF : Nat → Nat) (N M L H CM3 RM GA GB GFC j : Nat) : Nat :=
  strictN (XC j) (fun C =>
  strictN (TD j) (fun h =>
  strictN (Nat.land h (nat_lit 2097151)) (fun c =>
  strictN (Nat.land (Nat.shiftRight h (nat_lit 21)) (nat_lit 511)) (fun cnt =>
  nIf(bAnd(Nat.beq (Nat.add c cnt) (Nat.land (TD (Nat.succ j)) (nat_lit 2097151)),
      bAnd(Nat.ble cnt (nat_lit 266), bAnd(childrenOK h j c cnt (nat_lit 0),
        letB (chunk3 XC c) (fun CH =>
          gat M C CH h (fun PA CA PB CB =>
              bAnd(Nat.beq (mulC L H CM3 RM PA GA) (spreadM MSF CA),
                Nat.beq (mulC L H CM3 RM PB GB) (spreadM MSF CB)))
            cnt (nat_lit 0) (nat_lit 0) (nat_lit 0) (nat_lit 0) (nat_lit 0) (nat_lit 0) (nat_lit 0))))),
    strictN (Nat.sub N (Nat.mul (nat_lit 133) j)) (fun n0 =>
    strictN (nIf(Nat.ble n0 (nat_lit 133), n0, nat_lit 133)) (fun nr =>
      fixRows RM (mulC L H CM3 RM (leafA M C (nat_lit 133)) GFC) nr)),
    Nat.shiftLeft (nat_lit 1) (nat_lit 50))))))

@[expose] noncomputable def treeSum (XC TD MSF : Nat → Nat) (N M L H CM3 RM GA GB GFC lo n : Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat) (nat_lit 0)
    (fun i acc => strictN acc (fun a =>
      Nat.add a (treeLeaf XC TD MSF N M L H CM3 RM GA GB GFC (Nat.add lo i)))) n

@[expose] noncomputable def sig (SD : Nat → Nat) (i : Nat) : Nat :=
  Nat.land (Nat.shiftRight (SD (Nat.div i (nat_lit 133))) (Nat.mul (nat_lit 21) (Nat.mod i (nat_lit 133))))
    (nat_lit 2097151)

@[expose] noncomputable def sortGo (XC : Nat → Nat) (N M S S' m : Nat) : Nat → Nat → Nat → Bool :=
  Nat.rec (motive := fun _ => Nat → Nat → Bool) (fun _ _ => true)
    (fun _ ih t pk => bIf(Nat.blt (Nat.succ (Nat.add (Nat.mul (nat_lit 133) m) t)) N,
      letB (nIf(Nat.blt t (nat_lit 132),
          Nat.land (Nat.shiftRight S (Nat.mul (nat_lit 21) (Nat.succ t))) (nat_lit 2097151),
          Nat.land S' (nat_lit 2097151))) (fun b =>
      letB (recX XC M b) (fun kb =>
        bAnd(Nat.blt b N, bAnd(Nat.blt pk kb, ih (Nat.succ t) kb)))),
      true))

@[expose] noncomputable def sortLeaf (XC SD : Nat → Nat) (N M m : Nat) : Bool :=
  letB (SD m) (fun S => letB (SD (Nat.succ m)) (fun S' =>
  letB (Nat.land S (nat_lit 2097151)) (fun a =>
    bIf(Nat.blt (Nat.mul (nat_lit 133) m) N,
      bAnd(Nat.blt a N, sortGo XC N M S S' m (nat_lit 133) (nat_lit 0) (recX XC M a)),
      true))))

@[expose] noncomputable def sortRange (XC SD : Nat → Nat) (N M lo n : Nat) : Bool :=
  allBelow n (Nat.succ (Nat.div n (nat_lit 64))) (fun i => sortLeaf XC SD N M (Nat.add lo i))

@[expose] noncomputable def actLeaf (XC PI : Nat → Nat) (M MS L H CM3 RM nW G c nr : Nat) : Bool :=
  letB (mulC L H CM3 RM (leafA M (XC c) nr) G) (fun Y =>
    Nat.rec (motive := fun _ => Bool) true
      (fun r ih => bAnd(letB (PI (Nat.add (Nat.mul (nat_lit 133) c) r)) (fun k =>
        bAnd(Nat.blt k nW, Nat.beq (spread MS (recX XC M k)) (rowL RM Y r))), ih)) nr)

@[expose] noncomputable def fixVec (MS L H CM3 RM G x : Nat) : Bool :=
  Nat.beq (rowL RM (mulC L H CM3 RM x G) (nat_lit 0)) (spread MS x)

@[expose] noncomputable def elemOK (mul vm : Nat → Nat → Nat) (RP : Nat → Nat) (np ONE RM M tg : Nat) :
    Bool :=
  (fun k a m => Bool.rec (motive := fun _ => Bool)
      (Bool.rec (motive := fun _ => Bool)
        (Bool.rec (motive := fun _ => Bool) false
          (andB (Nat.blt a np) (andB (Nat.beq (Nat.mod m (nat_lit 2)) (nat_lit 1))
            (Nat.beq (powR mul ONE (mul M (RP a)) m) ONE)))
          (Nat.beq k (nat_lit 2)))
        (andB (Nat.blt a (nat_lit 133))
          (notB (Nat.beq (vm (rowL RM M a) M) (Nat.shiftLeft (nat_lit 1) (Nat.mul (nat_lit 13) a)))))
        (Nat.beq k (nat_lit 1)))
      (Nat.beq M ONE)
      (Nat.beq k (nat_lit 0)))
    (Nat.land tg (nat_lit 3)) (Nat.land (Nat.shiftRight tg (nat_lit 2)) (nat_lit 255))
    (Nat.shiftRight tg (nat_lit 10))

@[expose] noncomputable def cen (mul vm : Nat → Nat → Nat) (PC RP TG : Nat → Nat) (np ONE RM : Nat) :
    Nat → Nat → Nat → Nat → Bool :=
  Nat.rec (motive := fun _ => Nat → Nat → Nat → Bool)
    (fun _ M e => elemOK mul vm RP np ONE RM M (TG e))
    (fun _ ih k M e => bAnd(ih (Nat.succ k) M e,
      letB (mul M (PC k)) (fun M' => ih (Nat.succ k) M' (Nat.add e (Nat.shiftLeft (nat_lit 1) k)))))

@[expose] noncomputable def nfPre (mul : Nat → Nat → Nat) (PC : Nat → Nat) (ONE e : Nat) : Nat → Nat :=
  Nat.rec (motive := fun _ => Nat) ONE
    (fun i acc => strictN acc (fun a =>
      nIf(Nat.beq (Nat.land (Nat.shiftRight e i) (nat_lit 1)) (nat_lit 1), mul a (PC i), a)))

@[expose] noncomputable def cenAt (mul vm : Nat → Nat → Nat) (PC RP TG : Nat → Nat) (np ONE RM m k n : Nat) :
    Bool :=
  letB (nfPre mul PC ONE m k) (fun M => cen mul vm PC RP TG np ONE RM n k M m)

@[expose] noncomputable def trM (a : Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat) (nat_lit 0)
    (fun i acc => strictN acc (fun s => strictN (Nat.land (Nat.shiftRight a (Nat.mul (nat_lit 1729) i))
        (Nat.sub (Nat.shiftLeft (nat_lit 1) (nat_lit 1729)) (nat_lit 1))) (fun row =>
      Nat.rec (motive := fun _ => Nat) s
        (fun j acc2 => Nat.lor acc2 (Nat.shiftLeft (Nat.land (Nat.shiftRight row (Nat.mul (nat_lit 13) j))
            (nat_lit 8191)) (Nat.add (Nat.mul (nat_lit 1729) j) (Nat.mul (nat_lit 13) i)))) (nat_lit 133)))) (nat_lit 133)

@[expose] noncomputable def traceL (a : Nat) : Nat :=
  Nat.mod (Nat.rec (motive := fun _ => Nat) (nat_lit 0)
    (fun i acc => Nat.add acc (Nat.land (Nat.shiftRight a (Nat.mul (nat_lit 1742) i)) (nat_lit 8191)))
    (nat_lit 133)) (nat_lit 5)

end CFSG.KC.HNLocal

end
