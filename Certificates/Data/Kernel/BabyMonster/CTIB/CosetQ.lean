module

public import CFSG.Certificates.Kernel.BabyMonster.Native.Q23
public import CFSG.Certificates.Kernel.BabyMonster.Native.Census

public section

namespace CFSG.KC.BM.CosetQ

open CFSG.KC.BM

@[expose] noncomputable def allLt (n : Nat) (f : Nat → Bool) : Bool :=
  Nat.rec (motive := fun _ => Bool) true (fun i ih => andB ih (f i)) n

@[expose] noncomputable def betaK (LO a b : Nat) : Nat :=
  par32 (Nat.land (xorFields LO (Nat.land a (nat_lit 4194303))) b)

@[expose] noncomputable def relOK (LO A : Nat) : Bool :=
  allLt (nat_lit 22) (fun i => (fun a => andB (Nat.beq (Nat.shiftRight a (nat_lit 23)) (nat_lit 0))
    (andB (Nat.beq (betaK LO a a) (nat_lit 0))
      (allLt (nat_lit 22) (fun j => (fun b => Nat.beq (Nat.xor (betaK LO a b) (betaK LO b a))
          (Nat.xor (betaK LO (Nat.shiftLeft (nat_lit 1) i) (Nat.shiftLeft (nat_lit 1) j))
            (betaK LO (Nat.shiftLeft (nat_lit 1) j) (Nat.shiftLeft (nat_lit 1) i))))
        (fld32 A j))))) (fld32 A i))

@[expose] noncomputable def qinvK (LO e : Nat) : Nat := mulQ LO (mulQ LO e e) e

@[expose] noncomputable def conjK (LO A e n : Nat) : Nat :=
  mulQ LO (autQ LO A (qinvK LO e)) (mulQ LO n e)

@[expose] noncomputable def isInvK (LO A w n : Nat) : Bool :=
  Nat.beq (mulQ LO w (mulQ LO (autQ LO A n) n)) (nat_lit 0)

@[expose] noncomputable def setupOK (LO A k Bs T : Nat) : Bool :=
  andB (relOK LO A) (andB (Nat.beq (compAut LO A A) (id32 (nat_lit 22)))
    (allLt (nat_lit 22) (fun t => (fun b => (fun c =>
      andB (Nat.beq (xorFields T b) (Nat.shiftLeft (nat_lit 1) t))
      (andB (Nat.beq (xorFields Bs c) (Nat.shiftLeft (nat_lit 1) t))
      (andB (Nat.beq (Nat.shiftRight b (nat_lit 22)) (nat_lit 0))
      (andB (Nat.beq (Nat.shiftRight c (nat_lit 22)) (nat_lit 0))
        (Nat.beq (Nat.xor (Nat.land (autQ LO A b) (nat_lit 4194303)) b)
          (Bool.rec (motive := fun _ => Nat) (fld32 Bs (Nat.sub t (Nat.sub (nat_lit 22) k)))
            (nat_lit 0) (Nat.blt t (Nat.sub (nat_lit 22) k))))))))
      (fld32 T t)) (fld32 Bs t))))

@[expose] noncomputable def repOf (PT p : Nat) : Nat := Nat.land (fld32 PT p) (nat_lit 8388607)

@[expose] noncomputable def labOf (PT p : Nat) : Nat :=
  Nat.land (Nat.shiftRight (fld32 PT p) (nat_lit 23)) (nat_lit 7)

@[expose] noncomputable def splitOf (PT p : Nat) : Nat :=
  Nat.land (Nat.shiftRight (fld32 PT p) (nat_lit 26)) (nat_lit 1)

@[expose] noncomputable def witOf (PT p : Nat) : Nat := Nat.shiftRight (fld32 PT p) (nat_lit 27)

@[expose] noncomputable def vixOf (k T PT p : Nat) : Nat :=
  Nat.shiftRight (xorFields T (Nat.land (repOf PT p) (nat_lit 4194303))) k

@[expose] noncomputable def vOK (LO A w k Bs T VT PT npts j : Nat) : Bool :=
  (fun ent => (fun spl => (fun p0 => (fun p1 =>
    Bool.rec (motive := fun _ => Bool)
      (notB (isInvK LO A w (xorFields Bs (Nat.shiftLeft j k))))
      (andB (Nat.blt p0 npts) (andB (Nat.beq (vixOf k T PT p0) j)
        (andB (Nat.beq (splitOf PT p0) spl)
          (Bool.rec (motive := fun _ => Bool) true
            (andB (Nat.blt p1 npts) (andB (Nat.beq (vixOf k T PT p1) j)
              (andB (Nat.beq (splitOf PT p1) (nat_lit 1)) (notB (Nat.beq p0 p1)))))
            (Nat.beq spl (nat_lit 1))))))
      (Nat.beq (Nat.land ent (nat_lit 1)) (nat_lit 1)))
    (Nat.land (Nat.shiftRight ent (nat_lit 12)) (nat_lit 1023)))
    (Nat.land (Nat.shiftRight ent (nat_lit 2)) (nat_lit 1023)))
    (Nat.land (Nat.shiftRight ent (nat_lit 1)) (nat_lit 1)))
  (fld32 VT j)

@[expose] noncomputable def cntV (VT n : Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat) (nat_lit 0)
    (fun j acc => Nat.add acc (Nat.land (fld32 VT j) (nat_lit 1))) n

@[expose] noncomputable def incOK (PT n : Nat) : Bool :=
  allLt (Nat.sub n (nat_lit 1)) (fun p => Nat.blt (repOf PT p) (repOf PT (Nat.succ p)))

@[expose] noncomputable def ptOK (LO A w k Bs T PT p : Nat) : Bool :=
  (fun rep => andB (isInvK LO A w rep)
    (andB (Nat.beq (Nat.shiftRight (xorFields T (Nat.land rep (nat_lit 4194303)))
        (Nat.sub (nat_lit 22) k)) (nat_lit 0))
      (Bool.rec (motive := fun _ => Bool)
        ((fun wit => andB (Nat.blt wit (Nat.sub (nat_lit 22) k))
          (andB (Nat.beq (conjK LO A (fld32 Bs wit) rep) (Nat.xor rep (nat_lit 4194304)))
          (andB (Nat.blt rep (nat_lit 4194304))
            (allLt (Nat.shiftLeft (nat_lit 1) k) (fun c => Nat.ble rep (Nat.xor rep (xorFields Bs c)))))))
          (witOf PT p))
        (andB (allLt (Nat.sub (nat_lit 22) k) (fun t => Nat.beq (conjK LO A (fld32 Bs t) rep) rep))
          (allLt (Nat.shiftLeft (nat_lit 1) k) (fun c =>
            Nat.ble rep (conjK LO A (xorFields Bs (Nat.shiftLeft c (Nat.sub (nat_lit 22) k))) rep))))
        (Nat.beq (splitOf PT p) (nat_lit 1)))))
  (repOf PT p)

@[expose] noncomputable def ptIdxK (LO A k Bs T VT PT u : Nat) : Nat :=
  (fun c => (fun ent => (fun p0 =>
    Bool.rec (motive := fun _ => Nat) (nat_lit 1024)
      (Bool.rec (motive := fun _ => Nat)
        ((fun r0 => Bool.rec (motive := fun _ => Nat)
            (Nat.land (Nat.shiftRight ent (nat_lit 12)) (nat_lit 1023)) p0
            (Nat.beq (conjK LO A (xorFields Bs (Nat.shiftLeft (Nat.land (Nat.xor c
                (xorFields T (Nat.land r0 (nat_lit 4194303))))
                (Nat.sub (Nat.shiftLeft (nat_lit 1) k) (nat_lit 1))) (Nat.sub (nat_lit 22) k))) r0) u))
          (repOf PT p0))
        p0
        (Nat.beq (Nat.land (Nat.shiftRight ent (nat_lit 1)) (nat_lit 1)) (nat_lit 0)))
      (andB (Nat.beq (Nat.shiftRight c (Nat.sub (nat_lit 22) k)) (nat_lit 0))
        (Nat.beq (Nat.land ent (nat_lit 1)) (nat_lit 1))))
    (Nat.land (Nat.shiftRight ent (nat_lit 2)) (nat_lit 1023)))
    (fld32 VT (Nat.shiftRight c k)))
  (xorFields T (Nat.land u (nat_lit 4194303)))

@[expose] noncomputable def labOfK (LO A k Bs T VT PT u : Nat) : Nat :=
  (fun i => Bool.rec (motive := fun _ => Nat) (labOf PT i) (nat_lit 8) (Nat.beq i (nat_lit 1024)))
    (ptIdxK LO A k Bs T VT PT u)

@[expose] noncomputable def trOK (LO A k Bs T VT PT TR RT npts : Nat) (Gs Ds : List Nat) (off q : Nat) :
    Bool :=
  (fun e => Bool.rec (motive := fun _ => Bool)
    ((fun par => (fun j => andB (Nat.blt par npts) (andB (Nat.blt j (nat_lit 15))
        (andB (Nat.blt (Nat.shiftRight (fld32 TR par) (nat_lit 14)) (Nat.shiftRight e (nat_lit 14)))
          (Nat.beq (ptIdxK LO A k Bs T VT PT (mulQ LO (nthN Ds (Nat.add off j))
            (autQ LO (nthN Gs (Nat.add off j)) (repOf PT par)))) q))))
      (Nat.land (Nat.shiftRight e (nat_lit 10)) (nat_lit 15)))
      (Nat.sub (Nat.land e (nat_lit 1023)) (nat_lit 1)))
    (andB (Nat.beq (fld32 RT (labOf PT q)) q)
      (allLt q (fun q' => notB (Nat.beq (labOf PT q') (labOf PT q)))))
    (Nat.beq e (nat_lit 0)))
  (fld32 TR q)

@[expose] noncomputable def closOK (LO A k Bs T VT PT : Nat) (Gs Ds : List Nat) (off q : Nat) :
    Bool :=
  (fun p => (fun t => Nat.beq
      (labOfK LO A k Bs T VT PT (mulQ LO (nthN Ds t) (autQ LO (nthN Gs t) (repOf PT p))))
      (labOf PT p))
    (Nat.add off (Nat.mod q (nat_lit 15))))
  (Nat.div q (nat_lit 15))

@[expose] noncomputable def dOK (LO A G d : Nat) : Bool :=
  andB (Nat.blt d (nat_lit 8388608)) (allLt (nat_lit 22) (fun i =>
    Nat.beq (mulQ LO d (autQ LO G (fld32 A i))) (mulQ LO (autQ LO A (fld32 G i)) d)))

@[expose] noncomputable def ctabK (LO S : Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat) (nat_lit 0)
    (fun i acc => Nat.lor acc (Nat.shiftLeft
      (Nat.rec (motive := fun _ => Nat) (nat_lit 0)
        (fun j acc' => Nat.lor acc' (Bool.rec (motive := fun _ => Nat) (nat_lit 0)
          (Nat.shiftLeft (betaK LO (fld32 S i) (fld32 S j)) j) (Nat.blt i j))) (nat_lit 22))
      (Nat.mul (nat_lit 32) i))) (nat_lit 22)

@[expose] noncomputable def imgF (S C a : Nat) : Nat :=
  (fun q => (fun x => Nat.lor (Nat.land x (nat_lit 4194303))
      (Nat.shiftLeft (Nat.land (Nat.xor (Nat.xor (Nat.shiftRight a (nat_lit 22)) (Nat.shiftRight x (nat_lit 22)))
        (par32 (Nat.land (xorFields C q) q))) (nat_lit 1)) (nat_lit 22)))
    (xorFields S q)) (Nat.land a (nat_lit 4194303))

@[expose] noncomputable def compAutF (S C A : Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat → Nat → Nat → Nat) (fun _ _ acc => acc)
    (fun _ ih Ar sh acc => forceB (Nat.lor acc (Nat.shiftLeft (imgF S C (Nat.land Ar (nat_lit 4294967295))) sh))
      (fun a => ih (Nat.shiftRight Ar (nat_lit 32)) (Nat.add sh (nat_lit 32)) a))
    (nat_lit 22) A (nat_lit 0) (nat_lit 0)

@[expose] noncomputable def wordKF (S CT : List Nat) (st : List Nat) (acc : Nat) : Nat :=
  List.rec (motive := fun _ => Nat → Nat) (fun a => a)
    (fun s _ ih a => forceB (compAutF (nthN S s) (nthN CT s) a) (fun a' => ih a')) st acc

@[expose] noncomputable def wOK (LO : Nat) (S CT : List Nat) (Steps : List (List Nat))
    (Gs : List Nat) (t : Nat) : Bool :=
  andB (Nat.beq (wordKF S CT (nthLL Steps t) (id32 (nat_lit 22))) (nthN Gs t))
    (relOK LO (nthN Gs t))

@[expose] noncomputable def ctOK (LO : Nat) (S CT : List Nat) (s : Nat) : Bool :=
  Nat.beq (ctabK LO (nthN S s)) (nthN CT s)

@[expose] noncomputable def symsOK (LO : Nat) (S CT : List Nat) : Bool :=
  andB (relOK LO (nthN S 0)) (andB (relOK LO (nthN S 1))
    (andB (Nat.beq (compAut LO (nthN S 0) (nthN S 0)) (id32 (nat_lit 22)))
    (andB (allLt (nat_lit 11) (fun r =>
        Nat.beq (compAut LO (nthN S (Nat.succ r)) (nthN S 1)) (nthN S (Nat.add r (nat_lit 2)))))
    (andB (Nat.beq (Nat.rec (motive := fun _ => Nat) (id32 (nat_lit 22))
        (fun _ acc => compAutF (nthN S 1) (nthN CT 1) acc) (nat_lit 47)) (nthN S 13))
      (allLt (nat_lit 3) (fun r => Nat.beq (compAut LO (nthN S (Nat.add r (nat_lit 13))) (nthN S 13))
        (nthN S (Nat.add r (nat_lit 14)))))))))

end CFSG.KC.BM.CosetQ

end
