module

public import Certificates.Data.Kernel.KDense.Twins

public section

namespace CFSG.KC.KDense

open CFSG.KC CFSG.KC.MonsterConv.Perm CFSG.KC.Loop

@[expose] noncomputable def wK (k : Nat) : Nat := Nat.shiftLeft (nat_lit 1) k

@[expose] noncomputable def stBit (k i : Nat) : Nat :=
  Bool.rec (motive := fun _ => Nat) (Nat.sub (Nat.add i (nat_lit 1)) k)
    (Nat.sub (Nat.sub k (nat_lit 1)) i) (Nat.blt i k)

@[expose] noncomputable def netOK (k N : Nat) : Bool :=
  andB (Nat.blt N (Nat.shiftLeft (nat_lit 1) (Nat.mul (Nat.sub (Nat.mul (nat_lit 2) k) (nat_lit 1)) (wK k))))
    (Nat.rec (motive := fun _ => Bool) true
      (fun i ih => andB (Nat.beq (Nat.land (Nat.land (Nat.shiftRight N (Nat.mul i (wK k))) (ones (wK k)))
        (idPlane (wK k) (stBit k i))) (nat_lit 0)) ih)
      (Nat.sub (Nat.mul (nat_lit 2) k) (nat_lit 1)))

@[expose] noncomputable def netP (S k n N x : Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat → Nat) (fun y => y)
    (fun j ih y => strictN
      ((fun i => dsw (stageShift k i) (repP S n (Nat.land (Nat.shiftRight N (Nat.mul i S)) (ones S))) y)
        (Nat.sub (Nat.sub (Nat.mul (nat_lit 2) k) (nat_lit 2)) j)) ih)
    (Nat.sub (Nat.mul (nat_lit 2) k) (nat_lit 1)) x

@[expose] noncomputable def mux (S m x y : Nat) : Nat :=
  Nat.lor (Nat.land m x) (Nat.land (Nat.xor (ones S) m) y)

@[expose] noncomputable def setPl (S b y X : Nat) : Nat :=
  Nat.lor (Nat.xor X (Nat.shiftLeft (plane S b X) (Nat.mul b S))) (Nat.shiftLeft y (Nat.mul b S))

@[expose] noncomputable def eq5 (S o v : Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat) (ones S)
    (fun t acc => Nat.land acc (Bool.rec (motive := fun _ => Nat) (clr S (Nat.add o t)) (idPlane S (Nat.add o t))
      (Nat.beq (bitN v t) (nat_lit 1)))) (nat_lit 5)

@[expose] noncomputable def lookP (S o P : Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat) (nat_lit 0)
    (fun c acc => (fun e => Nat.xor acc (Nat.rec (motive := fun _ => Nat) (nat_lit 0)
        (fun b acc2 => Nat.lor acc2 (Nat.shiftLeft (selB (bitN (pe P c) b) e) (Nat.mul b S))) (nat_lit 5)))
      (eq5 S o c)) (nat_lit 24)

@[expose] noncomputable def listPack (l : List Nat) : Nat × Nat × Bool :=
  List.rec (motive := fun _ => Nat × Nat × Bool) (nat_lit 0, nat_lit 0, true)
    (fun x _ ih => Prod.rec (motive := fun _ => Nat × Nat × Bool) (fun c r => Prod.rec
      (motive := fun _ => Nat × Nat × Bool) (fun n ok => (Nat.add x (Nat.shiftLeft c (nat_lit 5)), Nat.add n (nat_lit 1),
        andB (Nat.blt x (nat_lit 24)) ok)) r) ih) l

@[expose] noncomputable def invP (P : Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat) (nat_lit 0)
    (fun i acc => Nat.lor acc (Nat.shiftLeft i (Nat.mul (nat_lit 5) (pe P i)))) (nat_lit 24)

@[expose] noncomputable def codeOK (P : Nat) : Bool :=
  Nat.rec (motive := fun _ => Bool) true
    (fun i ih => andB (Nat.beq (wordT (coeffT (permWordT P (bmT i)))) (permWordT P (bmT i))) ih) (nat_lit 12)

@[expose] noncomputable def permValidT (l : List Nat) : Bool :=
  Prod.rec (motive := fun _ => Bool) (fun P r => Prod.rec (motive := fun _ => Bool) (fun n ok =>
    andB (Nat.beq n (nat_lit 24)) (andB ok (andB
      (Nat.beq (Nat.rec (motive := fun _ => Nat) (nat_lit 0)
        (fun i acc => Nat.lor acc (Nat.shiftLeft (nat_lit 1) (pe P i))) (nat_lit 24)) (nat_lit 16777215))
      (andB (codeOK P) (codeOK (invP P)))))) r) (listPack l)

@[expose] noncomputable def permXOK (F : Fix) (P netX sgnX : Nat) : Bool :=
  (fun MP DP BT =>
    (fun ap => andB (netOK (nat_lit 17) netX) (andB
      (Nat.beq (netP SX (nat_lit 17) (nat_lit 24) netX
        (Nat.lor ap (Nat.shiftLeft (Nat.xor (thetaPl SX ap) (plin SX DP (Nat.xor (thetaPl SX F.keyA) F.keyD)))
          (Nat.mul (nat_lit 12) SX))))
        (Nat.lor F.keyA (Nat.shiftLeft F.keyD (Nat.mul (nat_lit 12) SX))))
      (Nat.beq sgnX (quadPl SX BT F.keyA))))
    (plin SX MP F.keyA))
  (basisImg (permCT P)) (basisImg (permDT P)) (betaTabT P)

@[expose] noncomputable def rowCodeP : Nat :=
  Nat.rec (motive := fun _ => Nat) (nat_lit 0)
    (fun k acc => Nat.lor acc (Nat.shiftLeft (idPlane SX (Nat.add k (nat_lit 5)))
      (Nat.mul (Nat.add k (nat_lit 1)) SX))) (nat_lit 11)

@[expose] noncomputable def permWOK (P netW sgnW : Nat) : Bool :=
  (fun MP BT =>
    (fun pc k63 =>
      (fun lowP eta' sg col =>
        andB (netOK (nat_lit 17) netW) (andB
          (Nat.beq (netP SX (nat_lit 17) (nat_lit 17) netW
            (Nat.rec (motive := fun _ => Nat) (nat_lit 0)
              (fun b acc => Nat.lor acc (Nat.shiftLeft (mux SX valW
                (Bool.rec (motive := fun _ => Nat)
                  (Bool.rec (motive := fun _ => Nat) eta' (plane SX (Nat.sub b (nat_lit 4)) lowP) (Nat.blt b (nat_lit 16)))
                  (plane SX b col) (Nat.blt b (nat_lit 5)))
                (idPlane SX b)) (Nat.mul b SX))) (nat_lit 17)))
            (idP (nat_lit 17)))
          (Nat.beq sgnW (Nat.land valW sg))))
      (Nat.rec (motive := fun _ => Nat) (nat_lit 0)
        (fun k acc => Nat.lor acc (Nat.shiftLeft
          (Bool.rec (motive := fun _ => Nat) (plane SX k pc) (Nat.xor (plane SX k pc) (plane SX (nat_lit 0) pc))
            (andB (Nat.blt (nat_lit 0) k) (Nat.blt k (nat_lit 6))))
          (Nat.mul k SX))) (nat_lit 12))
      (Nat.xor (idPlane SX (nat_lit 16)) (selB k63 (ones SX)))
      (Nat.xor (quadPl SX BT rowCodeP)
        (Nat.land (Nat.xor (idPlane SX (nat_lit 16)) (selB k63 (ones SX))) (plane SX (nat_lit 0) pc)))
      (lookP SX (nat_lit 0) P))
    (plin SX MP rowCodeP) (kappaT BT (nat_lit 63)))
  (basisImg (permCT P)) (betaTabT P)

@[expose] noncomputable def permAOK (P netA : Nat) : Bool :=
  (fun ci cj => andB (netOK (nat_lit 10) netA)
    (Nat.beq (netP SA (nat_lit 10) (nat_lit 10) netA
      (Nat.rec (motive := fun _ => Nat) (nat_lit 0)
        (fun b acc => Nat.lor acc (Nat.shiftLeft (mux SA valA
          (Bool.rec (motive := fun _ => Nat) (plane SA (Nat.sub b (nat_lit 5)) ci) (plane SA b cj) (Nat.blt b (nat_lit 5)))
          (idPlane SA b)) (Nat.mul b SA))) (nat_lit 10)))
      (idP (nat_lit 10))))
  (lookP SA (nat_lit 5) P) (lookP SA (nat_lit 0) P)

@[expose] noncomputable def entryOK (F : Fix) (T : Tab) (l : List Nat) (k : Nat) : Bool :=
  andB (permValidT l) (Prod.rec (motive := fun _ => Bool) (fun P _ =>
    andB (permXOK F P (T.netX k) (T.sgnX k)) (andB (permWOK P (T.netW k) (T.sgnW k)) (permAOK P (T.netA k))))
    (listPack l))

@[expose] noncomputable def tabOK (F : Fix) (T : Tab) : Bool :=
  List.rec (motive := fun _ => Nat → Bool) (fun _ => true)
    (fun l _ ih k => andB (entryOK F T l k) (ih (Nat.add k (nat_lit 1)))) T.arrs (nat_lit 0)

@[expose] noncomputable def gam6 (S X : Nat) : Nat :=
  Nat.xor (Nat.land X (ones (Nat.mul (nat_lit 6) S)))
    (repP S (nat_lit 6) (Nat.rec (motive := fun _ => Nat) (nat_lit 0) (fun i acc => Nat.xor acc (plane S i X)) (nat_lit 6)))

@[expose] noncomputable def e2six (S X : Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat) (nat_lit 0)
    (fun i acc => Nat.xor acc (Nat.land (plane S i X)
      (Nat.rec (motive := fun _ => Nat) (nat_lit 0)
        (fun j acc2 => Nat.xor acc2 (selB (Bool.rec (motive := fun _ => Nat) (nat_lit 0) (nat_lit 1) (Nat.blt i j))
          (plane S j X))) (nat_lit 6)))) (nat_lit 6)

@[expose] noncomputable def xiOK (F : Fix) : Bool :=
  (fun hi nu gmu =>
    andB (netOK (nat_lit 17) F.xiNet) (andB
      (Nat.beq (netP SX (nat_lit 17) (nat_lit 24) F.xiNet
        (Nat.lor (Nat.lor nu (Nat.land F.keyA hi))
          (Nat.shiftLeft (Nat.lor (Nat.xor gmu (gam6 SX nu)) (Nat.land F.keyD hi)) (Nat.mul (nat_lit 12) SX))))
        (Nat.lor F.keyA (Nat.shiftLeft F.keyD (Nat.mul (nat_lit 12) SX))))
      (Nat.beq F.xiSgn (Nat.xor (e2six SX nu)
        (Nat.rec (motive := fun _ => Nat) (nat_lit 0)
          (fun i acc => Nat.xor acc (Nat.land (plane SX i nu) (plane SX i gmu))) (nat_lit 6))))))
  (Nat.xor (onesP SX (nat_lit 12)) (onesP SX (nat_lit 6))) (gam6 SX F.keyD) (gam6 SX F.keyA)

@[expose] noncomputable def poutOK (F : Fix) : Bool :=
  (fun eta pp ph =>
    andB (netOK (nat_lit 17) F.pout)
      (Nat.beq (netP SX (nat_lit 17) (nat_lit 17) F.pout
        (setPl SX (nat_lit 16) (Nat.xor (ones SX) (Nat.xor eta pp))
          (setPl SX (nat_lit 9) (Nat.xor eta ph)
            (Nat.xor (idP (nat_lit 17)) (Nat.shiftLeft (repP SX (nat_lit 4) ph) (Nat.mul (nat_lit 5) SX))))))
        (idP (nat_lit 17))))
  (idPlane SX (nat_lit 16)) (idPlane SX (nat_lit 9)) par58

@[expose] noncomputable def pi6OK (F : Fix) : Bool :=
  andB (netOK (nat_lit 17) F.pi6)
    (Nat.beq (netP SX (nat_lit 17) (nat_lit 17) F.pi6
      (Nat.xor (idP (nat_lit 17)) (repP SX (nat_lit 6) (Nat.land regOct
        (Nat.rec (motive := fun _ => Nat) (nat_lit 0) (fun i acc => Nat.xor acc (idPlane SX i)) (nat_lit 6))))))
      (idP (nat_lit 17)))

@[expose] noncomputable def evenOK : Bool :=
  Prod.rec (motive := fun _ => Bool) (fun ok n => andB ok (Nat.beq n (nat_lit 64)))
    (Nat.rec (motive := fun _ => Bool × Nat) (true, nat_lit 0)
      (fun m ih => Prod.rec (motive := fun _ => Bool × Nat) (fun ok n =>
        Bool.rec (motive := fun _ => Bool × Nat) (ok, n)
          (andB ok (Nat.beq m (Nat.add (Nat.shiftLeft n (nat_lit 1)) (parT (nat_lit 6) n))), Nat.add n (nat_lit 1))
          (Nat.beq (parT (nat_lit 7) m) (nat_lit 0))) ih) (nat_lit 128))

@[expose] noncomputable def tauMasksOK (F : Fix) : Bool :=
  andB evenOK (andB
    (Nat.beq F.doct (Nat.shiftLeft (Nat.mul
      (Nat.rec (motive := fun _ => Nat) (nat_lit 0)
        (fun q acc => Nat.lor acc (Nat.shiftLeft (Nat.land (Nat.shiftRight
          (Nat.add (popcT (nat_lit 6) q) (parT (nat_lit 6) q)) (nat_lit 1)) (nat_lit 1)) q)) (nat_lit 64))
      (Nat.div (ones (nat_lit 48576)) (ones (nat_lit 64)))) (nat_lit 65536)))
    (Prod.rec (motive := fun _ => Bool) (fun u r => Prod.rec (motive := fun _ => Bool) (fun lo up =>
        andB (Nat.beq F.sgOddUp u) (andB (Nat.beq F.sgWLo lo) (Nat.beq F.sgWUp up))) r)
      (Nat.rec (motive := fun _ => Nat × Nat × Nat) (nat_lit 0, nat_lit 0, nat_lit 0)
        (fun t ih => (fun w p => Prod.rec (motive := fun _ => Nat × Nat × Nat) (fun u r => Prod.rec
            (motive := fun _ => Nat × Nat × Nat) (fun lo up =>
              (Nat.lor u (Nat.shiftLeft w (Nat.mul (nat_lit 32) t)),
               Nat.lor lo (Nat.shiftLeft (selB p (nat_lit 16777215)) (Nat.mul (nat_lit 32) t)),
               Nat.lor up (Nat.shiftLeft (Nat.xor w (selB p (nat_lit 16777215))) (Nat.mul (nat_lit 32) t)))) r) ih)
          (wordT (Nat.shiftLeft t (nat_lit 1))) (pT (Nat.shiftLeft t (nat_lit 1)))) (nat_lit 2048))))

@[expose] noncomputable def fixOK (F : Fix) : Bool :=
  andB (xiOK F) (andB (poutOK F) (andB (pi6OK F) (tauMasksOK F)))

end CFSG.KC.KDense

end
