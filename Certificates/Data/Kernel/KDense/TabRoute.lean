module

public import Certificates.Data.Kernel.KDense.Bind

public section

namespace CFSG.KC.KDense

open CFSG.KC CFSG.KC.MonsterConv.Perm CFSG.KC.Loop

@[expose] noncomputable def permCode (l : List Nat) : Nat :=
  Prod.rec (motive := fun _ => Nat) (fun P _ => P) (listPack l)

@[expose] noncomputable def srcX (F : Fix) (P : Nat) : Nat :=
  (fun MP DP => (fun ap => Nat.lor ap (Nat.shiftLeft (Nat.xor (thetaPl SX ap)
      (plin SX DP (Nat.xor (thetaPl SX F.keyA) F.keyD))) (Nat.mul (nat_lit 12) SX)))
    (plin SX MP F.keyA)) (basisImg (permCT P)) (basisImg (permDT P))

@[expose] noncomputable def tgtX (F : Fix) : Nat :=
  Nat.lor F.keyA (Nat.shiftLeft F.keyD (Nat.mul (nat_lit 12) SX))

@[expose] noncomputable def sgnXOf (F : Fix) (P : Nat) : Nat := quadPl SX (betaTabT P) F.keyA

@[expose] noncomputable def srcW (P : Nat) : Nat :=
  (fun MP BT =>
    (fun pc k63 =>
      (fun lowP eta' col =>
        Nat.rec (motive := fun _ => Nat) (nat_lit 0)
          (fun b acc => Nat.lor acc (Nat.shiftLeft (mux SX valW
            (Bool.rec (motive := fun _ => Nat)
              (Bool.rec (motive := fun _ => Nat) eta' (plane SX (Nat.sub b (nat_lit 4)) lowP)
                (Nat.blt b (nat_lit 16)))
              (plane SX b col) (Nat.blt b (nat_lit 5)))
            (idPlane SX b)) (Nat.mul b SX))) (nat_lit 17))
      (Nat.rec (motive := fun _ => Nat) (nat_lit 0)
        (fun k acc => Nat.lor acc (Nat.shiftLeft
          (Bool.rec (motive := fun _ => Nat) (plane SX k pc)
            (Nat.xor (plane SX k pc) (plane SX (nat_lit 0) pc))
            (andB (Nat.blt (nat_lit 0) k) (Nat.blt k (nat_lit 6))))
          (Nat.mul k SX))) (nat_lit 12))
      (Nat.xor (idPlane SX (nat_lit 16)) (selB k63 (ones SX)))
      (lookP SX (nat_lit 0) P))
    (plin SX MP rowCodeP) (kappaT BT (nat_lit 63)))
  (basisImg (permCT P)) (betaTabT P)

@[expose] noncomputable def sgnWOf (P : Nat) : Nat :=
  (fun MP BT =>
    (fun pc k63 =>
      Nat.land valW (Nat.xor (quadPl SX BT rowCodeP)
        (Nat.land (Nat.xor (idPlane SX (nat_lit 16)) (selB k63 (ones SX))) (plane SX (nat_lit 0) pc))))
    (plin SX MP rowCodeP) (kappaT BT (nat_lit 63)))
  (basisImg (permCT P)) (betaTabT P)

@[expose] noncomputable def srcA (P : Nat) : Nat :=
  (fun ci cj =>
    Nat.rec (motive := fun _ => Nat) (nat_lit 0)
      (fun b acc => Nat.lor acc (Nat.shiftLeft (mux SA valA
        (Bool.rec (motive := fun _ => Nat) (plane SA (Nat.sub b (nat_lit 5)) ci) (plane SA b cj)
          (Nat.blt b (nat_lit 5)))
        (idPlane SA b)) (Nat.mul b SA))) (nat_lit 10))
  (lookP SA (nat_lit 5) P) (lookP SA (nat_lit 0) P)

end CFSG.KC.KDense

end
