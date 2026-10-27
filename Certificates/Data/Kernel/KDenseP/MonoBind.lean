module

public import Certificates.Data.Kernel.KDenseP.Mono
public import Certificates.Data.Kernel.KDense.Bind
public import Certificates.Data.Kernel.KDense.Init

public section

namespace CFSG.KC.KDenseP

open CFSG.KC CFSG.KC.MonsterConv.Perm CFSG.KC.Loop CFSG.KC.KDense

@[expose] noncomputable def monoMoveX (np : Nat) (E : MonoE) (X : Nat) : Nat :=
  Nat.lor (monoOdd np E X)
    (pairsBack np E.psw (monoPair np E (nat_lit 114688) X) (monoPair np E (nat_lit 115712) X))

@[expose] noncomputable def eqOn (S np m x y : Nat) : Bool :=
  Nat.beq (Nat.land x (repN S np m)) (Nat.land y (repN S np m))

@[expose] noncomputable def monoNetsOK (E : MonoE) : Bool :=
  andB (andB (andB (netOK (nat_lit 5) E.cn) (netOK (nat_lit 11) E.on))
      (andB (netOK (nat_lit 10) E.qn) (netOK (nat_lit 12) E.wn)))
    (andB (andB (Nat.blt E.sel (Nat.shiftLeft (nat_lit 1) (nat_lit 20480)))
        (Nat.blt E.xsel (Nat.shiftLeft (nat_lit 1) (nat_lit 6144))))
      (andB (andB (Nat.blt E.psw (Nat.shiftLeft (nat_lit 1) SA)) (Nat.blt E.sgX (Nat.shiftLeft (nat_lit 1) SX)))
        (andB (Nat.blt E.sgW (Nat.shiftLeft (nat_lit 1) SX)) (Nat.blt E.sgA (Nat.shiftLeft (nat_lit 1) SA)))))

@[expose] noncomputable def monoPermXOK (F : Fix) (P : Nat) (E : MonoE) : Bool :=
  (fun MP DP BT =>
    (fun ap => andB
      (Nat.beq (monoMoveX (nat_lit 24) E
        (Nat.lor ap (Nat.shiftLeft (Nat.xor (thetaPl SX ap) (plin SX DP (Nat.xor (thetaPl SX F.keyA) F.keyD)))
          (Nat.mul (nat_lit 12) SX))))
        (Nat.lor F.keyA (Nat.shiftLeft F.keyD (Nat.mul (nat_lit 12) SX))))
      (Nat.beq E.sgX (quadPl SX BT F.keyA)))
    (plin SX MP F.keyA))
  (basisImg (permCT P)) (basisImg (permDT P)) (betaTabT P)

@[expose] noncomputable def monoPermWOK (P : Nat) (E : MonoE) : Bool :=
  (fun MP BT =>
    (fun pc k63 =>
      (fun lowP eta' sg col =>
        andB
          (eqOn SX (nat_lit 17) valW (monoW (nat_lit 17) E
            (Nat.rec (motive := fun _ => Nat) (nat_lit 0)
              (fun b acc => Nat.lor acc (Nat.shiftLeft (mux SX valW
                (Bool.rec (motive := fun _ => Nat)
                  (Bool.rec (motive := fun _ => Nat) eta' (plane SX (Nat.sub b (nat_lit 4)) lowP) (Nat.blt b (nat_lit 16)))
                  (plane SX b col) (Nat.blt b (nat_lit 5)))
                (idPlane SX b)) (Nat.mul b SX))) (nat_lit 17)))
            (idP (nat_lit 17)))
          (Nat.beq E.sgW (Nat.land valW sg)))
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

@[expose] noncomputable def monoPermAOK (P : Nat) (E : MonoE) : Bool :=
  (fun ci cj => andB (Nat.beq E.sgA (nat_lit 0))
    (eqOn SA (nat_lit 10) valA (amapN (nat_lit 10) E.cn
      (Nat.rec (motive := fun _ => Nat) (nat_lit 0)
        (fun b acc => Nat.lor acc (Nat.shiftLeft (mux SA valA
          (Bool.rec (motive := fun _ => Nat) (plane SA (Nat.sub b (nat_lit 5)) ci) (plane SA b cj) (Nat.blt b (nat_lit 5)))
          (idPlane SA b)) (Nat.mul b SA))) (nat_lit 10)))
      (idP (nat_lit 10))))
  (lookP SA (nat_lit 5) P) (lookP SA (nat_lit 0) P)

@[expose] noncomputable def monoPermOK (F : Fix) (l : List Nat) (E : MonoE) : Bool :=
  andB (permValidT l) (Prod.rec (motive := fun _ => Bool) (fun P _ =>
    andB (monoPermXOK F P E) (andB (monoPermWOK P E) (monoPermAOK P E))) (listPack l))

@[expose] noncomputable def parP (S X Y : Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat) (nat_lit 0)
    (fun k acc => Nat.xor acc (Nat.land (plane S k X) (plane S k Y))) (nat_lit 12)

@[expose] noncomputable def monoSignXOK (F : Fix) (a : Nat) (E : MonoE) : Bool :=
  (fun thB O Pad =>
    (fun T0 thAB T2 =>
      (fun T1 Dd0 Dd1 Dd2 =>
        andB
          (Nat.beq (monoMoveX (nat_lit 24) E
              (Nat.lor (Nat.xor T1 Dd1) (Nat.shiftLeft (Nat.xor T2 Dd2) (Nat.mul (nat_lit 12) SX))))
            (Nat.lor F.keyA (Nat.shiftLeft F.keyD (Nat.mul (nat_lit 12) SX))))
          (Nat.beq E.sgX (Nat.land validX (Nat.xor (Nat.xor T0 Dd0) (parP SX Dd1 T2)))))
        (Nat.xor F.keyA (repP SX (nat_lit 6) thAB))
        (Nat.land (Nat.xor (ones SX) O) Pad)
        (Nat.xor (constP SX a O) (repP SX (nat_lit 6) (Nat.xor (selB (pT a) O) Pad)))
        (Nat.xor F.keyD (constP SX (thetaT a) O)))
      (parSel SX a thB) (parSel SX (thetaT a) F.keyA)
      (plin SX (basisImg (fun b => dualT (Nat.land (wordT a) (wordT b)))) F.keyA))
    (thetaPl SX F.keyA) (parSel SX (nat_lit 63) F.keyD) (parSel SX a F.keyD)

@[expose] noncomputable def triTab (a : Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat) (nat_lit 0)
    (fun i acc => Nat.lor acc (Nat.rec (motive := fun _ => Nat) (nat_lit 0)
      (fun j acc2 => Nat.lor acc2 (Nat.shiftLeft
        (par24 (Nat.land (wordT a) (Nat.land (bmT i) (bmT j)))) (Nat.add (Nat.mul (nat_lit 12) i) j))) (nat_lit 12)))
    (nat_lit 12)

@[expose] noncomputable def halfTab (a : Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat) (nat_lit 0)
    (fun i acc => Nat.lor acc (Nat.shiftLeft
      (Nat.land (Nat.shiftRight (popc24 (Nat.land (wordT a) (bmT i))) (nat_lit 1)) (nat_lit 1)) i))
    (nat_lit 12)

@[expose] noncomputable def colMask (S m : Nat) : Nat := Nat.mul m (repU (nat_lit 32) (Nat.div S (nat_lit 32)))

@[expose] noncomputable def monoSignWOK (a : Nat) (E : MonoE) : Bool :=
  (fun t eta =>
    andB
      (eqOn SX (nat_lit 17) valW (monoW (nat_lit 17) E
        (Nat.rec (motive := fun _ => Nat) (nat_lit 0)
          (fun b acc => Nat.lor acc (Nat.shiftLeft (mux SX valW
            (Bool.rec (motive := fun _ => Nat) (idPlane SX b)
              (Nat.xor (idPlane SX b) (selB (bitN t (Nat.sub b (nat_lit 5))) (Nat.xor (ones SX) eta)))
              (andB (Nat.ble (nat_lit 5) b) (Nat.blt b (nat_lit 16))))
            (idPlane SX b)) (Nat.mul b SX))) (nat_lit 17)))
        (idP (nat_lit 17)))
      (Nat.beq E.sgW (Nat.land valW (Nat.xor (colMask SX (wordT a))
        (mux SX eta (Nat.xor (quadPl SX (triTab a) rowCodeP) (parSel SX (halfTab a) rowCodeP))
          (parSel SX a (thetaPl SX rowCodeP)))))))
    (Nat.shiftRight (Nat.xor a (selB (Nat.land a (nat_lit 1)) (nat_lit 63))) (nat_lit 1)) (idPlane SX (nat_lit 16))

@[expose] noncomputable def monoSignAOK (a : Nat) (E : MonoE) : Bool :=
  andB
    (Nat.beq (amapN (nat_lit 10) E.cn (idP (nat_lit 10))) (idP (nat_lit 10)))
    (Nat.beq E.sgA (Nat.land valA (Nat.xor (colMask SA (wordT a))
      (Nat.mul (Nat.rec (motive := fun _ => Nat) (nat_lit 0)
          (fun i acc => Nat.lor acc (Nat.shiftLeft (bitN (wordT a) i) (Nat.mul (nat_lit 32) i))) (nat_lit 24))
        (ones (nat_lit 32))))))

@[expose] noncomputable def monoSignOK (F : Fix) (a : Nat) (E : MonoE) : Bool :=
  andB (Nat.blt a (nat_lit 4096)) (andB (monoSignXOK F a E) (andB (monoSignWOK a E) (monoSignAOK a E)))

@[expose] noncomputable def monoPadOK (E : MonoE) : Bool :=
  Nat.beq (Nat.land (monoOdd (nat_lit 1) E (ones SX)) pairBlocks) (nat_lit 0)

@[expose] noncomputable def monoEntOK (F : Fix) (l : List Nat) (E : MonoE) : Bool :=
  andB (andB (monoNetsOK E) (monoPadOK E))
    (List.rec (motive := fun _ => Bool) false
      (fun a t _ => List.rec (motive := fun _ => Bool) (monoSignOK F a E) (fun _ _ _ => monoPermOK F l E) t) l)

@[expose] noncomputable def monoTabOK (F : Fix) (MT : MonoTab) : Bool :=
  List.rec (motive := fun _ => Nat → Bool) (fun _ => true)
    (fun l _ ih k => andB (monoEntOK F l (MT.ents k)) (ih (Nat.add k (nat_lit 1)))) MT.keys (nat_lit 0)

@[expose] noncomputable def dataOKP (F : Fix) (MT : MonoTab) (KT TH OCT DU1 : Nat) : Bool :=
  andB (thOK TH) (andB (octOK OCT) (andB (du1OK DU1) (andB (keysOK TH OCT DU1 KT)
    (andB (keyPlanesOK F KT) (andB (fixOK F) (monoTabOK F MT))))))

end CFSG.KC.KDenseP

end
