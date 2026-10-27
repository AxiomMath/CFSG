module

public import Certificates.Data.Kernel.WeylE8.U
public import Certificates.Data.Kernel.WeylE8.Agl

public section

namespace CFSG.KLC.E8

open CFSG.KC.Enum

@[expose] noncomputable def pMulK (PMT i j : Nat) : Nat :=
  pg (nat_lit 7) (nat_lit 127) PMT (Nat.add (Nat.mul (nat_lit 128) i) j)

@[expose] noncomputable def pInvK (PIT i : Nat) : Nat := pg (nat_lit 7) (nat_lit 127) PIT i

@[expose] noncomputable def pListK (PC PMT PIT PPAR PLAB : Nat) : Bool :=
  bAnd(allN (nat_lit 128) (fun i => permOKK (e24 PC i)),
  bAnd(allN (nat_lit 128) (fun i => allN i fun j => notB' (Nat.beq (e24 PC i) (e24 PC j))),
  bAnd(Nat.beq (e24 PC (nat_lit 0)) spId,
  bAnd(allN (nat_lit 128) (fun i => allN (nat_lit 128) fun j =>
      Nat.beq (spMul (e24 PC i) (e24 PC j)) (e24 PC (pMulK PMT i j))),
  bAnd(allN (nat_lit 128) (fun i => Nat.beq (spMul (e24 PC i) (e24 PC (pInvK PIT i))) spId),
    allN (nat_lit 128) fun i => bIf(Nat.beq i (nat_lit 0), true,
      strictB (pg (nat_lit 7) (nat_lit 127) PPAR i) fun p =>
        strictB (pg (nat_lit 3) (nat_lit 7) PLAB i) fun l =>
          bAnd(Nat.blt p i, bAnd(Nat.blt l (nat_lit 7), Nat.beq (pMulK PMT (Nat.succ l) p) i))))))))

@[expose] noncomputable def nthK (l : List Nat) : Nat → Nat :=
  List.rec (motive := fun _ => Nat → Nat) (fun _ => nat_lit 0)
    (fun a _ ih k => Nat.rec (motive := fun _ => Nat) a (fun k' _ => ih k') k) l

@[expose] noncomputable def wordIdxK (PMT : Nat) (gi w : List Nat) : Nat :=
  List.rec (motive := fun _ => Nat) (nat_lit 0) (fun k _ ih => pMulK PMT (nthK gi k) ih) w

@[expose] noncomputable def wordsHitK (PMT : Nat) (gi : List Nat) (W : List (List Nat)) (i : Nat) :
    Bool :=
  List.rec (motive := fun _ => Bool) false
    (fun w _ ih => bIf(Nat.beq (wordIdxK PMT gi w) i, true, ih)) W

@[expose] noncomputable def subK (PMT PIT M : Nat) (gi : List Nat) (W : List (List Nat)) : Bool :=
  bAnd(bitK M (nat_lit 0),
  bAnd(Nat.blt M (Nat.shiftLeft (nat_lit 1) (nat_lit 128)),
  bAnd(List.rec (motive := fun _ => Bool) true
      (fun g _ ih => bAnd(Nat.blt g (nat_lit 128), bAnd(bitK M g, ih))) gi,
  bAnd(allN (nat_lit 128) (fun i => bIf(bitK M i,
      allN (nat_lit 128) (fun j => bIf(bitK M j, bitK M (pMulK PMT i j), true)), true)),
  bAnd(allN (nat_lit 128) (fun i => bIf(bitK M i, bitK M (pInvK PIT i), true)),
    allN (nat_lit 128) fun i => bIf(bitK M i, wordsHitK PMT gi W i, true))))))

@[expose] noncomputable def fxAt (FX i : Nat) : Nat :=
  fld(FX, Nat.shiftLeft i (nat_lit 8),
    Nat.sub (Nat.shiftLeft (nat_lit 1) (nat_lit 256)) (nat_lit 1))

@[expose] noncomputable def fixAK (c n : Nat) : Bool :=
  allN (nat_lit 8) fun j => bIf(bitK n (spAt c j), bitK n j, notB' (bitK n j))

@[expose] noncomputable def fixTabK (PC FX : Nat) : Bool :=
  allN (nat_lit 128) fun i => strictB (fxAt FX i) fun F => strictB (e24 PC i) fun c =>
    allN (nat_lit 256) fun n => bIf(bitK F n, fixAK c n, notB' (fixAK c n))

@[expose] noncomputable def fixK (FX m : Nat) : Nat :=
  strictN (Nat.rec (motive := fun _ => Nat)
      (Nat.sub (Nat.shiftLeft (nat_lit 1) (nat_lit 256)) (nat_lit 1))
      (fun i ih => nIf(bitK m i, Nat.land ih (fxAt FX i), ih)) (nat_lit 128)) fun F =>
    sumN (nat_lit 256) fun n => nIf(bAnd(evenB n, bitK F n), nat_lit 1, nat_lit 0)

@[expose] noncomputable def validK (PMT m x : Nat) : Bool :=
  bAnd(notB' (bitK m x), bAnd(bitK m (pMulK PMT x x),
    allN (nat_lit 128) fun i => bIf(bitK m i, Nat.beq (pMulK PMT x i) (pMulK PMT i x), true)))

@[expose] noncomputable def extK (PMT PIT m x : Nat) : Nat :=
  strictN (pInvK PIT x) fun y => Nat.lor m (Nat.rec (motive := fun _ => Nat) (nat_lit 0)
    (fun n ih => Nat.lor ih (nIf(bitK m (pMulK PMT y n), Nat.shiftLeft (nat_lit 1) n, nat_lit 0)))
    (nat_lit 128))

@[expose] noncomputable def inListK (L : List Nat) (e : Nat) : Bool :=
  List.rec (motive := fun _ => Bool) false (fun a _ ih => bIf(Nat.beq a e, true, ih)) L

@[expose] noncomputable def subMaskK (m M : Nat) : Bool :=
  allN (nat_lit 128) fun i => bIf(bitK m i, bitK M i, true)

@[expose] noncomputable def layerValK (FX PPM Q1M Q0M k m : Nat) : Bool :=
  strictB (Nat.shiftLeft (fixK FX m) k) fun v =>
    bAnd(Nat.ble v (nat_lit 256), bAnd(bIf(Nat.beq v (nat_lit 256), Nat.beq m Q1M, true),
      bIf(subMaskK m PPM, bAnd(Nat.ble v (nat_lit 128),
        bIf(Nat.beq v (nat_lit 128), bIf(Nat.beq m (nat_lit 1), true, Nat.beq m Q0M), true)),
        true)))

@[expose] noncomputable def layerK (PMT PIT FX PPM Q1M Q0M k : Nat) (L L' : List Nat) : Bool :=
  List.rec (motive := fun _ => Bool) true (fun m _ ih =>
    bAnd(allN (nat_lit 128) (fun x => bIf(validK PMT m x, inListK L' (extK PMT PIT m x), true)),
      bAnd(layerValK FX PPM Q1M Q0M k m, ih))) L

@[expose] noncomputable def inL (L n x : Nat) : Bool :=
  notB' (allN n fun j => notB' (Nat.beq (e32 L j) x))

@[expose] noncomputable def uListK (UC UG UGI UPP ULP : Nat) : Bool :=
  bAnd(allN (nat_lit 128) (fun i => okC (e32 UC i)),
  bAnd(allN (nat_lit 128) (fun i => allN i fun j => notB' (Nat.beq (e32 UC i) (e32 UC j))),
  bAnd(Nat.beq (e32 UC (nat_lit 0)) spId,
  bAnd(allN (nat_lit 4) (fun k => strictB (e32 UG k) fun g => strictB (e32 UGI k) fun gi =>
      bAnd(okC g, bAnd(okC gi, Nat.beq (spMul g gi) spId))),
  bAnd(allN (nat_lit 128) (fun i => bIf(Nat.beq i (nat_lit 0), true,
      strictB (pg (nat_lit 8) (nat_lit 255) UPP i) fun p =>
        strictB (pg (nat_lit 8) (nat_lit 255) ULP i) fun l =>
          bAnd(Nat.blt p i, bAnd(Nat.blt l (nat_lit 4),
            Nat.beq (e32 UC i) (spMul (e32 UG l) (e32 UC p)))))),
  bAnd(allN (nat_lit 128) (fun i => allN (nat_lit 4) fun k =>
      bAnd(inL UC (nat_lit 128) (spMul (e32 UG k) (e32 UC i)),
        inL UC (nat_lit 128) (spMul (e32 UGI k) (e32 UC i)))),
  bAnd(allN (nat_lit 4) (fun i => allN (nat_lit 4) fun j => commB (e32 UG i) (e32 UG j)),
    notB' (Nat.beq (spMul (e32 UG (nat_lit 1)) (e32 UG (nat_lit 1))) spId))))))))

@[expose] noncomputable def liftK (r q : Nat) : Nat := spMul (signC r) q

@[expose] noncomputable def lift1K (LR Q1C : Nat) : Bool :=
  allN (nat_lit 8) fun a => allN (nat_lit 8) fun b => allN (nat_lit 8) fun c =>
    allN (nat_lit 8) fun d =>
      strictB (liftK (pg (nat_lit 8) (nat_lit 255) LR a) (e32 Q1C (nat_lit 0))) fun x0 =>
      strictB (liftK (pg (nat_lit 8) (nat_lit 255) LR b) (e32 Q1C (nat_lit 1))) fun x1 =>
      strictB (liftK (pg (nat_lit 8) (nat_lit 255) LR c) (e32 Q1C (nat_lit 2))) fun x2 =>
      strictB (liftK (pg (nat_lit 8) (nat_lit 255) LR d) (e32 Q1C (nat_lit 3))) fun x3 =>
        bIf(bAnd(commB x0 x1, bAnd(commB x0 x2, bAnd(commB x0 x3, bAnd(commB x1 x2,
            bAnd(commB x1 x3, commB x2 x3))))),
          bAnd(frameK' x0, bAnd(frameK' x1, bAnd(frameK' x2, frameK' x3))), true)

@[expose] noncomputable def lift0K (LR Q0C UC : Nat) : Bool :=
  allN (nat_lit 8) fun a => allN (nat_lit 8) fun b => allN (nat_lit 8) fun c =>
    strictB (liftK (pg (nat_lit 8) (nat_lit 255) LR a) (e32 Q0C (nat_lit 0))) fun x0 =>
    strictB (liftK (pg (nat_lit 8) (nat_lit 255) LR b) (e32 Q0C (nat_lit 1))) fun x1 =>
    strictB (liftK (pg (nat_lit 8) (nat_lit 255) LR c) (e32 Q0C (nat_lit 2))) fun x2 =>
      bIf(bAnd(commB x0 x1, bAnd(commB x0 x2, commB x1 x2)),
        bIf(bAnd(frameK' x0, bAnd(frameK' x1, frameK' x2)), true,
          bAnd(inL UC (nat_lit 128) x0, bAnd(inL UC (nat_lit 128) x1, inL UC (nat_lit 128) x2))),
        true)

end CFSG.KLC.E8

end
