module

public import Certificates.Data.Kernel.S23Inner

public section

namespace CFSG.KC.CTIBq

open CFSG.KLie.CT CFSG.KC.Loop CFSG.KC.F4M CFSG.KC.S23

@[expose] noncomputable def M22 : Nat := nat_lit 4194303

@[expose] noncomputable def gu (GR j : Nat) : Nat :=
  Nat.land (fget GR j (nat_lit 22)) (Nat.sub M22 (maskN (Nat.succ j)))

@[expose] noncomputable def mbByte (GR k x : Nat) : Nat :=
  xorN (nat_lit 8) fun t => nIf(andB (bit x t) (Nat.blt (Nat.add (Nat.mul (nat_lit 8) k) t) (nat_lit 22)),
    gu GR (Nat.add (Nat.mul (nat_lit 8) k) t), nat_lit 0)

@[expose] noncomputable def tbOf (GR : Nat) : Nat :=
  orN (nat_lit 768) fun t => Nat.shiftLeft
    (mbByte GR (Nat.shiftRight t (nat_lit 8)) (Nat.land t (nat_lit 255))) (Nat.mul (nat_lit 22) t)

@[expose] noncomputable def mb (TB b : Nat) : Nat :=
  Nat.xor (fget TB (Nat.land b (nat_lit 255)) (nat_lit 22))
    (Nat.xor (fget TB (Nat.add (nat_lit 256) (Nat.land (Nat.shiftRight b (nat_lit 8)) (nat_lit 255))) (nat_lit 22))
      (fget TB (Nat.add (nat_lit 512) (Nat.land (Nat.shiftRight b (nat_lit 16)) (nat_lit 255))) (nat_lit 22)))

@[expose] noncomputable def qmulK (TB a b : Nat) : Nat :=
  Nat.lor (Nat.land (Nat.xor a b) M22)
    (Nat.shiftLeft (Nat.land (Nat.xor (Nat.xor (Nat.shiftRight a (nat_lit 22)) (Nat.shiftRight b (nat_lit 22)))
      (par (Nat.land a (mb TB b)))) (nat_lit 1)) (nat_lit 22))

@[expose] noncomputable def qinvK (TB d : Nat) : Nat := qmulK TB (qmulK TB d d) d

@[expose] noncomputable def img (A i : Nat) : Nat := fget A i (nat_lit 23)

@[expose] noncomputable def autApplyK (TB A n : Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat) (Nat.shiftLeft (Nat.land (Nat.shiftRight n (nat_lit 22)) (nat_lit 1)) (nat_lit 22))
    (fun m ih => strictN ih fun acc => nIf(bit n m, qmulK TB acc (img A m), acc)) (nat_lit 22)

@[expose] noncomputable def autCompK (TB A B : Nat) : Nat :=
  strictN A fun A => strictN B fun B =>
    orN (nat_lit 22) fun i => Nat.shiftLeft (autApplyK TB B (img A i)) (Nat.mul (nat_lit 23) i)

@[expose] noncomputable def ID23 : Nat := orN (nat_lit 22) fun i => Nat.shiftLeft (pw2 i) (Nat.mul (nat_lit 23) i)

@[expose] noncomputable def autPowK (TB A k : Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat) ID23 (fun _ ih => autCompK TB ih A) k

@[expose] noncomputable def innerK (TB d : Nat) : Nat :=
  orN (nat_lit 22) fun i =>
    Nat.shiftLeft (qmulK TB (qmulK TB (qinvK TB d) (pw2 i)) d) (Nat.mul (nat_lit 23) i)

@[expose] noncomputable def sgnImg (Q s : Nat) : Nat :=
  orN (nat_lit 22) fun i => Nat.shiftLeft
    (Nat.lor (fget Q i (nat_lit 22)) (Nat.shiftLeft (Nat.land (Nat.shiftRight s i) (nat_lit 1)) (nat_lit 22)))
    (Nat.mul (nat_lit 23) i)

@[expose] noncomputable def wordAutK (TB G0 G1 GI : Nat) (w : List Nat) : Nat :=
  List.rec (motive := fun _ => Nat → Nat) (fun A => A)
    (fun l _ ih A => strictN (autCompK TB A
      (nIf(Nat.beq l (nat_lit 0), G0, nIf(Nat.beq l (nat_lit 1), G1, GI)))) ih) w ID23

@[expose] noncomputable def wordOK (w : List Nat) : Bool :=
  List.rec (motive := fun _ => Bool) true (fun l _ ih => andB (Nat.blt l (nat_lit 3)) ih) w

@[expose] noncomputable def bindL (P w : Nat) (l : List Nat) : Bool :=
  List.rec (motive := fun _ => Nat → Bool) (fun _ => true)
    (fun x _ ih k => andB (Nat.blt x (pw2 w)) (andB (Nat.beq x (fget P k w)) (ih (Nat.succ k)))) l
    (nat_lit 0)

@[expose] noncomputable def lenL (l : List Nat) : Nat :=
  List.rec (motive := fun _ => Nat) (nat_lit 0) (fun _ _ ih => Nat.succ ih) l

@[expose] noncomputable def d8K (GR A8 : Nat) : Bool :=
  strictB (tbOf GR) fun TB => (fun q => (fun X =>
    andB (Nat.beq (q (nat_lit 2) (nat_lit 2)) (nat_lit 0))
    (andB (Nat.beq (q (nat_lit 32) (nat_lit 32)) (nat_lit 0))
    (andB (Nat.beq (q (nat_lit 2) (nat_lit 1)) (q (nat_lit 1) (nat_lit 2)))
    (andB (Nat.beq (q (nat_lit 32) (nat_lit 1)) (q (nat_lit 1) (nat_lit 32)))
    (andB (Nat.beq (q (q (nat_lit 2) (nat_lit 32)) (q (nat_lit 2) (nat_lit 32))) X)
    (andB (Nat.beq (q (q (nat_lit 1) (nat_lit 2)) (q (nat_lit 1) (nat_lit 2))) (nat_lit 0))
    (andB (Nat.beq (q (q (nat_lit 1) (nat_lit 32)) (q (nat_lit 1) (nat_lit 32))) (nat_lit 0))
    (andB (Nat.beq (q (nat_lit 9) (nat_lit 9)) (nat_lit 0))
    (andB (Nat.beq (q (nat_lit 3162) (nat_lit 3162)) (nat_lit 0))
    (andB (Nat.beq (q (nat_lit 3162) (nat_lit 128)) (q (nat_lit 128) (nat_lit 3162)))
    (andB (Nat.beq (q (nat_lit 0) (q (autApplyK TB A8 (nat_lit 3162)) (nat_lit 3162))) (nat_lit 5449715))
    (andB (Nat.beq (q (nat_lit 2) (nat_lit 1255411)) (q (q (nat_lit 1255411) (nat_lit 2)) X))
    (andB (Nat.beq (q (q (nat_lit 128) (nat_lit 2)) (q (nat_lit 128) (nat_lit 2))) (nat_lit 0))
    (andB (Nat.beq (q (q (nat_lit 128) (nat_lit 9)) (q (nat_lit 128) (nat_lit 9))) (nat_lit 0))
    (andB (Nat.beq (q (q (nat_lit 128) (nat_lit 3162)) (q (nat_lit 128) (nat_lit 3162))) (nat_lit 0))
      (Nat.beq (q (nat_lit 1255411) X) (nat_lit 5449715)))))))))))))))))
    (nat_lit 4194304)) (qmulK TB)

@[expose] noncomputable def fgPairK (TB A6 v a : Nat) : Bool :=
  (fun q =>
    andB (Nat.beq (q a (nat_lit 4456968)) (q (nat_lit 4456968) a))
    (andB (Nat.beq (q (nat_lit 10541) a) (q (q (autApplyK TB A6 a) (nat_lit 10541)) v))
    (andB (Nat.beq (q (nat_lit 10541) v) (q (autApplyK TB A6 v) (nat_lit 10541)))
    (andB (Nat.beq (q v (nat_lit 4456968)) (q (nat_lit 4456968) v))
      (Nat.beq (q v v) (nat_lit 0)))))) (qmulK TB)

@[expose] noncomputable def fgK (GR A6 : Nat) : Bool :=
  strictB (tbOf GR) fun TB =>
  andB (fgPairK TB A6 (nat_lit 5131954) (nat_lit 3138877))
  (andB (fgPairK TB A6 (nat_lit 6537621) (nat_lit 2916759))
  (andB (fgPairK TB A6 (nat_lit 7180071) (nat_lit 7635562))
  (andB (Nat.beq (qmulK TB (nat_lit 5131954) (nat_lit 6537621)) (nat_lit 7180071))
    (Nat.beq (qmulK TB (nat_lit 6537621) (nat_lit 5131954)) (nat_lit 7180071)))))

@[expose] noncomputable def frameK (TB : Nat) : Bool :=
  andB (Nat.beq (qmulK TB (nat_lit 1) (nat_lit 6)) (nat_lit 7))
  (andB (Nat.beq (qmulK TB (nat_lit 6) (nat_lit 1)) (nat_lit 7))
  (andB (Nat.beq (qmulK TB (nat_lit 1) (nat_lit 7)) (nat_lit 6))
    (Nat.beq (qmulK TB (nat_lit 7) (nat_lit 1)) (nat_lit 6))))

@[expose] noncomputable def oddK (TB G0 G1 GI c y : Nat) (wa : List Nat) (ea ma : Nat) (wb : List Nat)
    (eb mb n e : Nat) : Bool :=
  strictB (wordAutK TB G0 G1 GI wa) fun A => strictB (wordAutK TB G0 G1 GI wb) fun B =>
  strictB (autPowK TB A ea) fun Ae => strictB (autPowK TB B eb) fun Be =>
  strictB (autPowK TB Ae (Nat.succ ma)) fun Aa => strictB (autPowK TB Be (Nat.succ mb)) fun Bb =>
  strictB (autCompK TB (autCompK TB (autCompK TB (autCompK TB (autCompK TB Aa Bb)
      (autPowK TB Aa (Nat.sub ma (nat_lit 1)))) (innerK TB n)) Aa) (innerK TB (qinvK TB n))) fun S =>
    andB (wordOK wa) (andB (wordOK wb)
    (andB (Nat.beq (Nat.mod ma (nat_lit 2)) (nat_lit 1)) (andB (Nat.beq (Nat.mod mb (nat_lit 2)) (nat_lit 1))
    (andB (Nat.beq (autPowK TB Ae ma) ID23) (andB (Nat.beq (autPowK TB Be mb) ID23)
    (andB (Nat.beq (autApplyK TB A c) c) (andB (Nat.beq (autApplyK TB A y) y)
    (andB (Nat.beq (autApplyK TB B c) c) (andB (Nat.beq (autApplyK TB B y) y)
    (andB (Nat.beq (qmulK TB n c) (qmulK TB c n)) (andB (Nat.beq (qmulK TB n y) (qmulK TB y n))
    (andB (Nat.beq (autCompK TB S S) (innerK TB y))
    (andB (Nat.beq (qmulK TB e c) (qmulK TB c e))
      (Nat.beq (qmulK TB (qmulK TB (qinvK TB e) y) e) (qmulK TB y (nat_lit 4194304))))))))))))))))

@[expose] noncomputable def frameCheck (GR : Nat) : Bool := strictB (tbOf GR) fun TB => frameK TB

@[expose] noncomputable def oddCheck (GR Q1 Q2 s1 s2 c y : Nat) (wa : List Nat) (ea ma : Nat)
    (wb : List Nat) (eb mb n e : Nat) : Bool :=
  strictB (tbOf GR) fun TB =>
  strictB (sgnImg Q1 s1) fun G0 => strictB (sgnImg Q2 s2) fun G1 =>
  strictB (autPowK TB G1 (nat_lit 47)) fun GI => oddK TB G0 G1 GI c y wa ea ma wb eb mb n e

end CFSG.KC.CTIBq

end
