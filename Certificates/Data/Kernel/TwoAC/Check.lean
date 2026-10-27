module

public import CFSG.Certificates.Kernel.BabyMonster.F2
public import Certificates.Data.Kernel.YModel.Text

public section

namespace CFSG.KC.BM.TwoAC

open CFSG.KC.BM CFSG.KC.YModel

@[expose] noncomputable def rowAtS (S : List Nat) (t : Nat) : Nat :=
  rowOf (lget S (Nat.div t (nat_lit 64))) (Nat.mod t (nat_lit 64))

@[expose] noncomputable def nodeOK (S SA SB : List Nat) (V0 V1 k t c : Nat) : Bool :=
  Bool.rec (motive := fun _ => Bool)
    (andB (Nat.blt (Nat.shiftRight c (nat_lit 1)) t)
      (Nat.beq (rowAtS S t)
        (rowAtS (Bool.rec (motive := fun _ => List Nat) SA SB
          (Nat.beq (Nat.land c (nat_lit 1)) (nat_lit 1))) (Nat.shiftRight c (nat_lit 1)))))
    (andB (Nat.blt c (nat_lit 8742))
      (Nat.beq (rowAtS S t)
        (rowOf (Bool.rec (motive := fun _ => Nat) V0 V1 (Nat.beq c (nat_lit 8741))) k)))
    (Nat.ble (nat_lit 8740) c)

@[expose] noncomputable def blockNodesOK (S SA SB : List Nat) (V0 V1 k : Nat) (blk : List Nat)
    (t : Nat) : Bool :=
  List.rec (motive := fun _ => Nat → Bool) (fun _ => true)
    (fun c _ ih t => Bool.rec (motive := fun _ => Bool) false (ih (Nat.succ t))
      (nodeOK S SA SB V0 V1 k t c)) blk t

@[expose] noncomputable def forestOK (Fb : List (List Nat)) (S SA SB : List Nat) (V0 V1 k : Nat) :
    Bool :=
  andB (Nat.beq (lenLL Fb) (nat_lit 69))
    (List.rec (motive := fun _ => Nat → Bool) (fun _ => true)
      (fun blk _ ih s => Bool.rec (motive := fun _ => Bool) false (ih (Nat.succ s))
        (andB (Nat.beq (lenL blk) (rowsS s))
          (blockNodesOK S SA SB V0 V1 k blk (Nat.mul (nat_lit 64) s)))) Fb (nat_lit 0))

@[expose] noncomputable def combRows (V J m : Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat) (nat_lit 0)
    (fun j ih => Nat.xor ih (Bool.rec (motive := fun _ => Nat) (nat_lit 0) (rowOf V j)
      (Nat.beq (Nat.land (Nat.shiftRight J j) (nat_lit 1)) (nat_lit 1)))) m

@[expose] noncomputable def rowsNZ (V0 V1 m : Nat) : Bool :=
  Nat.rec (motive := fun _ => Bool) true
    (fun i ih => andB ih (notB (Nat.beq
      (Nat.lor (combRows V0 (Nat.succ i) m) (combRows V1 (Nat.succ i) m)) (nat_lit 0))))
    (Nat.sub (Nat.shiftLeft (nat_lit 1) m) (nat_lit 1))

@[expose] noncomputable def LMall : Nat :=
  Nat.sub (Nat.shiftLeft (nat_lit 1) (nat_lit 279680)) (nat_lit 1)

@[expose] noncomputable def testN (S Da Db : List Nat) (Al Ba Bb : Nat) : Nat :=
  Nat.xor (Nat.land (Nat.xor (mulS S Ba) (mulS Da (mulS S Al))) LMall)
    (Nat.shiftLeft (Nat.land (Nat.xor (mulS S Bb) (mulS Db (mulS S Al))) LMall) (nat_lit 279680))

@[expose] noncomputable def combL (Ts : List Nat) (J : Nat) : Nat :=
  List.rec (motive := fun _ => Nat → Nat) (fun _ => nat_lit 0)
    (fun T _ ih J => Nat.xor (Bool.rec (motive := fun _ => Nat) (nat_lit 0) T
      (Nat.beq (Nat.land J (nat_lit 1)) (nat_lit 1))) (ih (Nat.shiftRight J (nat_lit 1)))) Ts J

@[expose] noncomputable def combNZ (Ts : List Nat) : Bool :=
  Nat.rec (motive := fun _ => Bool) true
    (fun i ih => andB ih (notB (Nat.beq (combL Ts (Nat.succ i)) (nat_lit 0))))
    (Nat.sub (Nat.shiftLeft (nat_lit 1) (lenL Ts)) (nat_lit 1))

@[expose] noncomputable def xorAt (As : List (List Nat)) (s : Nat) : Nat :=
  List.rec (motive := fun _ => Nat) (nat_lit 0) (fun A _ ih => Nat.xor (lget A s) ih) As

@[expose] noncomputable def xorRowL (T : List Nat) (As : List (List Nat)) (s : Nat) : Bool :=
  Nat.beq (lget T s) (xorAt As s)

end CFSG.KC.BM.TwoAC

end
