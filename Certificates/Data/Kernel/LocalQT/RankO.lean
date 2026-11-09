module

public import Certificates.Data.Kernel.LocalQT.RankQ

public section

namespace CFSG.KC.LQT.RB

open CFSG.KC.Ord CFSG.KC.LQT.P CFSG.KC.LQT.S CFSG.KC.LQT.L CFSG.KC.LQT.PW CFSG.KC.LQT.BC
open CFSG.KC.LQT.PP CFSG.KC.LQT.BW CFSG.KC.LQT.BT CFSG.KC.LQT.RW CFSG.KC.LQT.RF

@[expose] noncomputable def dfsWO (mul : Nat → Nat → Nat) (invs : List Nat) (d : Nat) :
    Nat → List Nat → List Nat → Bool :=
  Nat.rec (motive := fun _ => Nat → List Nat → List Nat → Bool) (fun _ _ _ => true)
    (fun _ ih h L S => anyL invs fun c => andB (andB (Nat.blt h c) (andB (notB (hasW S c))
      (allL L fun l => Nat.beq (mul c l) (mul l c))))
      (ih c (List.cons c L) (appK S (mapW (mul c) S)))) d

@[expose] noncomputable def branchFO (mul : Nat → Nat → Nat) (invs : List Nat) (z d c : Nat) :
    Bool :=
  notB (andB (andB (notB (hasW [0, z] c)) (Nat.beq (mul c z) (mul z c)))
    (dfsWO mul invs d c [c, z] (appK [0, z] (mapW (mul c) [0, z]))))

@[expose] noncomputable def eqvRU (W g N : Nat) (CT QT UP UI : Nat → Nat) (x : Nat) : Bool :=
  letRQ (QT x) fun s => andB (Nat.beq (imgW W s 0) x)
    (andB (Bool.rec (motive := fun _ => Bool)
      (andB (Nat.blt (fieldT W UP x) x) (andB (Nat.blt (fieldT W UI x) g)
        (Nat.beq (imgW W (QT (fieldT W UP x)) (fieldT W CT (fieldT W UI x))) x)))
      true (Nat.beq x 0))
    (allR 0 g fun j => letRQ (fieldT W CT (Nat.add (Nat.mul x (Nat.add g g)) j)) fun y =>
      andB (Nat.blt y N) (allR 0 g fun i =>
        Nat.beq (imgW W (QT y) (fieldT W CT i))
          (fieldT W CT (Nat.add (Nat.mul (imgW W s (fieldT W CT i)) (Nat.add g g)) j)))))

@[expose] noncomputable def rankBO (W N : Nat) (QT : Nat → Nat) (d zi lo len : Nat) : Bool :=
  (fun (invs : List Nat) => allL (sliceK invs lo len) (branchFO (mulRQ W QT) invs zi d))
    (invsB N (mulRQ W QT))

end CFSG.KC.LQT.RB

end
