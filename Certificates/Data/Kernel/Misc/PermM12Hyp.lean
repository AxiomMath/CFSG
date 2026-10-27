module

public import Certificates.Data.Kernel.LocalQT.Small

public section

namespace CFSG.KC.Misc.M12Hyp

open CFSG.KC.Ord CFSG.KC.LQT.P CFSG.KC.LQT.S

@[expose] noncomputable def encT (t : List Nat) : Nat :=
  List.rec (motive := fun _ => Nat) (nat_lit 0)
    (fun x _ ih => Nat.add x (Nat.mul (nat_lit 32) ih)) t

@[expose] noncomputable def validT (t : List Nat) : Bool :=
  andB (Nat.beq (lenL t) (nat_lit 12))
    (andB (List.rec (motive := fun _ => Bool) true (fun x _ ih => andB (Nat.blt x (nat_lit 12)) ih) t)
      (Nat.beq (mul 12 (inv 12 (encT t)) (encT t)) (one 12)))

@[expose] noncomputable def validL (l : List (List Nat)) : Bool :=
  List.rec (motive := fun _ => Bool) true (fun t _ ih => andB (validT t) ih) l

@[expose] noncomputable def m (s t : Nat) : Nat := mul 12 s t

@[expose] noncomputable def tcK (s t : Nat) : Nat := m (inv 12 (m s t)) (m t s)

@[expose] noncomputable def oneJ (J s : Nat) : Bool := orB (Nat.beq s (one 12)) (Nat.beq s J)

@[expose] noncomputable def nodupL (l : List Nat) : Bool :=
  List.rec (motive := fun _ => Bool) true (fun x xs ih => andB (notB (memL x xs)) ih) l

@[expose] noncomputable def mulCl (l : List Nat) : Bool :=
  allL l fun s => allL l fun t => memL (m s t) l

@[expose] noncomputable def invCl (l : List Nat) : Bool := allL l fun s => memL (inv 12 s) l

@[expose] noncomputable def normBy (H l : List Nat) : Bool :=
  allL H fun c => allL l fun q => memL (m (m c q) (inv 12 c)) l

@[expose] noncomputable def key5 (a0 a1 a2 a3 a4 : Nat) : Nat :=
  Nat.add a0 (Nat.mul 32 (Nat.add a1 (Nat.mul 32 (Nat.add a2 (Nat.mul 32 (Nat.add a3
    (Nat.mul 32 a4)))))))

@[expose] noncomputable def c5135 (H Q Q1 Q2 B G : List Nat) (J E N F X : Nat) : Bool := allBs
  [
    allL G (fun g => Nat.beq (m J g) (m g J)), Nat.beq (lenL H) 192, nodupL H, memL J H,
    allN 4 (fun a0 => allN 4 fun a1 => allN 4 fun a2 => allN 4 fun a3 => allN 12 fun a4 =>
      impB (notB (Nat.beq a0 a1)) (impB (notB (Nat.beq a0 a2)) (impB (notB (Nat.beq a0 a3))
      (impB (notB (Nat.beq a1 a2)) (impB (notB (Nat.beq a1 a3)) (impB (notB (Nat.beq a2 a3))
      (impB (Nat.ble 4 a4) (anyL H fun c =>
        Nat.beq (Nat.land c (nat_lit 33554431)) (key5 a0 a1 a2 a3 a4))))))))),
    allL H (fun t => impB (allL H fun s => Nat.beq (m t s) (m s t)) (oneJ J t)),
    anyL H (fun c => anyL H fun d => notB (Nat.beq (tcK c d) (one 12))),
    Nat.beq (lenL Q) 32, memL (one 12) Q, memL J Q, mulCl Q,
    invCl Q, normBy H Q,
    allL Q (fun s => Bool.rec (motive := fun _ => Bool) (notB (oneJ J s)) (oneJ J s)
      (allL Q fun t => Nat.beq (m s t) (m t s))),
    allL Q (fun s => allL Q fun t => oneJ J (tcK s t)),
    allL Q (fun s => oneJ J (m s s)),
    anyL Q (fun s => andB (notB (Nat.beq s (one 12))) (notB (Nat.beq s J))),
    anyL H (fun c => anyL H fun d => notB (memL (tcK c d) Q)),
    allL H (fun x => impB (Nat.beq (m x (m x x)) (one 12)) (impB (notB (Nat.beq x (one 12)))
      (allL Q fun q => impB (Nat.beq (m q x) (m x q)) (oneJ J q)))),
    memL X Q, notB (Nat.beq X J), Nat.beq (lenL Q1) 8, Nat.beq (lenL Q2) 8,
    nodupL Q1, nodupL Q2, allL Q1 (fun t => memL t Q), allL Q2 (fun t => memL t Q),
    memL (one 12) Q1, memL (one 12) Q2,
    mulCl Q1, mulCl Q2, invCl Q1, invCl Q2, normBy H Q1, normBy H Q2,
    allL Q (fun x => allL Q fun y => impB (Nat.beq (pow 12 x 4) (one 12))
      (impB (notB (Nat.beq (pow 12 x 2) (one 12))) (impB (Nat.beq (m y y) (pow 12 x 2))
      (impB (Nat.beq (m y x) (m (pow 12 x 3) y))
        (orB (andB (memL x Q1) (memL y Q1)) (andB (memL x Q2) (memL y Q2))))))),
    Nat.beq (lenL B) 64, nodupL B, memL (one 12) B, mulCl B, invCl B, allL B (fun t => memL t H),
    memL E B, memL N B, memL F B, memL J B, memL X B,
    allL B (fun s => impB (allL B fun t => Nat.beq (m s t) (m t s)) (impB (Nat.beq (m s s) (one 12))
      (impB (notB (Nat.beq s (one 12))) (Nat.beq s J))))]

end CFSG.KC.Misc.M12Hyp

end
