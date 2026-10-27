module

public import Certificates.Data.Kernel.Misc.Coset.Act

public section

namespace CFSG.KC.MiscCoset.CovAct

open CFSG.KC.MiscCoset.Act

@[expose] noncomputable def stepE (q s e : Nat) : Nat :=
  Nat.add (Nat.mul q (Nat.div e q)) (Nat.mod (Nat.add (Nat.mod s q) (Nat.mod e q)) q)

@[expose] noncomputable def stepS (A : Nat → Nat) (q L s c : Nat) : Nat :=
  stepE q s (A (Nat.add (Nat.mul (Nat.div s q) L) c))

@[expose] noncomputable def walkS (A : Nat → Nat) (q L : Nat) (w : List Nat) (s : Nat) : Nat :=
  List.rec (motive := fun _ => Nat → Nat) (fun y => y) (fun c _ ih y => ih (stepS A q L y c)) w s

@[expose] noncomputable def invC (c : Nat) : Nat :=
  Bool.rec (Nat.pred c) (Nat.succ c) (Nat.beq (Nat.mod c 2) 0)

@[expose] noncomputable def cpOK (A : Nat → Nat) (q N mb L : Nat) (mac : List (List Nat))
    (chk : List (List Nat × Nat)) (p : Nat) : Bool :=
  andB (allR 0 (Nat.add mb mb) fun c =>
      andB (Nat.blt (A (Nat.add (Nat.mul p L) c)) (Nat.mul q N))
        (Nat.beq (stepS A q L (stepS A q L (Nat.mul q p) c) (invC c)) (Nat.mul q p)))
  (andB (List.rec (motive := fun _ => Nat → Bool) (fun _ => true)
      (fun w _ ih j => andB
        (Nat.beq (A (Nat.add (Nat.mul p L) (Nat.add (Nat.add mb mb) j))) (walkS A q L w (Nat.mul q p)))
        (ih (Nat.succ j))) mac 0)
    (List.rec (motive := fun _ => Bool) true
      (fun wt _ ih => andB (Nat.beq (walkS A q L wt.1 (Nat.mul q p)) (Nat.add (Nat.mul q p) wt.2)) ih)
      chk))

end CFSG.KC.MiscCoset.CovAct

end
