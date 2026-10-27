module

public import Certificates.Data.Kernel.L52Insp443.Lin

public section

namespace CFSG.KC.L52I

open CFSG.KC.Ord CFSG.KC.LQT.P CFSG.KC.Misc.GLM

@[expose] noncomputable def maskK (bs : List Nat) (m : Nat) : Nat :=
  List.rec (motive := fun _ => Nat → Nat) (fun _ => idK)
    (fun b _ ih m => Bool.rec (motive := fun _ => Nat) (ih (Nat.div m 2))
      (mmulK b (ih (Nat.div m 2))) (Nat.beq (Nat.mod m 2) 1)) bs m

@[expose] noncomputable def nzK (bs : List Nat) (cnt : Nat) : Bool :=
  Nat.rec (motive := fun _ => Bool) true
    (fun m acc => CFSG.KC.Ord.andB (CFSG.KC.Ord.orB (Nat.beq m 0) (CFSG.KC.Ord.notB (Nat.beq (maskK bs m) idK))) acc) cnt

@[expose] noncomputable def ebasK (bs : List Nat) : Bool :=
  CFSG.KC.Ord.andB (allK (fun b => Nat.beq (mmulK b b) idK) bs)
    (CFSG.KC.Ord.andB (allK (fun b => allK (commK b) bs) bs) (nzK bs (Nat.pow 2 (List.length bs))))

@[expose] noncomputable def subKOK (us ws : List Nat) : Bool :=
  CFSG.KC.Ord.andB (ebasK us) (CFSG.KC.Ord.andB (ebasK ws) (CFSG.KC.Ord.andB (allK (fun u => memK u (spanK ws)) us)
    (allK (fun w => allK (commK w) us) ws)))

@[expose] noncomputable def orbK (ps qs : List Nat) (c : Nat) : List Nat :=
  List.zipWith (fun p q => mmulK (mmulK p c) q) ps qs

@[expose] noncomputable def hitsK (L : List Nat) : List Nat → List Nat → Bool :=
  List.rec (motive := fun _ => List Nat → Bool)
    (fun rs => List.rec (motive := fun _ => Bool) true (fun _ _ _ => false) rs)
    (fun b _ ih rs => List.rec (motive := fun _ => Bool) false
      (fun r rs' _ => CFSG.KC.Ord.andB (CFSG.KC.Ord.andB (Nat.blt r (Nat.pow 2 (List.length L))) (Nat.beq (maskK L r) b))
        (ih rs')) rs)

@[expose] noncomputable def nthL (R : List (List Nat)) : Nat → List Nat :=
  List.rec (motive := fun _ => Nat → List Nat) (fun _ => List.nil)
    (fun x _ ih j => Nat.rec (motive := fun _ => List Nat) x (fun j' _ => ih j') j) R

@[expose] noncomputable def irrK (ps qs us ws : List Nat) (R : List (List Nat)) : Bool :=
  Nat.rec (motive := fun _ => Bool) true
    (fun m acc => CFSG.KC.Ord.andB (letB (maskK ws m) fun c => CFSG.KC.Ord.orB (memK c (spanK us))
      (hitsK (List.append us (orbK ps qs c)) ws (nthL R m))) acc)
    (Nat.pow 2 (List.length ws))

end CFSG.KC.L52I

end
