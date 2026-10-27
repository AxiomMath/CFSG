module

public import Certificates.Data.Kernel.SporCov.Census

public section

namespace CFSG.KC.SporCov

@[expose] noncomputable def cenE (E : List Nat → List Nat → Bool) (p : Nat) (H : List (List Nat))
    (k : Nat) (Rp Gs : List (List Nat)) (m : Nat) (g : List Nat) : Bool :=
  cond (Nat.beq (nthN g 0) 0) (E (cw H k p m) [])
    (cond (Nat.beq (nthN g 0) 1) (neOK E (repW (cw H k p m) p))
      (cond (Nat.beq (nthN g 0) 2)
        (Nat.blt (nthN g 1) (lenW Rp) && cjOK E (nthW Rp (nthN g 1)) (nthW Gs (nthN g 2)) (cw H k p m))
        false))

@[expose] noncomputable def headW (T : List (List Nat)) : List Nat := nthW T 0

@[expose] noncomputable def tailW (T : List (List Nat)) : List (List Nat) :=
  List.rec (motive := fun _ => List (List Nat)) [] (fun _ t _ => t) T

@[expose] noncomputable def cenAll (E : List Nat → List Nat → Bool) (p : Nat) (H : List (List Nat))
    (k : Nat) (Rp Gs : List (List Nat)) (P : List Nat) (T : List (List Nat)) : Bool :=
  List.rec (motive := fun _ => List (List Nat) → Bool) (fun _ => true)
    (fun m _ ih T => cenE E p H k Rp Gs m (headW T) && ih (tailW T)) P T

end CFSG.KC.SporCov

end
