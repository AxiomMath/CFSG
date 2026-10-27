module

public import Certificates.Data.Kernel.LocalQT.Syl
public import Certificates.Data.Kernel.LocalQT.Word

public section

namespace CFSG.KC.B45P

open CFSG.KC.Ord CFSG.KC.LQT.P CFSG.KC.LQT.W CFSG.KC.LQT.Syl

@[expose] noncomputable def genWE (n cA cB : Nat) (RL : List Nat)
    (e : Nat × List (List Int) × List Nat × List Nat) : Bool :=
  andB (Nat.beq (lenK e.2.1) 2)
    (letB (getK RL e.1 (one n)) fun t =>
      letB (evalZK n [cA, cB] (getK e.2.1 0 [])) fun c1 =>
        letB (evalZK n [cA, cB] (getK e.2.1 1 [])) fun c2 =>
          letB (conj n c1 t) fun x1 => letB (conj n c2 t) fun x2 =>
            andB (Nat.beq (evalWK n [t, x1, x2] e.2.2.1) cA)
              (Nat.beq (evalWK n [t, x1, x2] e.2.2.2) cB))

@[expose] noncomputable def genWK (n cA cB : Nat) (RL : List Nat)
    (tab : List (Nat × List (List Int) × List Nat × List Nat)) : Bool :=
  List.rec (motive := fun _ => Bool) true (fun e _ ih => andB (genWE n cA cB RL e) ih) tab

end CFSG.KC.B45P

end
