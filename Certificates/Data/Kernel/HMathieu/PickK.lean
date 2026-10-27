module

public import Certificates.Data.Kernel.HMathieu.PredXi

public section

namespace CFSG.KC.HMathieu

open CFSG.Quasithin.H.Mathieu

@[expose] noncomputable def reduceK (bs : List Nat) (x : Nat) : Nat :=
  List.rec (motive := fun _ => Nat → Nat) (fun x => x)
    (fun b _ ih x => ih (bif Nat.ble x (Nat.xor x b) then x else Nat.xor x b)) bs x

@[expose] noncomputable def insK (r : Nat) (l : List Nat) : List Nat :=
  List.rec (motive := fun _ => List Nat) [r]
    (fun b bs ih => bif Nat.blt b r then r :: b :: bs else b :: ih) l

@[expose] noncomputable def pickK (vs : List Nat) : List Nat :=
  (vs.foldl (fun (st : List Nat × List Nat) v =>
    bif Nat.beq (reduceK st.1 v) 0 then st else (insK (reduceK st.1 v) st.1, v :: st.2))
    ([], [])).2

@[expose] noncomputable def predXiKF (n r fb : Nat) (F : List (List Nat)) (m : Nat) (L S : List Nat)
    (st : List (List Nat) × List Nat) : Bool :=
  L.isEmpty || (decide (L.length ≤ 4) && decide (L.length + 2 ≤ n - Nat.log 2 st.2.length) &&
    (L.length != 4 || (decide (st.2.length ≤ 2 ^ fb) &&
      indepK r (xiCandsT F m S) (pickK (xiCandsT F m S)))))

end CFSG.KC.HMathieu

end
