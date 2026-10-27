module

public import Certificates.Data.Kernel.HMathieu.FixCert
public import Certificates.Data.Kernel.HMathieu.Tab

public section

namespace CFSG.KC.HMathieu

open CFSG.Quasithin.H.Mathieu

@[expose] def ascFrom (a : Nat) : List Nat → Bool
  | [] => true
  | b :: l => Nat.blt a b && ascFrom b l

@[expose] def ascB : List Nat → Bool
  | [] => true
  | a :: l => ascFrom a l

@[expose] noncomputable def fixListOK (n : Nat) (M J R : List Nat) : Bool :=
  J.all (fun j => decide (j < n)) && imgOK M J &&
    R.all (fun v => decide (v < 2 ^ n) && actM M v == v) && ascB R &&
    decide (2 ^ (n - J.length) ≤ R.length)

@[expose] noncomputable def fixAllK (ok : List Nat → Bool) (cc lift : List Nat) (n : Nat) :
    List Nat → List (List Nat) → List (List Nat) → Bool
  | [], _, _ => true
  | e :: E, Js, Rs =>
    fixListOK n (matP cc lift n e) (Js.headD []) (Rs.headD []) && ok (Rs.headD []) &&
      fixAllK ok cc lift n E Js.tail Rs.tail

end CFSG.KC.HMathieu

end
