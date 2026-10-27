module

public import Certificates.Data.Kernel.SporSch.LySeven

public section

namespace CFSG.KS.SporSch.LySev

open CFSG.KC.Enum CFSG.KS

@[expose] noncomputable def mul7K (X Y : Nat) : Nat :=
  foldN (nat_lit 49) (fun t acc => Nat.lor acc (Nat.shiftLeft
    (Nat.mod (foldN (nat_lit 7) (fun l s => Nat.add s
      (Nat.mul (d3 X (Nat.add (Nat.mul (nat_lit 7) (Nat.div t (nat_lit 7))) l))
        (d3 Y (Nat.add (Nat.mul (nat_lit 7) l) (Nat.mod t (nat_lit 7)))))) (nat_lit 0)) (nat_lit 5))
    (Nat.mul (nat_lit 3) t))) (nat_lit 0)

@[expose] noncomputable def congr7K (P S : Nat) : Nat :=
  strictN (mul7K P S) (fun PS =>
  foldN (nat_lit 49) (fun t acc => Nat.lor acc (Nat.shiftLeft
    (Nat.mod (foldN (nat_lit 7) (fun l s => Nat.add s
      (Nat.mul (d3 PS (Nat.add (Nat.mul (nat_lit 7) (Nat.div t (nat_lit 7))) l))
        (d3 P (Nat.add (Nat.mul (nat_lit 7) (Nat.mod t (nat_lit 7))) l)))) (nat_lit 0)) (nat_lit 5))
    (Nat.mul (nat_lit 3) t))) (nat_lit 0))

@[expose] noncomputable def id7K : Nat :=
  foldN (nat_lit 7) (fun i acc => Nat.lor acc (Nat.shiftLeft (nat_lit 1) (Nat.mul (nat_lit 24) i)))
    (nat_lit 0)

@[expose] noncomputable def red49 (X : Nat) : Bool :=
  bAnd(allN (nat_lit 49) (fun t => Nat.blt (d3 X t) (nat_lit 5)),
    Nat.blt X (Nat.shiftLeft (nat_lit 1) (nat_lit 147)))

@[expose] noncomputable def pk49 (a : Array Nat) : Nat :=
  foldN (nat_lit 49) (fun t acc => Nat.lor acc (Nat.shiftLeft (a[t]!) (Nat.mul (nat_lit 3) t)))
    (nat_lit 0)

end CFSG.KS.SporSch.LySev

end
