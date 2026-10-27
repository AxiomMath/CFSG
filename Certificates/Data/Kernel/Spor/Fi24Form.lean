module

public import CFSG.Certificates.Kernel.Common.Loop
public import Certificates.Data.Kernel.Spor.Fi24FixK

public section

namespace CFSG.KC.Fi24Form

open CFSG.KC.Loop CFSG.KC.LceS CFSG.KC.Fi24FixK

@[expose] noncomputable def LOF : Nat := Nat.sub (Nat.shiftLeft (nat_lit 1) (nat_lit 609961)) (nat_lit 1)

@[expose] noncomputable def rowP (P i : Nat) : Nat := Nat.land (Nat.shiftRight P (Nat.mul (nat_lit 781) i)) RM

@[expose] noncomputable def transOK (P1 P2 Q1 Q2 lo m hi : Nat) : Bool :=
  allBelow m hi (fun t => letB (Nat.add lo t) (fun i =>
    letB (rowP P1 i) (fun x1 =>
    letB (rowP P2 i) (fun x2 =>
      allBelow (nat_lit 781) (nat_lit 13) (fun j => letB j (fun j =>
        andB (Nat.beq (bitAt x1 j) (bitAt (rowP Q1 j) i))
          (Nat.beq (bitAt x2 j) (bitAt (rowP Q2 j) i))))))))

@[expose] noncomputable def transM (X Y lo m hi : Nat) : Bool :=
  transOK (Nat.land X LOF) (Nat.shiftRight X (nat_lit 609961)) (Nat.land Y LOF)
    (Nat.shiftRight Y (nat_lit 609961)) lo m hi

end CFSG.KC.Fi24Form

end
