module

public import Certificates.Data.Kernel.RuIdx2K
public import Certificates.Data.Kernel.SporLatDc

public section

namespace CFSG.KC.RuIdx2

open CFSG.KC.SLDc

@[expose] noncomputable def unW (W : Nat) : List Nat :=
  (List.range (Nat.land W (nat_lit 255))).map fun i => fld(W, Nat.add (nat_lit 8) (Nat.shiftLeft i (nat_lit 2)), nat_lit 15)

@[expose] noncomputable def conjW (ci c y : List Nat) (t ti s o : Nat) : List Nat :=
  ci ++ (List.replicate s ti ++ (List.replicate o t ++ (y ++ (List.replicate s t ++ c))))

@[expose] noncomputable def vaK (C : DcCtx) (E : List (List Nat)) (u w : List Nat) : Bool :=
  isW C w && memW C E (u, [], 0) (genLab C w)

end CFSG.KC.RuIdx2

end
