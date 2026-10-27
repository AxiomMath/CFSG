module

public import Certificates.Data.Kernel.L34Syl.Defs

public section

namespace CFSG.KC.L34Syl

open CFSG.KC.Enum

@[expose] noncomputable def tabEqB (t : Array Nat) (x : Nat) : Bool :=
  t.size == 42 && (List.range 42).all fun i => t[i]! == pg 6 63 x i

end CFSG.KC.L34Syl
