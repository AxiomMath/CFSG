module

public import Certificates.Kernel.Co2Jc.OffData
public import Certificates.Data.Kernel.M1F2

public section

namespace CertificateChecks.KernelCo2Jc

open CFSG.KC.Enum

@[expose] noncomputable def PT (i : Nat) : Nat := OP i

@[expose] noncomputable def colsOf (A : Nat) : List Nat :=
  (List.range 10).map fun c => CFSG.KC.M1F2.rowF 10 A c

@[expose] noncomputable def tabsL : List (List Nat) := (List.range 256).map fun i => colsOf (PT i)

@[expose] noncomputable def mulL (s i : Nat) : Nat := pg (nat_lit 10) (nat_lit 1023) (OM s) i

@[expose] noncomputable def oi (j i : Nat) : Nat := pg (nat_lit 10) (nat_lit 1023) (OI j) i

@[expose] noncomputable def parL (i : Nat) : Nat := oi 0 i

@[expose] noncomputable def parG (i : Nat) : Nat := oi 1 i

@[expose] noncomputable def gI (k : Nat) : Nat := oi 2 k

@[expose] noncomputable def FX (i : Nat) : Nat := OF i

@[expose] noncomputable def stI (q s : Nat) : Nat := pg (nat_lit 10) (nat_lit 1023) (OS q) s

end CertificateChecks.KernelCo2Jc
