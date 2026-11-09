module

public import Certificates.Data.Kernel.Co1PPin
public import Certificates.Kernel.Co1P.Defs
public import Certificates.Kernel.Co1P.PinERecs
public import Certificates.Kernel.Co1P.PinEHs
public import Certificates.Kernel.Co1P.PinEHis
public import Certificates.Kernel.Co1P.PinEG

public section

namespace CertificateChecks.KernelCo1P

open CFSG.KC.Co1B CFSG.KC.Co1P CFSG.KD.Co1P

@[expose] noncomputable def recE (i : Nat) : Nat := tabK 32 PRE i

@[expose] noncomputable def tabGE (g w : Nat) (C : List Nat) (i : Nat) : Nat :=
  CFSG.KLie.CT.fget (CFSG.KC.Co1F2.getL (nat_lit 0) C (Nat.div i g)) (Nat.mod i g) w

@[expose] noncomputable def hsE (i : Nat) : Nat := tabGE 256 576 HSGE i

@[expose] noncomputable def hisE (i : Nat) : Nat := tabGE 256 576 HISGE i

@[expose] noncomputable def ptPE (i : Nat) : Nat := mulWK (mulWK (hsE i) (repK 1)) (hisE i)

@[expose] noncomputable def skE (s : Nat) : Nat := tabGE 1024 64 SKGE s

@[expose] noncomputable def ixE (s : Nat) : Nat := tabGE 1024 16 IXGE s

@[expose] noncomputable def memE (X : Nat) : Bool := memPin 12600 64 15 skE ixE ptPE X

@[expose] noncomputable def hsE_chunk (c : Nat) : Bool := pinChunk (hsAct BK) oneK hsE recE 12600 c

@[expose] noncomputable def hisE_chunk (c : Nat) : Bool := pinChunk (hisAct BIK) oneK hisE recE 12600 c

@[expose] noncomputable def keyE_chunk (c : Nat) : Bool := keyChunk 12600 64 skE ixE ptPE c

end CertificateChecks.KernelCo1P

end
