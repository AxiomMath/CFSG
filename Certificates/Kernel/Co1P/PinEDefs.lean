module

public import Certificates.Data.Kernel.Co1PPin
public import Certificates.Kernel.Co1P.Defs
public import Certificates.Kernel.Co1P.PinERecs
public import Certificates.Kernel.Co1P.PinEHs
public import Certificates.Kernel.Co1P.PinEHis

public section

namespace CertificateChecks.KernelCo1P

open CFSG.KC.Co1B CFSG.KC.Co1P CFSG.KD.Co1P

@[expose] noncomputable def recE (i : Nat) : Nat := tabK 32 PRE i

@[expose] noncomputable def hsE (i : Nat) : Nat := tabK 576 PHS i

@[expose] noncomputable def hisE (i : Nat) : Nat := tabK 576 PHIS i

@[expose] noncomputable def ptPE (i : Nat) : Nat := mulWK (mulWK (hsE i) (repK 1)) (hisE i)

@[expose] noncomputable def skE (s : Nat) : Nat := tabK 64 SKE s

@[expose] noncomputable def ixE (s : Nat) : Nat := tabK 16 IXE s

@[expose] noncomputable def memE (X : Nat) : Bool := memPin 12600 64 15 skE ixE ptPE X

@[expose] noncomputable def hsE_chunk (c : Nat) : Bool := pinChunk (hsAct BK) oneK hsE recE 12600 c

@[expose] noncomputable def hisE_chunk (c : Nat) : Bool := pinChunk (hisAct BIK) oneK hisE recE 12600 c

@[expose] noncomputable def keyE_chunk (c : Nat) : Bool := keyChunk 12600 64 skE ixE ptPE c

end CertificateChecks.KernelCo1P

end
