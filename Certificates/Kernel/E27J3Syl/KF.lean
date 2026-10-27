module

public import Certificates.Kernel.E27J3Syl.DV
public import Certificates.Data.Kernel.Spor.PEnumB
public import Certificates.Data.Kernel.Spor.HKeyB
public import Certificates.Kernel.E27J3Syl.D

public section

namespace CFSG.KD.E27J3S

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.PEnum CFSG.KS.MulH CFSG.KS.PEnumB

@[expose] def bsC : List Nat := [0, 1, 3, 2]

@[expose] noncomputable def c131001Pb (k : Nat) : Bool :=
  slK SE.cnt (penumPtB 6156 13 (mask 13) bsC SE.GI 2 SE.cnt SE.T SE.PL SE.POS SE.SRT SE.SRI)
    (Nat.mul 16 k) 16

@[expose] noncomputable def jHv (i : Nat) : Bool := Nat.beq (hkeyB 6156 13 (mask 13) (SE.T i)) (SEV i)

@[expose] noncomputable def c131001Hv (k : Nat) : Bool := slK SE.cnt jHv (Nat.mul 16 k) 16

@[expose] noncomputable def c131001Hsv : Bool := slK SE.cnt (hsortVK SE.cnt SEV SE.HS SE.HSI) 0 256

@[expose] noncomputable def c131001Fp (k : Nat) : Bool :=
  slK (Nat.mul SE.cnt 4) (findProdB SE.cnt 13 (mask 13) bsC 4 SE.T (bothK 2 SE.GI SEI) SECl)
    (Nat.mul 256 k) 256

end CFSG.KD.E27J3S

end
