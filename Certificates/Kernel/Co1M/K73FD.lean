module

public import Certificates.Kernel.Co1M.D10073
public import Certificates.Kernel.Co1M.D10073F
public import Certificates.Kernel.Co1M.Data10071
public import Certificates.Kernel.VecCert.Co1.Data
public import CFSG.Certificates.Kernel.Co1M.OrbitMem
public import Certificates.Data.Kernel.Co1M.Odd73F

public section

namespace CFSG.KD.Co1M

open CFSG.KC.Odd73 CFSG.KC.Co1F2 CFSG.KC.M1F2 CFSG.KLie.CT CFSG.KC.Co1M CFSG.KC.VecK

@[expose] noncomputable def t4K73 (x : Nat) : Bool :=
  andB (notB (Nat.beq x (nat_lit 0))) (andB (notB (dotK (nat_lit 24) x (vmF (nat_lit 24) QT73 x)))
    (notB (orbMemK (nat_lit 98280) (lk CertificateChecks.KernelVec.Co1.S (nat_lit 32)) (nat_lit 17) x)))

@[expose] noncomputable def fx73F (j : Nat) : Bool :=
  Nat.beq (cnt7K t4K73 (trK (nat_lit 24) (getL (nat_lit 0) R73 (nat_lit 70)))
      (trK (nat_lit 24) (getL (nat_lit 0) R73 (nat_lit 73)))
      (trK (nat_lit 24) (getL (nat_lit 0) R73 (nat_lit 76)))
      (List.drop (nat_lit 6) FR3) (offK FR3 (nat_lit 6) j))
    (pack7 (List.getD FC73 j List.nil))

@[expose] noncomputable def fx73G (j : Nat) : Bool := fx73F (Nat.add (nat_lit 32) j)

end CFSG.KD.Co1M

end
