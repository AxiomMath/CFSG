module

public import Certificates.Kernel.Census.Fi22RDefs
public import Certificates.Kernel.Census.Fi22PkT1R

public section

namespace CertificateChecks.KernelCensus.Fi22K.T1

open CFSG.KC.Census CFSG.ComponentClassification.RankTwoSporadic.Fi22 CertificateChecks.KernelCensus.Fi22K

@[expose] noncomputable def entT1 (j : Nat) : Bool :=
  bAnd(pentryOKB 3510 12 inXK 2 [694] #[] 16 fi22T1Root j,
    pentryOKB 3510 12 inXK 1 [694] #[] 16 fi22T1Root j)

end CertificateChecks.KernelCensus.Fi22K.T1

end
