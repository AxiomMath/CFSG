module

public import Certificates.Kernel.Census.Fi22RDefs
public import Certificates.Kernel.Census.Fi22PkT0R

public section

namespace CertificateChecks.KernelCensus.Fi22K.T0

open CFSG.KC.Census CFSG.ComponentClassification.RankTwoSporadic.Fi22 CertificateChecks.KernelCensus.Fi22K

@[expose] noncomputable def entT0 (j : Nat) : Bool :=
  bAnd(pentryOKB 3510 12 inXK 2 [694, 182] #[] 13 fi22T0Root j,
    pentryOKB 3510 12 inXK 1 [694, 182] #[] 13 fi22T0Root j)

end CertificateChecks.KernelCensus.Fi22K.T0

end
