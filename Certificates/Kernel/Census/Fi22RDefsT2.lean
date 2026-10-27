module

public import Certificates.Kernel.Census.Fi22RDefs
public import Certificates.Kernel.Census.Fi22PkT2R

public section

namespace CertificateChecks.KernelCensus.Fi22K.T2

open CFSG.KC.Census CFSG.ComponentClassification.RankTwoSporadic.Fi22 CertificateChecks.KernelCensus.Fi22K

@[expose] noncomputable def entT2 (j : Nat) : Bool :=
  bAnd(pentryOKB 3510 12 inXK 2 [] #[] 10 fi22T2Root j,
    pentryOKB 3510 12 inXK 1 [] #[] 10 fi22T2Root j)

end CertificateChecks.KernelCensus.Fi22K.T2

end
