module

public import CFSG.RankThree.PartOne.SPOR.Co1SylowData

public section

namespace CertificateChecks.KernelCo1Syl5

open CFSG.Sporadic.Co1Schreier.Native CFSG.RankThree.PartOne.SPOR

def sylDag : List Rows × List Rows × Bool := dag co1PlaneBase co1SylowDerivs

end CertificateChecks.KernelCo1Syl5

end
