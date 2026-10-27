module

public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Rows.Co1PairData

public section

namespace CertificateChecks.KernelCo1B.Pair27202

open CFSG.Sporadic.Co1Schreier.Native CFSG.EvenSporadicStandard.Co1Pair

def pairMats : List Rows × List Rows × Bool :=
  (cpSs.toList ++ (cpTMs.toList.map Array.toList).flatten, [], true)

end CertificateChecks.KernelCo1B.Pair27202
