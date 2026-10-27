module

public import CFSG.Sporadic.Co1Block.PermData

public section

namespace CertificateChecks.KernelCo1B.Bound17591

open CFSG.Sporadic.Co1Block

def xbChunks : Array Nat := Id.run do
  let mut a := Array.replicate 4096 0
  for x in certVecs do
    a := a.modify (x >>> 12) (· ||| (1 <<< (x &&& 4095)))
  return a

end CertificateChecks.KernelCo1B.Bound17591
