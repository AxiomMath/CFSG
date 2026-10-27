module

public import Certificates.Data.Odd87F3Check
public import CFSG.Sporadic.Schreier.ImagePairs
public meta import Certificates.Data.Odd87F3Check
public meta import CFSG.Sporadic.Schreier.ImagePairs

public section

namespace Certificates.Ivk8Weak

open CFSG.Sporadic.Th.Native CFSG.Sporadic.Schreier.Native CFSG.Sporadic.Schreier
  CFSG.Certificates Certificates.Odd87F3

@[expose] def subprodsT (n : ℕ) : List Table → List Table
  | [] => [idT n]
  | t :: ts => (subprodsT n ts) ++ (subprodsT n ts).map (compT n t)

end Certificates.Ivk8Weak
