module

public import CFSG.Monster.Existence.StdOdd.Cert.CentFacts
public import CFSG.Monster.Existence.StdOdd.Cert.RepsInputs
import Certificates.Kernel.StdOdd.C5.ChecksP

public section

namespace Certificates

open CFSG.Monster.Existence.StdOdd.Cert in
theorem certificate6031 : CentFacts 5 100800 repWord5 (wordOfString "ABBABAB")
    (fun i => [0, 2, 3, 1, 4].getD i 0)
    [(2, 5), (1, 4)] [(2, 5), (1, 4)] :=
  CFSG.KD.StdOdd.Cent.C5.facts5

end Certificates
