module

public import CFSG.Monster.Existence.StdOdd.Cert.CentFacts
public import CFSG.Monster.Existence.StdOdd.Cert.RepsInputs
import Certificates.Kernel.StdOdd.C11.ChecksP

public section

namespace Certificates

open CFSG.Monster.Existence.StdOdd.Cert in
theorem certificate6027 : CentFacts 11 66 repWord11 (wordOfString "BBABBABBABABABABABB")
    (fun i => [0, 4, 7, 3, 8, 1, 2, 5, 6, 9, 10].getD i 0)
    [(4, 5), (3, 3), (1, 4)] [(4, 5), (2, 3), (3, 3), (1, 4), (5, 4)] :=
  CFSG.KD.StdOdd.Cent.C11.facts11

end Certificates
