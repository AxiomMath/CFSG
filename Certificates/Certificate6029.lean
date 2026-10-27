module

public import CFSG.Monster.Existence.StdOdd.Cert.CentFacts
public import CFSG.Monster.Existence.StdOdd.Cert.RepsInputs
import Certificates.Kernel.StdOdd.C17.Checks

public section

namespace Certificates

open CFSG.Monster.Existence.StdOdd.Cert in
theorem certificate6029 : CentFacts 17 17 repWord17 (wordOfString "BABABBABABABBABB")
    (fun i => [0, 7, 10, 3, 13, 6, 14, 1, 2, 4, 5, 8, 9, 11, 12, 15, 16].getD i 0)
    [(7, 5), (5, 4), (8, 4)] [(7, 5), (1, 3), (3, 3), (6, 3), (2, 4), (4, 4), (5, 4), (8, 4)] :=
  CFSG.KD.StdOdd.Cent.C17.facts17

end Certificates
