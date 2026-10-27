module

public import CFSG.Monster.Existence.StdOdd.Cert.CentFacts
public import CFSG.Monster.Existence.StdOdd.Cert.RepsInputs
import Certificates.Kernel.StdOdd.C19.ChecksP

public section

namespace Certificates

open CFSG.Monster.Existence.StdOdd.Cert in
theorem certificate6030 : CentFacts 19 19 repWord19 (wordOfString "BBABBABBABABAB")
    (fun i => [0, 4, 6, 10, 2, 8, 1, 3, 5, 7, 9, 11, 12, 13, 14, 15, 16, 17, 18].getD i 0)
    [(4, 5), (6, 5)] [(4, 5), (6, 5), (3, 3), (5, 3), (1, 4), (2, 4), (7, 4), (8, 4), (9, 4)] :=
  CFSG.KD.StdOdd.Cent.C19.facts19

end Certificates
