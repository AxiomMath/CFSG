module

public import CFSG.Monster.Existence.StdOdd.Cert.CentFactsSound
public import Certificates.Certificate6030

public section

namespace CFSG.Monster.Existence.StdOdd.Cert

theorem centFacts19 :
    CentFacts 19 19 repWord19 (wordOfString "BBABBABBABABAB")
      (fun i => [0, 4, 6, 10, 2, 8, 1, 3, 5, 7, 9, 11, 12, 13, 14, 15, 16, 17, 18].getD i 0)
      [(4, 5), (6, 5)] [(4, 5), (6, 5), (3, 3), (5, 3), (1, 4), (2, 4), (7, 4), (8, 4), (9, 4)] :=
  Certificates.certificate6030

theorem card_centralizer_rep19 :
    Nat.card (Subgroup.centralizer ({rep19} : Set Rgrp)) = 19 :=
  card_centralizer_of_centFacts orderOf_rep19 centFacts19

end CFSG.Monster.Existence.StdOdd.Cert
