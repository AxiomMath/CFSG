module

public import CFSG.Monster.Existence.StdOdd.Cert.CentFactsSound
public import Certificates.Certificate6028

public section

namespace CFSG.Monster.Existence.StdOdd.Cert

theorem centFacts13 :
    CentFacts 13 13 repWord13 (wordOfString "ABBABABBABBABABABABBABBAB")
      (fun i => [0, 1, 7, 6, 8, 2, 3, 4, 5, 9, 10, 11, 12].getD i 0)
      [(1, 5), (6, 5)] [(1, 5), (6, 5), (5, 3), (2, 4), (3, 4), (4, 4)] :=
  Certificates.certificate6028

theorem card_centralizer_rep13 :
    Nat.card (Subgroup.centralizer ({rep13} : Set Rgrp)) = 13 :=
  card_centralizer_of_centFacts orderOf_rep13 centFacts13

end CFSG.Monster.Existence.StdOdd.Cert
