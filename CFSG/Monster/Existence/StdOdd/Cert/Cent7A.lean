module

public import CFSG.Monster.Existence.StdOdd.Cert.CentFactsSound
public import Certificates.Certificate6032

public section

namespace CFSG.Monster.Existence.StdOdd.Cert

theorem centFacts7A :
    CentFacts 7 141120 repWord7A (wordOfString "BABABBABAB")
      (fun i => [0, 1, 2, 3, 4, 5, 6].getD i 0)
      [(1, 5), (3, 4)] [(1, 5), (2, 3), (3, 4)] :=
  Certificates.certificate6032

theorem card_centralizer_rep7A :
    Nat.card (Subgroup.centralizer ({rep7A} : Set Rgrp)) = 141120 :=
  card_centralizer_of_centFacts orderOf_rep7A centFacts7A

end CFSG.Monster.Existence.StdOdd.Cert
