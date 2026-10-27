module

public import CFSG.Monster.Existence.StdOdd.Cert.Centralizers
public import CFSG.Monster.Existence.StdOdd.Cert.Cent5
public import CFSG.Monster.Existence.StdOdd.Cert.Cent7A
public import CFSG.Monster.Existence.StdOdd.Cert.Cent7B
public import CFSG.Monster.Existence.StdOdd.Cert.Cent11
public import CFSG.Monster.Existence.StdOdd.Cert.Cent13
public import CFSG.Monster.Existence.StdOdd.Cert.Cent17
public import CFSG.Monster.Existence.StdOdd.Cert.Cent19

public section

namespace CFSG.Monster.Existence.StdOdd.Cert

theorem centralizerFacts_std :
    CentralizerFacts Rgrp :=
  centralizerFacts_of_reps card_centralizer_rep5 card_centralizer_rep7A card_centralizer_rep7B
    card_centralizer_rep11 card_centralizer_rep13 card_centralizer_rep17 card_centralizer_rep19

end CFSG.Monster.Existence.StdOdd.Cert
