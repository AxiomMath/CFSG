module

public import CFSG.Quasithin.H13.A6S13816u
public import CFSG.Quasithin.H13.A6S13816k
public import CFSG.Quasithin.H13.KGFactSzCent

public section

namespace CFSG.Quasithin.H13.A6

open CFSG.Open hiding StatedSL StatedSp
open CFSG.QuasithinUnique CFSG.Quasithin CFSG.LieType.BorelTits

theorem lem13816_holds
    (h36 : QuasithinUnique.Vol2Native.A36CoreForSQTKCat)
    (h37 : A37ForSQTK) (h38 : A38ForSQTK) (h122 : CFSG.Quasithin.Lemma122A)
    (h139 : Stmt13_3_9) (h1334 : Stmt13_3_4) (h1337 : Stmt13_3_7) (h13 : Lem13813)
    (hD36 : D36) (hD37 : D37) (hD321 : D321) (hI5 : Insp5a) (hA21 : AsA21SQTKSection)
    (h56 : AsB56) (h310 : D310) (h391 : D391) (hI4 : Insp4) : Lem13816 :=
  lem13816_of_cases h36 h37 h38 hD36 hD37 hD321 hI5 h139 h1334 h13
    (case13816L32_of h37 h38 h122)
    (case13816L2_of h37 h38 h122 h1334 h1337 h13 (case13816L2Hat_holds h36 h37 h38 h122 h139
      h1334 h1337 h13 hD36 hD37 hD321 hI5 hA21 h56))
    (case13816SzPair_of h37 h38 h1334 h139 h13 KGSz.szCent_holds
      (case13816SzPairMod_of h36 h37 h38 hD36 hD37 hD321 hI5 h139 h1334 h13 KGSz.szEnd_holds))
    (case13816SzNormal_of h1334 h139 h13 KGSz.szCent_holds
      (case13816SzNormalMod_of h36 h37 h38 h310 h391 hI4 h139 h1334 h13 KGSz.szEnd_holds))

end CFSG.Quasithin.H13.A6
