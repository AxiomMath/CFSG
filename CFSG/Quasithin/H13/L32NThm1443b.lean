module

public import CFSG.Quasithin.H13.GoldschmidtQ8SqE9
public import CFSG.Quasithin.H13.L32NLem1445d
public import CFSG.Quasithin.H13.L32NLem1445a

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Blueprint

theorem thm1443One_of_core (hI45 : G23Type.StatementI45) (h1332 : Stmt13_3_2)
    (h1334 : A6.Stmt13_3_4) (h1222 : Stmt12_2_2) (h12213 : Stmt12_2_13) (h37 : A37ForSQTK)
    (h38 : A38ForSQTK) (h39 : A39ForSQTK) (hRest : Lemma14323Rest) (hCTL : Lemma1444CTL) :
    Thm1443One :=
  have h14453 := lemma1445Three_of_inputs h1332 h1334 h1222 h12213 h37 h38 h39 hRest
    (lemma1445One_of_inputs h1332 h1334 h1222 h12213 h37 h38 h39 hRest hCTL)
  thm1443One_of_inputs hI45 h1332 h1334 h1222 h12213 h37 h38 h39
    (lemma1444One_of_inputs h1332 h1334 h1222 h12213 h37 h38 h39 hRest)
    (lemma1444Two_of_inputs h1332 h1334 h1222 h12213 h37 h38 h39 hRest
      (lemma1444Six_of_inputs h1332 h1334 h1222 h12213 h37 h38 h39 hRest hCTL))
    (lemma1444Four_of_inputs h1332 h1334 h1222 h12213)
    (lemma1444Seven_of_inputs h1332 h1334 h1222 h12213 h37 h38 h39 hRest)
    (lemma1445Two_of_inputs h1332 h1334 h1222 h12213 h37 h38 h39 hRest hCTL h14453)
    h14453 q8SqE9Decomp_holds

end CFSG.Quasithin.H13
