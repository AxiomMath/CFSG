module

public import Certificates.Certificate6018

public section

namespace CFSG.Monster.AxisCount.HS

open CFSG.Monster CFSG.Monster.B.Short

theorem stabAll_ok :
    ∀ (i : Fin 12), ∀ k, k < 2 → wordLin (uW i k) (vv i) = vv i :=
  Certificates.certificate6018.1

theorem trace_injective :
    Function.Injective fun i : Fin 12 => trA2 (vv i) :=
  Certificates.certificate6018.2.1

theorem e1UAll_ok (i : Fin 12) :
    ∀ k, k < 2 → bbU i k < 10 ∧
      wordLin (uW i k) (wordLin (Cert.gammaW i) aStarMinus) =
        wordLin (hppU i k ++ Cert.gammaW i) (wordLin (babyW (bbU i k)) aStarMinus) :=
  Certificates.certificate6018.2.2.1 i

theorem e2UAll_ok (i : Fin 12) :
    ∀ k, k < 2 → wordLin (hppU i k) aStar = aStar :=
  Certificates.certificate6018.2.2.2 i

end CFSG.Monster.AxisCount.HS
