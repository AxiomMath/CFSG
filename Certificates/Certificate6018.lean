module

public import CFSG.Monster.AxisCount.HSIdentBase
import Certificates.Kernel.KDenseP.Axis.C6018

public section

namespace Certificates

open CFSG CFSG.Monster CFSG.Monster.AxisCount CFSG.Monster.AxisCount.HS CFSG.Monster.B.Short in
theorem certificate6018 : (∀ (i : Fin 12), ∀ k, k < 2 → wordLin (uW i k) (CFSG.Monster.AxisCount.HS.vv i) = CFSG.Monster.AxisCount.HS.vv i)
    ∧ (Function.Injective fun i : Fin 12 => trA2 (CFSG.Monster.AxisCount.HS.vv i))
    ∧ (∀ (i : Fin 12), ∀ k, k < 2 → bbU i k < 10 ∧
      wordLin (uW i k) (wordLin (Cert.gammaW i) aStarMinus) =
        wordLin (hppU i k ++ Cert.gammaW i) (wordLin (babyW (bbU i k)) aStarMinus))
    ∧ (∀ (i : Fin 12), ∀ k, k < 2 → wordLin (hppU i k) aStar = aStar) :=
  CertificateChecks.KernelKDenseP.Axis.c6018

end Certificates
