module

public import CFSG.LocalAnalysis.RankThreeTheoremC.ONPair.ModelFacts
import Certificates.Kernel.Sporadic.ONPv.Facts
import Certificates.Certificate2212

public section

namespace Certificates

open CFSG.ONSchreier CFSG.LocalAnalysis.RankThreeTheoremC.ONPair CFSG.ClassicalInvolution.Phan.Q3G
open CertificateChecks.KernelSpor.ONPv

theorem coe_wordVal_qP
    (r : List (Fin 4 × Bool)) :
    ((wordVal qP r : Pv) : Equiv.Perm (Fin N)) =
      wordVal (fun i : Fin 4 => hval qWords[i.val]!) r :=
  (wordVal_map Pv.subtype qP r).symm

theorem certificate753505 : 
    (∀ r ∈ CFSG.LocalAnalysis.RankThreeTheoremC.ONPair.sl3Rels7,
      CFSG.ClassicalInvolution.Phan.Q3G.wordVal CFSG.LocalAnalysis.RankThreeTheoremC.ONPair.qP r =
        1) ∧
    CFSG.ClassicalInvolution.Phan.Q3G.wordVal CFSG.LocalAnalysis.RankThreeTheoremC.ONPair.qP
        (CFSG.ClassicalInvolution.Phan.Q3G.decodeWord 4
          CFSG.LocalAnalysis.RankThreeTheoremC.ONPair.sl3OmegaCodes7) = 1 ∧
    CFSG.LocalAnalysis.RankThreeTheoremC.ONPair.qP 0 ≠ 1 ∧
    ∀ i, (CFSG.LocalAnalysis.RankThreeTheoremC.ONPair.qP i :
      Equiv.Perm (Fin CFSG.ONSchreier.N)) 0 = 0 :=
  ⟨fun r hr => Subtype.ext ((coe_wordVal_qP r).trans (pv505_rels r hr)),
    Subtype.ext ((coe_wordVal_qP _).trans pv505_omega),
    fun h => pv505_ne (congrArg Subtype.val h), pv505_fix⟩

end Certificates
