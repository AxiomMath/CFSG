module

public import CFSG.LocalAnalysis.ComponentClassification.RankTwoSporadicDefs
public import CFSG.Sporadic.HeldB.AutData
import Certificates.Kernel.Census.HeC.Final
import CFSG.LocalAnalysis.ComponentClassification.RankTwoSporadicHeConj2

public section

namespace Certificates

open CertificateChecks

open CFSG.KC.HeConj

open CFSG.ComponentClassification.RankTwoSporadic CFSG.Sporadic.HeldB in
theorem certificate15005 : 
    YCensus (heP.subgroupOf heAutGroup) (· ≤ heP.subgroupOf heAutGroup) ∧
      YCensus17U (heP.subgroupOf heAutGroup) (fun _ => False) :=
  by
    obtain ⟨d, U, w, kS, BP, NS, CH, NR, NL, NT, BT, NQ, BQ, PS, PSI, LR, Ts, LT, PT, QT, hU, hT,
      hlen, h⟩ := KernelCensus.HeCj.he_conj
    exact ⟨he_yCensusII_of_heConjOK hU hT hlen h, he_yCensus17U_of_heConjOK hU hT hlen h⟩

end Certificates
