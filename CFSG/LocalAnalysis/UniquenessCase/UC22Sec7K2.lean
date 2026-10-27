module

public import CFSG.LocalAnalysis.UniquenessCase.UCFront07Use
public import CFSG.LocalAnalysis.UniquenessCase.UC6S846e
import CFSG.LocalAnalysis.UniquenessCase.UC22SigmaThree

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

open CFSG.Open
open CFSG.Yardstones.Mf4cdcdf2e013 (Standing4 Setup4)
open CFSG.RankThree.PartOne (IsStronglyPEmbedded)
open CFSG.LocalAnalysis.UniquenessCase.PartOne.Section7 (Conclusion76 StronglyEmbeddedFive)

variable {G : Type} [Group G] [Finite G]

theorem conclusion76_setup4_k_eq_two (hSE : StronglyEmbeddedFive) (hS : Standing4 G)
    (hU : uniqueFourUnique G) (S : Setup4 G) (hσ : S.InMSigma)
    (hk : (UC6.dataOfSetup4 hS hU S).k = 2) {p : ℕ} (hp : p ∈ (UC6.dataOfSetup4 hS hU S).sig)
    (hsp : IsStronglyPEmbedded p (UC6.dataOfSetup4 hS hU S).M) :
    Conclusion76 (UC6.dataOfSetup4 hS hU S).M p :=
  UC6.conclusion76_dataOfSetup4_of_k_eq_two hSE hS hU S hσ (three_not_mem_uniqueFourBeta hS hU S)
    hk hp hsp

theorem conclusion76_setup4_k_eq_two_of_calC (hSE : StronglyEmbeddedFive) (hS : Standing4 G)
    (hU : uniqueFourUnique G) (S : Setup4 G) (hσ : S.InMSigma)
    (hSg : UC6S846.SigmaStd (UC6.dataOfSetup4 hS hU S)) {L : Subgroup G}
    (hL : L ∈ calC (UC6.dataOfSetup4 hS hU S).M) (hk : (UC6.dataOfSetup4 hS hU S).k = 2)
    {p : ℕ} (hp : p ∈ (UC6.dataOfSetup4 hS hU S).sig) :
    Conclusion76 (UC6.dataOfSetup4 hS hU S).M p :=
  conclusion76_setup4_k_eq_two hSE hS hU S hσ hk hp
    (hSg.sig1_sp p (UC6S846.sig_subset_sig1 hSg (UC6S846.not_solvable_of_mem_calC hL) hp))

end CFSG.LocalAnalysis.UniquenessCase.UC22
