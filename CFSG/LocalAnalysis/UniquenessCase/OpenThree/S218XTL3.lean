module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.DataThree
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.R76Sig
public import CFSG.LocalAnalysis.UniquenessCase.UC6R
import CFSG.LocalAnalysis.UniquenessCase.UC22S218XE3L3
import CFSG.LocalAnalysis.UniquenessCase.UC6S846h
public import CFSG.LocalAnalysis.UniquenessCase.UC22S21a

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

open CFSG.Open
open CFSG.LocalAnalysis.RankThreeUC (Setup Standing AGL81TheoremC)

variable {G : Type} [Group G] [Finite G]

theorem s21_8XTL3_dataOfSetup (hS : Standing G) (_hUC : CFSG.Open.rankThreeUC G)
    (_hC : AGL81TheoremC G) (S : Setup G) (_hMS : S.InMSigma)
    (h211 : S21_1 (PartTwo.Three.dataOfSetup hS S) (fun _ _ => True))
    (h614 : UC6.R6_14 (PartTwo.Three.dataOfSetup hS S))
    (h76 : F07.R76Sig (PartTwo.Three.dataOfSetup hS S))
    (hH : H1930 (PartTwo.Three.dataOfSetup hS S))
    (c : Ctx21 (PartTwo.Three.dataOfSetup hS S) (fun _ _ => True)) {L : Subgroup G}
    (hL : L ∈ calC (PartTwo.Three.dataOfSetup hS S).M) {n : ℕ} (hX : IsL3 (BarInf L) n)
    (hn : ¬ IsPowTwo n) : False :=
  uc22s218x_false_L3 (PartTwo.Three.dataOfSetup hS S) _ (UC6S846.sigmaStd_dataOfSetup hS S) h614
    h211 (fun p hp hsp => h76 p hp ((PartTwo.Three.dataOfSetup hS S).sig_prime p hp).2 hsp) hH c hL
    hX hn

end CFSG.LocalAnalysis.UniquenessCase.UC22
