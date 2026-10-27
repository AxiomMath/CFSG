module

public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82E3.Context
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.DataThree
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.R76Sig
import CFSG.LocalAnalysis.UniquenessCase.UC6S846h

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82E3

open CFSG.LocalAnalysis.RankThreeUC (Setup Standing)
open CFSG.Yardstones.Mf4cdcdf2e013 (TheoremCAt)

variable {G : Type} [Group G] [Finite G]

theorem std82E3_dataOfSetup (hS : Standing G) (S : Setup G) (hMS : S.InMSigma)
    (hC : TheoremCAt (PartTwo.Three.dataOfSetup hS S).M)
    (h614 : UC6.R6_14 (PartTwo.Three.dataOfSetup hS S))
    (h76 : UC22.F07.R76Sig (PartTwo.Three.dataOfSetup hS S)) :
    Std82E3 (PartTwo.Three.dataOfSetup hS S) where
  rank := hS.rank
  kProper := hS.kProper
  sig_nonempty := (UC6S846.sigmaStd_dataOfSetup hS S).nonempty
  three_le := (UC6S846.sigmaStd_dataOfSetup hS S).three_le
  sig1_sp := (UC6S846.sigmaStd_dataOfSetup hS S).sig1_sp
  solvable_of := (UC6S846.sigmaStd_dataOfSetup hS S).solvable_of
  three_mem_sig := fun h => by
    have h3 : S.p = 3 := hMS.1 h
    rw [← h3]
    exact PartTwo.Three.mem_sigmaOf S
  u2 := fun _ hp H hH h2 => hp.2.choose_spec.u2 H hH h2
  theoremC := hC
  r614 := h614
  r76 := fun p hp hsp => h76 p hp ((PartTwo.Three.dataOfSetup hS S).sig_prime p hp).2 hsp

end CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82E3
