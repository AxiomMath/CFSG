module

public import Certificates.Kernel.CoverU43.TabsA
public import Certificates.Data.ThirteenListThreeCoverInputs
public import CFSG.Certificates.Kernel.Misc.Coset.PG

public section

namespace CertificateChecks.KernelCoverU43

open CFSG.Certificates CFSG.CosetTable CFSG.KC.MiscCoset CFSG.OddTranspositions.PartFour.CoverCard

theorem relsH_eq : coverWords.map encW = CFSG.KBRoute.F704101H.rels := by
  decide +kernel

theorem wordsH_eq : (subsetOf 6 [0, 1, 2, 3, 4]).map (fun x => [(x.val, true)]) =
    CFSG.KBRoute.F704101H.T1.words := by
  decide +kernel

theorem relsT_eq : (restrictWords (subsetOf 6 [0, 1, 2, 3, 4]) coverWords).map encW =
    CFSG.KBRoute.F704101T.rels := by
  decide +kernel

theorem wordsT_eq : CFSG.KBRoute.F704101T.T1.words = [] := by
  decide +kernel

theorem factH : KB.TableFact 6 (coverWords.map encW)
    ((subsetOf 6 [0, 1, 2, 3, 4]).map fun x => [(x.val, true)]) 27216 := by
  have h := CFSG.KBFact.F704101H
  rw [← relsH_eq, ← wordsH_eq] at h
  exact h

theorem factT : KB.TableFact 5
    ((restrictWords (subsetOf 6 [0, 1, 2, 3, 4]) coverWords).map encW) [] 720 := by
  have h := CFSG.KBFact.F704101T
  rw [← relsT_eq, wordsT_eq] at h
  exact h

end CertificateChecks.KernelCoverU43
