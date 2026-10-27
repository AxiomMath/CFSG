module

public import CFSG.LocalAnalysis.RankThreeTheoremC.ONPair.SL3PresData
public import CFSG.Certificates.CosetTablePresented
import Certificates.Kernel.PresLetters.F753504
import CFSG.Certificates.Kernel.Misc.Coset.TableFact

open CFSG CFSG.CosetTable CFSG.KC.MiscCoset CFSG.Certificates
open CFSG.LocalAnalysis.RankThreeTheoremC.ONPair

namespace CertificateChecks.PresLetters753504

abbrev R3 : List (List (Fin (subsetOf 4 [0, 1, 2]).length × Bool)) :=
  restrictWords (subsetOf 4 [0, 1, 2]) sl3Rels7

theorem relsA : sl3Rels7.map encW = CFSG.KBRoute.F753504a.rels := by
  decide +kernel

theorem relsB : R3.map encW = CFSG.KBRoute.F753504b.rels := by
  decide +kernel

theorem relsC : (restrictWords (subsetOf (subsetOf 4 [0, 1, 2]).length [0, 1]) R3).map encW =
    CFSG.KBRoute.F753504c.rels := by
  decide +kernel

theorem card3 : Finite (PG (subsetOf 4 [0, 1, 2]).length R3) ∧
    Nat.card (PG (subsetOf 4 [0, 1, 2]).length R3) ≤ 49 * 336 := by
  have hb : KB.TableFact (subsetOf 4 [0, 1, 2]).length (R3.map encW)
      ((subsetOf (subsetOf 4 [0, 1, 2]).length [0, 1]).map fun x => [(x.val, true)]) 49 := by
    rw [relsB]
    exact CFSG.KBFact.F753504b
  have hc : KB.TableFact (subsetOf (subsetOf 4 [0, 1, 2]).length [0, 1]).length
      ((restrictWords (subsetOf (subsetOf 4 [0, 1, 2]).length [0, 1]) R3).map encW) [] 336 := by
    rw [relsC]
    exact CFSG.KBFact.F753504c
  exact TableFact.card_restrict _ (by decide) _ (by decide) hb hc

end CertificateChecks.PresLetters753504

public section

namespace Certificates

open CertificateChecks.PresLetters753504 in
theorem certificate753504 : Finite (CFSG.CosetTable.PG 4 CFSG.LocalAnalysis.RankThreeTheoremC.ONPair.sl3Rels7) ∧
    Nat.card (CFSG.CosetTable.PG 4 CFSG.LocalAnalysis.RankThreeTheoremC.ONPair.sl3Rels7) ≤ 5630688 := by
  have ha : KB.TableFact 4 (sl3Rels7.map encW)
      ((subsetOf 4 [0, 1, 2]).map fun x => [(x.val, true)]) 342 := by
    rw [relsA]
    exact CFSG.KBFact.F753504a
  obtain ⟨f, c⟩ := card_le_of_index_restrict sl3Rels7 (subsetOf 4 [0, 1, 2])
    (TableFact.genSub_index _ (by norm_num) _ ha) card3
  exact ⟨f, c.trans (by norm_num)⟩

end Certificates
