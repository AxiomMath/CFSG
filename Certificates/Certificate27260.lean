module

public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Balance.Cocode24Check
import CFSG.Certificates.Kernel.EvenSporCocode.Sound
import Certificates.Kernel.EvenSporCocode.Span
import Certificates.Kernel.EvenSporCocode.RowsA
import Certificates.Kernel.EvenSporCocode.RowsB
import Certificates.Kernel.EvenSporCocode.DfsA
import Certificates.Kernel.EvenSporCocode.DfsB

public section

open CFSG.EvenSporadicStandard.Induction.Balance.Cocode24 CFSG.KC.EvenSporCocode

namespace CertificateChecks.Batch27260

open CFSG.EvenSporadicStandard.Induction.Balance.Cocode24 CFSG.KC.EvenSporCocode

open CertificateChecks.KernelCocode

private theorem rowCR_all (i : ℕ) (hi : i < 1024) : rowCR i = true := by
  by_cases h : i < 512
  · exact rowsA_all i h
  · obtain ⟨k, rfl⟩ : ∃ k, i = 512 + k := ⟨i - 512, by omega⟩
    have hk : k < 512 := by omega
    exact rowsB_all k hk

private theorem dfs_all : ∀ k < 12, dfsF k = true
  | 0, _ => dfsF0 | 1, _ => dfsF1 | 2, _ => dfsF2 | 3, _ => dfsF3 | 4, _ => dfsF4
  | 5, _ => dfsF5 | 6, _ => dfsF6 | 7, _ => dfsF7 | 8, _ => dfsF8 | 9, _ => dfsF9
  | 10, _ => dfsF10 | 11, _ => dfsF11
  | _ + 12, h => absurd h (by omega)

theorem checks : spanOK 1024 sylowTabs = true ∧ sylowTabs.all autOK = true ∧
    rowsOKWith (tabsArr sylowTabs) (rowsOf (tabsArr sylowTabs)) = true ∧
    dfsOKWith (tabsArr sylowTabs) (rowsOf (tabsArr sylowTabs)) = true := by
  have hdfs : dfsSub D.RB D.LT (invsK D.LT) (invsK D.LT) = true := by
    rw [iv_eq]
    exact dfsSub_of_blocks iv_len fun k hk =>
      (dfsSubK_eq planes_ok _ _ _ _).symm.trans (dfs_all k hk)
  obtain ⟨h1, h3, h4⟩ := checks_of lt_eq lt_len kt_nodup lt_valid gens_valid kt_eq ep_eq rb_len
    (rows_of_rowCR iv_eq (by rw [← kt_eq, List.length_map, lt_len]) rowCR_all) close_ok hdfs
  exact ⟨h1, gens_aut, h3, h4⟩

end CertificateChecks.Batch27260

namespace Certificates

open CertificateChecks

open CFSG.EvenSporadicStandard.Induction.Balance.Cocode24 in
theorem certificate27260 : (spanOK 1024 sylowTabs = true) ∧ (sylowTabs.all autOK = true) ∧
    (rowsOKWith (tabsArr sylowTabs) (rowsOf (tabsArr sylowTabs)) = true) ∧
    (dfsOKWith (tabsArr sylowTabs) (rowsOf (tabsArr sylowTabs)) = true) := CertificateChecks.Batch27260.checks

end Certificates
