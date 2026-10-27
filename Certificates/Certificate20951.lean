module

public import CFSG.RankThree.Native.BFiveHCheckInputs
public import CFSG.Monster.B.Pinned.Primes.Data
public import CFSG.RankThree.Native.FiveLocalBasic

public section

open CFSG.RankThree.Native CFSG.Monster.B.Pinned

namespace CertificateChecks.Batch20951

open CFSG.RankThree.Native CFSG.Monster.B.Pinned

private theorem bFiveH_spec_rows_length_0 : ∀ i : Fin 4, (bFiveHRows.getD i []).length = 4 := by
  decide +kernel

private theorem bFiveH_spec_rows_lt_1 : ∀ i j : Fin 4, (bFiveHRows.getD i []).getD j 0 < 5 := by
  decide +kernel

private theorem bFiveH_spec_central_lt_2 : ∀ i : Fin 4, bFiveHC.getD i 0 < 5 := by
  decide +kernel

private theorem MFive_eq_f5M_3 : MFive = f5M := by
  decide +kernel

private theorem fiveActRows_val_4 :
    ∀ i j : Fin 4, (fiveActRows.getD i []).getD j 0 = (f5X i j).val := by
  decide +kernel

private theorem fiveActC_val_5 : ∀ i : Fin 4, fiveActC.getD i 0 = FiveLocal.xc i := by
  decide +kernel

private theorem bFiveHRows_val_6 :
    ∀ i j : Fin 4, (bFiveHRows.getD i []).getD j 0 = (f5H i j).val := by
  decide +kernel

private theorem bFiveHC_val_7 : ∀ i : Fin 4, bFiveHC.getD i 0 = FiveLocal.hc i := by
  decide +kernel

end CertificateChecks.Batch20951

namespace Certificates

open CertificateChecks

open CFSG.RankThree.Native CFSG.Monster.B.Pinned in
theorem certificate20951 :
    (∀ i : Fin 4, (bFiveHRows.getD i []).length = 4) ∧
    (∀ i j : Fin 4, (bFiveHRows.getD i []).getD j 0 < 5) ∧
    (∀ i : Fin 4, bFiveHC.getD i 0 < 5) ∧
    MFive = f5M ∧
    (∀ i j : Fin 4, (fiveActRows.getD i []).getD j 0 = (f5X i j).val) ∧
    (∀ i : Fin 4, fiveActC.getD i 0 = FiveLocal.xc i) ∧
    (∀ i j : Fin 4, (bFiveHRows.getD i []).getD j 0 = (f5H i j).val) ∧
    (∀ i : Fin 4, bFiveHC.getD i 0 = FiveLocal.hc i) := by
  exact ⟨@CertificateChecks.Batch20951.bFiveH_spec_rows_length_0, @CertificateChecks.Batch20951.bFiveH_spec_rows_lt_1,
    @CertificateChecks.Batch20951.bFiveH_spec_central_lt_2, @CertificateChecks.Batch20951.MFive_eq_f5M_3,
    @CertificateChecks.Batch20951.fiveActRows_val_4, @CertificateChecks.Batch20951.fiveActC_val_5, @CertificateChecks.Batch20951.bFiveHRows_val_6,
    @CertificateChecks.Batch20951.bFiveHC_val_7⟩

end Certificates
