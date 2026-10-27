module

public import CFSG.Monster.B.Pinned.Primes.ThreeRelationsInputs
public import Certificates.Certificate3027
public import Certificates.Certificate3106

public section

open CFSG CFSG.Monster CFSG.Monster.B CFSG.Monster.B.Pinned CFSG.Monster.B.Bin
  CFSG.Monster.B.Primes.Native CFSG.Blueprint

namespace CertificateChecks.Batch16008

open CFSG CFSG.Monster CFSG.Monster.B CFSG.Monster.B.Pinned CFSG.Monster.B.Bin
  CFSG.Monster.B.Primes.Native CFSG.Blueprint

private theorem three_spec_0 : ∀ i j : Fin 8, (threeCommRows.getD i []).getD j 0 < 3 := by
  decide +kernel

private theorem three_spec_1 : ∀ i : Fin 8, (threeXRows.getD i []).length = 8 := by
  decide +kernel

private theorem three_spec_2 : ∀ i j : Fin 8, (threeXRows.getD i []).getD j 0 < 3 := by
  decide +kernel

private theorem three_spec_3 : ∀ i : Fin 8, threeCVec.getD i 0 < 3 := by
  decide +kernel

private theorem three_spec_4 : ∀ i : Fin 8, (threeYRows.getD i []).length = 8 := by
  decide +kernel

private theorem three_spec_5 : ∀ i j : Fin 8, (threeYRows.getD i []).getD j 0 < 3 := by
  decide +kernel

private theorem three_spec_6 : ∀ i : Fin 8, threeDVec.getD i 0 < 3 := by
  decide +kernel

private theorem bcomm_qThree_7 : ∀ i j : Fin 8, (threeCommRows.getD i []).getD j 0 < 3 := by
  decide +kernel

private theorem bcomm_qThree_8 : ∀ i : Fin 8, (threeCommRows.getD i []).getD i 0 = 0 := by
  decide +kernel

private theorem bcomm_qThree_9 :
    ∀ i j : Fin 8,
      ((threeCommRows.getD i []).getD j 0 + (threeCommRows.getD j []).getD i 0) % 3 = 0 := by
  decide +kernel

private theorem XThree_val_10 : ∀ i j : Fin 8, (threeXRows.getD i []).getD j 0 < 3 := by
  decide +kernel

private theorem YThree_val_11 : ∀ i j : Fin 8, (threeYRows.getD i []).getD j 0 < 3 := by
  decide +kernel

private theorem cThree_val_12 : ∀ i : Fin 8, threeCVec.getD i 0 < 3 := by
  decide +kernel

private theorem dThree_val_13 : ∀ i : Fin 8, threeDVec.getD i 0 < 3 := by
  decide +kernel

private theorem MThree_mul_inv_14 : MThree * rowsMat 3 8 threeCommInvRows = 1 := by
  decide +kernel

end CertificateChecks.Batch16008

namespace Certificates

open CertificateChecks

open CFSG CFSG.Monster CFSG.Monster.B CFSG.Monster.B.Pinned CFSG.Monster.B.Bin
  CFSG.Monster.B.Primes.Native CFSG.Blueprint in
theorem certificate16008 : (
    ∀ i j : Fin 8, (threeCommRows.getD i []).getD j 0 < 3
  ) ∧ (
    ∀ i : Fin 8, (threeXRows.getD i []).length = 8
  ) ∧ (
    ∀ i j : Fin 8, (threeXRows.getD i []).getD j 0 < 3
  ) ∧ (
    ∀ i : Fin 8, threeCVec.getD i 0 < 3
  ) ∧ (
    ∀ i : Fin 8, (threeYRows.getD i []).length = 8
  ) ∧ (
    ∀ i j : Fin 8, (threeYRows.getD i []).getD j 0 < 3
  ) ∧ (
    ∀ i : Fin 8, threeDVec.getD i 0 < 3
  ) ∧ (
    ∀ i j : Fin 8, (threeCommRows.getD i []).getD j 0 < 3
  ) ∧ (
    ∀ i : Fin 8, (threeCommRows.getD i []).getD i 0 = 0
  ) ∧ (
    ∀ i j : Fin 8,
      ((threeCommRows.getD i []).getD j 0 + (threeCommRows.getD j []).getD i 0) % 3 = 0
  ) ∧ (
    ∀ i j : Fin 8, (threeXRows.getD i []).getD j 0 < 3
  ) ∧ (
    ∀ i j : Fin 8, (threeYRows.getD i []).getD j 0 < 3
  ) ∧ (
    ∀ i : Fin 8, threeCVec.getD i 0 < 3
  ) ∧ (
    ∀ i : Fin 8, threeDVec.getD i 0 < 3
  ) ∧ (
    MThree * rowsMat 3 8 threeCommInvRows = 1
  ) := by
  exact ⟨CertificateChecks.Batch16008.three_spec_0, CertificateChecks.Batch16008.three_spec_1, CertificateChecks.Batch16008.three_spec_2,
    CertificateChecks.Batch16008.three_spec_3, CertificateChecks.Batch16008.three_spec_4, CertificateChecks.Batch16008.three_spec_5,
    CertificateChecks.Batch16008.three_spec_6, CertificateChecks.Batch16008.bcomm_qThree_7, CertificateChecks.Batch16008.bcomm_qThree_8,
    CertificateChecks.Batch16008.bcomm_qThree_9, CertificateChecks.Batch16008.XThree_val_10, CertificateChecks.Batch16008.YThree_val_11,
    CertificateChecks.Batch16008.cThree_val_12, CertificateChecks.Batch16008.dThree_val_13, CertificateChecks.Batch16008.MThree_mul_inv_14⟩

end Certificates
