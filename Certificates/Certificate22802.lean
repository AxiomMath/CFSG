module

public import CFSG.LocalAnalysis.ComponentClassification.HSFLitAutL34CertInputs
public import Certificates.Certificate2022Base

public section

open CFSG.ComponentClassification.HSFLit.AutL34

namespace CertificateChecks.Batch22802

open CFSG.ComponentClassification.HSFLit.AutL34

private theorem baseOK_0 : baseOK t0L = true := by decide +kernel

private theorem centerOK_1 : centerOK t0L (blk 0 (trL t0L)) = true := by decide +kernel

private theorem centerOK_2 : centerOK t0L (blk 1 (trL t0L)) = true := by decide +kernel

private theorem centerOK_3 : centerOK t0L (blk 2 (trL t0L)) = true := by decide +kernel

private theorem centerOK_4 : centerOK t0L (blk 3 (trL t0L)) = true := by decide +kernel

private theorem commOK_5 : commOK t0L = true := by decide +kernel

private theorem rankOK_6 : rankOK t0L (trL t0L) = true := by decide +kernel

private theorem quatOK_7 : quatOK t0L (blk 0 (trL t0L)) = true := by decide +kernel

private theorem quatOK_8 : quatOK t0L (blk 1 (trL t0L)) = true := by decide +kernel

private theorem quatOK_9 : quatOK t0L (blk 2 (trL t0L)) = true := by decide +kernel

private theorem quatOK_10 : quatOK t0L (blk 3 (trL t0L)) = true := by decide +kernel

private theorem unitOK_11 : unitOK (trL t0L) = true := by decide +kernel

end CertificateChecks.Batch22802

namespace Certificates

open CertificateChecks

open CFSG.ComponentClassification.HSFLit.AutL34 in
theorem certificate22802 : baseOK t0L = true ∧ centerOK t0L (blk 0 (trL t0L)) = true ∧
    centerOK t0L (blk 1 (trL t0L)) = true ∧ centerOK t0L (blk 2 (trL t0L)) = true ∧
    centerOK t0L (blk 3 (trL t0L)) = true ∧ commOK t0L = true ∧ rankOK t0L (trL t0L) = true ∧
    quatOK t0L (blk 0 (trL t0L)) = true ∧ quatOK t0L (blk 1 (trL t0L)) = true ∧
    quatOK t0L (blk 2 (trL t0L)) = true ∧ quatOK t0L (blk 3 (trL t0L)) = true ∧
    unitOK (trL t0L) = true := by
  exact ⟨CertificateChecks.Batch22802.baseOK_0, CertificateChecks.Batch22802.centerOK_1, CertificateChecks.Batch22802.centerOK_2,
    CertificateChecks.Batch22802.centerOK_3, CertificateChecks.Batch22802.centerOK_4, CertificateChecks.Batch22802.commOK_5, CertificateChecks.Batch22802.rankOK_6,
    CertificateChecks.Batch22802.quatOK_7, CertificateChecks.Batch22802.quatOK_8, CertificateChecks.Batch22802.quatOK_9, CertificateChecks.Batch22802.quatOK_10,
    CertificateChecks.Batch22802.unitOK_11⟩

end Certificates
