module

public import CFSG.Quasithin.Background.JonesParshallG2TwoCertificate8952Inputs
public import CFSG.Quasithin.Background.JonesParshallWords

public section

open CFSG.Quasithin.JonesParshall

namespace CertificateChecks.Batch8952

open CFSG.Quasithin.JonesParshall

private theorem cmat_g2a_0 : wordEvalM mats8 [6, 1, 5, 1, 6, 5] = matA2 := by
  decide +kernel

private theorem cmat_g2b_0 : wordEvalM mats8 [7, 5, 3, 7, 3, 5] = matB2 := by
  decide +kernel

private theorem gens8_inv_0 : ∀ i : Fin 8, mats8 i * mats8 i = 1 := by
  decide +kernel

private theorem conj_g2a_0 : mats8 0 * matA2 * mats8 0 =
    wordEvalM ![matA2, matB2] [1, 0, 0, 1, 1, 0, 1, 0, 1, 1, 0, 0, 1, 0, 1, 0] := by
  decide +kernel

private theorem conj_g2b_0 : mats8 0 * matB2 * mats8 0 = matB2 := by
  decide +kernel

private theorem gens8_eq_0 :
    ∀ i : Fin 8, mats8 i = wordEvalM ![matX2, matA2, matB2] (wordsG i) := by
  decide +kernel

end CertificateChecks.Batch8952

namespace Certificates

open CertificateChecks

open CFSG.Quasithin.JonesParshall in
theorem certificate8952 : wordEvalM mats8 [6, 1, 5, 1, 6, 5] = matA2 ∧ wordEvalM mats8 [7, 5, 3, 7, 3, 5] = matB2 ∧
    (∀ i : Fin 8, mats8 i * mats8 i = 1) ∧
    mats8 0 * matA2 * mats8 0 =
      wordEvalM ![matA2, matB2] [1, 0, 0, 1, 1, 0, 1, 0, 1, 1, 0, 0, 1, 0, 1, 0] ∧
    mats8 0 * matB2 * mats8 0 = matB2 ∧
    ∀ i : Fin 8, mats8 i = wordEvalM ![matX2, matA2, matB2] (wordsG i) := by
  exact ⟨CertificateChecks.Batch8952.cmat_g2a_0, CertificateChecks.Batch8952.cmat_g2b_0, CertificateChecks.Batch8952.gens8_inv_0,
    CertificateChecks.Batch8952.conj_g2a_0, CertificateChecks.Batch8952.conj_g2b_0, CertificateChecks.Batch8952.gens8_eq_0⟩

end Certificates
