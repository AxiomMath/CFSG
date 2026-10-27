module

public import CFSG.Quasithin.Background.JonesParshallG2Two
public import CFSG.Quasithin.Background.B5FinG2U33Inputs

public section

open CFSG CFSG.Quasithin CFSG.Quasithin.JonesParshall CFSG.Quasithin.Explicit CFSG.CosetTable CFSG.Open commutatorElement

namespace CertificateChecks.Batch17951

open CFSG CFSG.Quasithin CFSG.Quasithin.JonesParshall CFSG.Quasithin.Explicit CFSG.CosetTable CFSG.Open commutatorElement

private theorem u33HomL_injective_0 : ¬(u33Mats 2 = 1) := by
  decide +kernel

private theorem u33Pres_nonabelian_1 : ¬(u33Mats 3 * u33Mats 2 = u33Mats 2 * u33Mats 3) := by
  decide +kernel

private theorem g2a_eq_word_2 : matA2 = wordEvalM u33Mats [2, 3, 4, 3, 3, 4] := by
  decide +kernel

private theorem g2b_eq_word_3 : matB2 = wordEvalM u33Mats [1, 4, 3, 2, 4, 3, 4, 3, 1, 0] := by
  decide +kernel

end CertificateChecks.Batch17951

namespace Certificates

open CertificateChecks

open CFSG CFSG.Quasithin CFSG.Quasithin.JonesParshall CFSG.Quasithin.Explicit CFSG.CosetTable CFSG.Open commutatorElement in
theorem certificate17951 : (
¬(u33Mats 2 = 1)
)
    ∧ (
¬(u33Mats 3 * u33Mats 2 = u33Mats 2 * u33Mats 3)
)
    ∧ (
matA2 = wordEvalM u33Mats [2, 3, 4, 3, 3, 4]
)
    ∧ (
matB2 = wordEvalM u33Mats [1, 4, 3, 2, 4, 3, 4, 3, 1, 0]
) := by
  exact ⟨@CertificateChecks.Batch17951.u33HomL_injective_0, @CertificateChecks.Batch17951.u33Pres_nonabelian_1,
    @CertificateChecks.Batch17951.g2a_eq_word_2, @CertificateChecks.Batch17951.g2b_eq_word_3⟩

end Certificates
