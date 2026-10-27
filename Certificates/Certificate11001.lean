module

public import CFSG.LocalAnalysis.ComponentClassification.M12CoverModelsGroupsInputs

public section

open CFSG CFSG.ComponentClassification CFSG.ComponentClassification.M12Cover CFSG.ComponentClassification.M12Cover.InternalSylow CFSG.ComponentClassification.CentralCover

namespace CertificateChecks.Batch11001

open CFSG CFSG.ComponentClassification CFSG.ComponentClassification.M12Cover CFSG.ComponentClassification.M12Cover.InternalSylow CFSG.ComponentClassification.CentralCover

private theorem centerCheck_R_0 : centerCheckN 128 starN = true := by
  decide +kernel

private theorem rootCounts_R_check_1 : ((List.range 128).countP fun x => starN x x == 27) = 0 ∧
    ((List.range 128).countP fun x => starN (starN x x) (starN x x) == 27) = 0 ∧
    ((List.range 128).countP fun x => starN x x == 64) = 24 ∧
    ((List.range 128).countP fun x => starN (starN x x) (starN x x) == 64) = 0 ∧
    ((List.range 128).countP fun x => starN x x == 91) = 24 ∧
    ((List.range 128).countP fun x => starN (starN x x) (starN x x) == 91) = 32 ∧
    starN 27 27 = 0 ∧ starN 64 64 = 0 ∧ starN 91 91 = 0 ∧
    (List.range 128).countP isCentralLabel = 4 := by
  decide +kernel

private theorem centerCheck_T_2 : ∀ ε : ZMod 2, centerCheckN 256 (tmulN ε.val) = true := by
  intro ε
  fin_cases ε <;>
    decide +kernel

private theorem rootCounts_T0_check_3 : ((List.range 256).countP fun x => tmulN 0 x x == 27) = 0 ∧
    ((List.range 256).countP fun x => tmulN 0 (tmulN 0 x x) (tmulN 0 x x) == 27) = 0 ∧
    ((List.range 256).countP fun x => tmulN 0 x x == 64) = 24 ∧
    ((List.range 256).countP fun x => tmulN 0 (tmulN 0 x x) (tmulN 0 x x) == 64) = 32 ∧
    ((List.range 256).countP fun x => tmulN 0 x x == 91) = 40 ∧
    ((List.range 256).countP fun x => tmulN 0 (tmulN 0 x x) (tmulN 0 x x) == 91) = 32 := by
  decide +kernel

private theorem rootCounts_T1_check_4 : ((List.range 256).countP fun x => tmulN 1 x x == 27) = 16 ∧
    ((List.range 256).countP fun x => tmulN 1 (tmulN 1 x x) (tmulN 1 x x) == 27) = 0 ∧
    ((List.range 256).countP fun x => tmulN 1 x x == 64) = 40 ∧
    ((List.range 256).countP fun x => tmulN 1 (tmulN 1 x x) (tmulN 1 x x) == 64) = 32 ∧
    ((List.range 256).countP fun x => tmulN 1 x x == 91) = 24 ∧
    ((List.range 256).countP fun x => tmulN 1 (tmulN 1 x x) (tmulN 1 x x) == 91) = 32 := by
  decide +kernel

private theorem squares_T_check_5 : ∀ ε : ZMod 2, tmulN ε.val 27 27 = 0 ∧ tmulN ε.val 64 64 = 0 ∧ tmulN ε.val 91 91 = 0 ∧ (List.range 256).countP isCentralLabel = 4 := by
  intro ε
  fin_cases ε <;>
    decide +kernel

end CertificateChecks.Batch11001

namespace Certificates

open CertificateChecks

open CFSG CFSG.ComponentClassification CFSG.ComponentClassification.M12Cover CFSG.ComponentClassification.M12Cover.InternalSylow CFSG.ComponentClassification.CentralCover in
theorem certificate11001 : (
centerCheckN 128 starN = true
)
    ∧ (
((List.range 128).countP fun x => starN x x == 27) = 0 ∧
    ((List.range 128).countP fun x => starN (starN x x) (starN x x) == 27) = 0 ∧
    ((List.range 128).countP fun x => starN x x == 64) = 24 ∧
    ((List.range 128).countP fun x => starN (starN x x) (starN x x) == 64) = 0 ∧
    ((List.range 128).countP fun x => starN x x == 91) = 24 ∧
    ((List.range 128).countP fun x => starN (starN x x) (starN x x) == 91) = 32 ∧
    starN 27 27 = 0 ∧ starN 64 64 = 0 ∧ starN 91 91 = 0 ∧
    (List.range 128).countP isCentralLabel = 4
)
    ∧ (
∀ ε : ZMod 2, centerCheckN 256 (tmulN ε.val) = true
)
    ∧ (
((List.range 256).countP fun x => tmulN 0 x x == 27) = 0 ∧
    ((List.range 256).countP fun x => tmulN 0 (tmulN 0 x x) (tmulN 0 x x) == 27) = 0 ∧
    ((List.range 256).countP fun x => tmulN 0 x x == 64) = 24 ∧
    ((List.range 256).countP fun x => tmulN 0 (tmulN 0 x x) (tmulN 0 x x) == 64) = 32 ∧
    ((List.range 256).countP fun x => tmulN 0 x x == 91) = 40 ∧
    ((List.range 256).countP fun x => tmulN 0 (tmulN 0 x x) (tmulN 0 x x) == 91) = 32
)
    ∧ (
((List.range 256).countP fun x => tmulN 1 x x == 27) = 16 ∧
    ((List.range 256).countP fun x => tmulN 1 (tmulN 1 x x) (tmulN 1 x x) == 27) = 0 ∧
    ((List.range 256).countP fun x => tmulN 1 x x == 64) = 40 ∧
    ((List.range 256).countP fun x => tmulN 1 (tmulN 1 x x) (tmulN 1 x x) == 64) = 32 ∧
    ((List.range 256).countP fun x => tmulN 1 x x == 91) = 24 ∧
    ((List.range 256).countP fun x => tmulN 1 (tmulN 1 x x) (tmulN 1 x x) == 91) = 32
)
    ∧ (
∀ ε : ZMod 2, tmulN ε.val 27 27 = 0 ∧ tmulN ε.val 64 64 = 0 ∧ tmulN ε.val 91 91 = 0 ∧ (List.range 256).countP isCentralLabel = 4
) := by
  exact ⟨CertificateChecks.Batch11001.centerCheck_R_0, CertificateChecks.Batch11001.rootCounts_R_check_1, CertificateChecks.Batch11001.centerCheck_T_2, CertificateChecks.Batch11001.rootCounts_T0_check_3, CertificateChecks.Batch11001.rootCounts_T1_check_4, CertificateChecks.Batch11001.squares_T_check_5⟩

end Certificates
