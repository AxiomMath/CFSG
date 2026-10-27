module

public import Certificates.Data.Asch54SporFi22Pair
import Certificates.Kernel.Asch54.Fi22Glue

public section

namespace Certificates

open CertificateChecks

open CFSG.Monster.B.Fischer CFSG.Sporadic.FischerOddCore CFSG.LocalAnalysis.WeakClosure81.Asch54Fi22 in
theorem certificate75338 : A0 ≤ fi22P ∧ Nat.card A0 = 17694720 ∧ fi22OuterT ≤ A0 ∧ fi22OuterT ≤ fi22H 1 ∧
    mP * mP = 1 ∧ fi22U * mP ∈ fi22P ∧ (∀ x ∈ fi22OuterT, mP * x * mP⁻¹ ∈ fi22OuterT) ∧
    (∀ x ∈ A0, mP * x * mP⁻¹ ∈ A0) ∧ (∀ x ∈ fi22H 1, mP * x * mP⁻¹ ∈ fi22H 1) := KernelSpor.A54F22G.facts75338

end Certificates
