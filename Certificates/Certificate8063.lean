module

public import CFSG.Quasithin.Background.B3SpecFacts
import Certificates.Kernel.B3.Assembly

public section

namespace Certificates

open CFSG CFSG.Quasithin CFSG.Quasithin.B3 in
theorem certificate8063 : (∀ n k, SQTKn n → CaseA n k → PropB32A n k) ∧
    (∀ n k, SQTKn n → CaseB n k → ¬ (n = 8 ∧ k = Mod.ut0) → PropB32B5 n k) ∧
    PropB32B6 8 Mod.ut0 ∧ StrongTl6 Mod.u0 ∧ StrongTl6 Mod.ut0 :=
  ⟨CFSG.KD.B3MA.propB32A_all, CFSG.KD.B3MA.propB32B5_all, CFSG.KD.B3MA.propB32B6_eight,
    CFSG.KD.B3MA.strongTl6 (Or.inl rfl), CFSG.KD.B3MA.strongTl6 (Or.inr rfl)⟩

end Certificates
