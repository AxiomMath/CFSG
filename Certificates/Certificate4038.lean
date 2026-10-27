module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.X1TightFinInputs
import Certificates.Kernel.LocalQT.Small.C4038

public section

namespace Certificates

open CFSG CFSG.QuasithinUnique CFSG.QuasithinUnique.Setup CFSG.QuasithinUnique.Setup.X1 CFSG.QuasithinUnique.Setup.X1.Tight in
theorem certificate4038 : (∀ x ∈ [0, 1, 30, 31], ∀ y < 32, good x y = false)
    ∧ (∀ w < 32,
          (∀ k < 5, app5 (dwC w) (app5 (dwC w) (app5 (dwC w) (app5 (dwC w) (2 ^ k)))) = 2 ^ k) →
            ∃ x < 32, cycOK x = true ∧ app5 (dwC w) x = x) :=
  ⟨CFSG.KC.LQT.T.s4038a (by decide) le_rfl CFSG.KD.LQT.C4038.ka,
    CFSG.KC.LQT.T.s4038b le_rfl CFSG.KD.LQT.C4038.kb⟩

end Certificates
