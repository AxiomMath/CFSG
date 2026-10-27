module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.L246B42RuData
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.L246B42RuCheckInputs
import Certificates.Kernel.LocalQT.Tc.C4036
import CFSG.Certificates.Kernel.LocalQTTcKSound

public section

namespace Certificates

open CertificateChecks

open CertificateChecks.KD.LQT.C4036 in
open CFSG CFSG.QuasithinUnique CFSG.QuasithinUnique.Bridge CFSG.QuasithinUnique.Bridge.RuExcl in
open CFSG.QuasithinUnique.Setup.X1 CFSG.Sporadic.RuSchreier CFSG.Monster.B.Co2 in
open CFSG.Monster.B.Co2.Native in
theorem certificate4036 : (threeConjCheck 4060 [ruA0P, ruA1P] ruA0P ruAWords ruAProg [ruA0A, ruA1A] = true)
    ∧ (threeConjCheck 4060 [ruA0P, ruA1P] ruZtP ruZWords ruZProg [ruA0A, ruA1A] = true) := by
  rw [gens_eq, a0p_eq, zt_eq, targ_eq]
  exact ⟨CFSG.KC.LQT.TCK.tcK_sound hA, CFSG.KC.LQT.TCK.tcK_sound hZ⟩

end Certificates
