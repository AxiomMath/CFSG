module

public import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.L2_5_2FinM23Inputs
import Certificates.Kernel.LocalQT.Tab2.C4047
import CFSG.Certificates.Kernel.LocalQTTab2KSound

public section

namespace Certificates

open CFSG.KD.LQT.C4047 in
open CFSG CFSG.QuasithinUnique CFSG.QuasithinUnique.Unc25G2 CFSG.QuasithinUnique.Unc25G2.M2x in
open CFSG.Sporadic.Mathieu CFSG.Blueprint in
theorem certificate4047 : (Check 23 d23) :=
  CFSG.KC.LQT.T2.check_soundK (by decide) _ _ _ _ h₁ h₂ h₃ hk

end Certificates
