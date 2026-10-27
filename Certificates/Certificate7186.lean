module

public import Certificates.Data.M22Asl
import Certificates.Kernel.M22Asl.Checks
import CFSG.Certificates.Kernel.M23AslSound

public section

namespace Certificates

open CFSG.KC.M23Asl CFSG.KC.LQT CFSG.KD.M22Asl

theorem certificate7186 : M22Asl.check = true := by
  have eP : CFSG.QuasithinUnique.Vol2Native.A312L.M22Lat.p5Gens.map P.code = gP := by
    decide +kernel
  have eS : M22Asl.aslGens.map P.code = gS := by decide +kernel
  exact diagExt_sound (by decide) (by decide) _ _ eP eS dg

end Certificates
