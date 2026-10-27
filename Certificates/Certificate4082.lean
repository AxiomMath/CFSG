
module

public import Certificates.Certificate4082Base
import all Certificates.Certificate4082Base

public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.A312ListA7LatticeInputs
import Certificates.Kernel.LocalQT.Lat.C4082
import CFSG.Certificates.Kernel.LocalQTA7RhoSound

public section

namespace Certificates

open CFSG.KD.LQT.C4082 CFSG.KC.LQT.L CFSG.QuasithinUnique.Vol2Native.A312L.Seven in
open CFSG CFSG.QuasithinUnique CFSG.QuasithinUnique.Vol2Native CFSG.QuasithinUnique.Vol2Native.A312L CFSG.QuasithinUnique.Vol2Native.A312L.Seven in
open Matrix Equiv in
theorem certificate4082 : (∀ g : SpecialLinearGroup (Fin 3) (ZMod 2),
          (CFSG.QuasithinUnique.Vol2Native.A312L.Seven.elts (latGens.getD 8 [])).contains (rhoRaw vec8 g) = true)
    ∧ (∀ g : SpecialLinearGroup (Fin 3) (ZMod 2),
          (CFSG.QuasithinUnique.Vol2Native.A312L.Seven.elts (latGens.getD 9 [])).contains (rhoRaw vec9 g) = true) :=
  ⟨rho7_sound C CFSG.KD.LQT.C4082.inj (latGens.getD 8 []) vec8 certificate4082_v8 r8,
    rho7_sound C CFSG.KD.LQT.C4082.inj (latGens.getD 9 []) vec9 certificate4082_v9 r9⟩

end Certificates
