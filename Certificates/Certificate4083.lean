
module


public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.A312ListA7LatticeInputs
import Certificates.Kernel.LocalQT.Lat.C4083
import CFSG.Certificates.Kernel.LocalQTA7KSound

public section

namespace Certificates

open CFSG.KD.LQT.C4083 CFSG.KC.LQT.L CFSG.QuasithinUnique.Vol2Native.A312L.Seven in
open CFSG CFSG.QuasithinUnique CFSG.QuasithinUnique.Vol2Native CFSG.QuasithinUnique.Vol2Native.A312L CFSG.QuasithinUnique.Vol2Native.A312L.Seven in
open scoped commutatorElement in
open Equiv CFSG.QuasithinUnique.Unc25K1.Six in
theorem certificate4083 : (∀ x : P7, Perm.sign x = 1 →
          ((CFSG.QuasithinUnique.Vol2Native.A312L.Seven.elts (latGens.getD 10 [])).contains (R7.enc x) = true ↔ x 6 = 6))
    ∧ (∀ x : P7, Perm.sign x = 1 →
          ((CFSG.QuasithinUnique.Vol2Native.A312L.Seven.elts (latGens.getD 7 [])).contains (R7.enc x) = true ↔
            (x 4 = 4 ∨ x 4 = 5) ∧ (x 5 = 4 ∨ x 5 = 5)))
    ∧ (∀ g ∈ dGens, Perm.sign g = 1) :=
  ⟨fix7_sound C CFSG.KD.LQT.C4083.inj (latGens.getD 10 []) 6 f1,
    pair7_sound C CFSG.KD.LQT.C4083.inj (latGens.getD 7 []) 4 5 f2,
    CFSG.KC.LQT.LK.signs_sound (by decide) dGens f3⟩

end Certificates
