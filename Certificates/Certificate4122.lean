module

public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.A312ListA7LatticeInputs
import Certificates.Kernel.LocalQT.Small.Perm7

public section

namespace Certificates

open CFSG.KC.LQT.S CFSG.KD.LQT.Perm7 in
open CFSG CFSG.QuasithinUnique in
open CFSG.QuasithinUnique.Vol2Native.A312L.Seven in
theorem certificate4122 : (∀ σ : P7, (∀ g ∈ dGens, σ * g = g * σ) → σ ^ 2 = 1) := s4122 _ _ cd1 cd2 k4122

end Certificates
