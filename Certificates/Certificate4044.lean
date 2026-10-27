module

public import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.L2_5_19TabA8BasicInputs
import Certificates.Kernel.LocalQT.Small.Perm7

public section

namespace Certificates

open CFSG.KC.LQT.S CFSG.KD.LQT.Perm7 in
open CFSG CFSG.QuasithinUnique CFSG.QuasithinUnique.Id2519 CFSG.QuasithinUnique.Id2519.Tab CFSG.QuasithinUnique.Id2519.Tab.A8 in
open Equiv Equiv.Perm in
theorem certificate4044 : (∀ a b : Fin 8, a ≠ b → ∀ τ : Perm (Fin 8), τ * g5 a b = g5 a b * τ →
          τ * g3 a b = g3 a b * τ → τ = 1 ∨ τ = swap a b) := s4044 _ _ g53 k4044

end Certificates
