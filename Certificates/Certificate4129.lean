module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.L246C123SylowA7Inputs
import Certificates.Kernel.LocalQT.Small.Perm7

public section

namespace Certificates

open CFSG.KC.LQT.S CFSG.KD.LQT.Perm7 in
open CFSG CFSG.QuasithinUnique CFSG.QuasithinUnique.L246 CFSG.QuasithinUnique.L246.C123 in
open Equiv in
theorem certificate4129 : (Perm.sign c5 = 1)
    ∧ (Perm.sign c7 = 1)
    ∧ (c5 ^ 5 = 1)
    ∧ (c7 ^ 7 = 1)
    ∧ (c5 ≠ 1)
    ∧ (c7 ≠ 1)
    ∧ ((Finset.univ.filter fun g : Perm (Fin 7) => Perm.sign g = 1 ∧ g * c5 * g⁻¹ ∈ pset5).card =
            20)
    ∧ ((Finset.univ.filter fun g : Perm (Fin 7) => Perm.sign g = 1 ∧ g * c7 * g⁻¹ ∈ pset7).card =
            21) := (s4129 _ _ cc5 cc7 k4129)

end Certificates
