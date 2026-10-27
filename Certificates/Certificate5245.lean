module

public import CFSG.Blueprint.NativeSporadic
import Certificates.Kernel.Ivk8Norm.Final

public section

namespace Certificates

theorem certificate5245 : ∀ P W : Subgroup (Equiv.Perm (Fin 22)), P ≤ CFSG.Blueprint.NativeSporadic.M22 →
    W ≤ CFSG.Blueprint.NativeSporadic.M22 → Nat.card P = 2 ^ 7 → IsPGroup 3 W →
    P ≤ Subgroup.normalizer (W : Set (Equiv.Perm (Fin 22))) → W = ⊥ := CFSG.KS.Ivk8Norm.Final.m22_noThree

end Certificates
