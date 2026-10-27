module

public import CFSG.Blueprint.NativeSporadic
import Certificates.Kernel.Ivk8Norm.Final

public section

namespace Certificates

theorem certificate5244 : ∀ P W : Subgroup (Equiv.Perm (Fin 12)), P ≤ CFSG.Blueprint.NativeSporadic.M12 →
    W ≤ CFSG.Blueprint.NativeSporadic.M12 → Nat.card P = 2 ^ 6 → IsPGroup 3 W →
    P ≤ Subgroup.normalizer (W : Set (Equiv.Perm (Fin 12))) → W = ⊥ := CFSG.KS.Ivk8Norm.Final.m12_noThree

end Certificates
