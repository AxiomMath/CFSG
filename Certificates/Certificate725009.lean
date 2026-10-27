module

public import CFSG.Sporadic.SmallOddCore.HSData
import Certificates.Kernel.W4Row.HS119Core

public section

namespace Certificates

open CFSG.Sporadic.SmallOddCore CFSG.Sporadic.Schreier in
theorem certificate725009 : ∀ {R' : Subgroup (Equiv.Perm (Fin 3850))}, hsP ≤ R' → R' ≤ hsR →
    ∀ {A C : Subgroup (Equiv.Perm (Fin 3850))}, A ≤ hsS ⊓ R' → (∀ a ∈ A, a * a = 1) →
      8 ≤ Nat.card A → hsS ⊓ R' ≤ C →
      (∀ g ∈ R', Nat.card A ≤ 4 * Nat.card ↥(A.map (MulAut.conj g).toMonoidHom ⊓ C) →
        A.map (MulAut.conj g).toMonoidHom ≤ C) → R' ≤ C :=
  CFSG.KD.HS119.hs119_core

end Certificates
