module

public import CFSG.HardMathSupport.Dickson.Sec6.Gen3D4Aux.EGroup
import Certificates.Kernel.CertF8.Glue17200

public section

namespace Certificates

open CFSG.HardMathSupport.Dickson.Sec6.Gen3D4 in
theorem certificate17200 : ∀ {X : Type} [Group X] [Finite X] (R : Realization X),
    (∀ c < 4, CFSG.Open.IsElemAbelian 3 (R.Eg c) ∧ Nat.card (R.Eg c) = 27) ∧
      ∃ P : Subgroup X, Nat.card P = 3 ^ 5 ∧ ∀ B : Subgroup X, B ≤ P →
        CFSG.Open.IsElemAbelian 3 B → ∃ c < 4, ∃ g : X, B.map (MulAut.conj g).toMonoidHom ≤ R.Eg c :=
  fun R => Kernel.CertF8.C17200.facts17200 R

end Certificates
