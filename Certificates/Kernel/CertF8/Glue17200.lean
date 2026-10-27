module

public import CFSG.Certificates.Kernel.CertF8.Sound17200
public import Certificates.Kernel.CertF8.Syl17200Data
import Certificates.Kernel.CertF8.Syl17200Rows
import Certificates.Kernel.CertF8.Syl17200Cover
import Certificates.Kernel.CertF8.GlueGen64
import CFSG.Certificates.Kernel.Common.ForallChunks

public section

namespace Certificates.Kernel.CertF8.C17200

open CFSG.KC.CertF8 CFSG.KC.CertF8.S17200 CFSG.KC.Misc.Clos CFSG.HardMathSupport.Dickson.Sec6.Gen3D4
  CFSG.Open

#kc_forall_chunks rowsC
  (fun k => CFSG.KC.Misc.Clos.allR (Nat.mul 9 k) 9
    (CFSG.KC.CertF8.S17200.rowAt CFSG.KC.CertF8.S17200.T) = true) 27
  CFSG.KC.CertF8.S17200.ch17200r.c 1

#kc_forall_chunks coverC
  (fun k => CFSG.KC.Misc.Clos.allR (Nat.mul 27 k) 27
    (CFSG.KC.CertF8.S17200.h3At CFSG.KC.CertF8.S17200.T) = true) 9
  CFSG.KC.CertF8.S17200.ch17200h.c 1

theorem rows : ∀ j < 243, rowAt T j = true :=
  forall_of_chunks 9 27 _ rowsC

theorem cover : ∀ x < 243, h3At T x = true :=
  forall_of_chunks 27 9 _ coverC

theorem hyp : Hyp T :=
  hyp_of (T := T) codePr64_symP codePr64_oneP rows ch17200m cover

theorem facts17200 {X : Type} [Group X] [Finite X] (R : Realization X) :
    (∀ c < 4, IsElemAbelian 3 (R.Eg c) ∧ Nat.card (R.Eg c) = 27) ∧
      ∃ P : Subgroup X, Nat.card P = 3 ^ 5 ∧ ∀ B : Subgroup X, B ≤ P → IsElemAbelian 3 B →
        ∃ c < 4, ∃ g : X, B.map (MulAut.conj g).toMonoidHom ≤ R.Eg c :=
  sound17200 R hyp

end Certificates.Kernel.CertF8.C17200

end
