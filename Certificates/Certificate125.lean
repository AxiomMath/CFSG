module

public import CFSG.ClassicalInvolution.Q3.TL4VtxE4O8Defs
public import CFSG.ClassicalInvolution.Q3.TL4VtxE4Q8B
import Certificates.Kernel.OmegaEight.Quat125Cert

public section

namespace Certificates

open CertificateChecks

open CFSG.EvenSmallLie.OmegaEight CFSG.Monster.B.Co2 CFSG.ClassicalInvolution.Q3.TL4.E4O8 in
open CFSG.ClassicalInvolution.Generic CFSG.ClassicalInvolution.Q3.TL4 in
theorem certificate125 :
    (∀ a ∈ [u0A (), v0A (), threeA ()] ++ wsA (), ∃ g ∈ omegaT, Rep 360 a g) ∧
    (u0 * u0 = mainPerm 0 ∧ mainPerm 0 * mainPerm 0 = 1 ∧ mainPerm 0 ≠ 1 ∧
      ∀ x, x ∈ K0 ↔ x ∈ L0P) ∧
    (gen 8 * mainPerm 0 = mainPerm 0 * gen 8 ∧ gen 9 * mainPerm 0 = mainPerm 0 * gen 9 ∧
      (∀ k ∈ [1, 3, 4], wsP.getD k 1 * mainPerm 0 = mainPerm 0 * wsP.getD k 1) ∧
      three ^ 3 = 1 ∧ conjSub three K0 = K0 ∧ three * u0 ≠ u0 * three) ∧
    (∀ {K : Subgroup (Equiv.Perm (Fin 360))} {s : Equiv.Perm (Fin 360)},
      Vtx.AmbientQuatDatum omegaT K s → ∃ g ∈ omegaT, conjSub g K = K0) ∧
    (wsP.length = 6300 ∧ ∀ {g : Equiv.Perm (Fin 360)}, g ∈ omegaT →
      ∃ k < wsP.length, conjSub g K0 = conjSub (wsP.getD k 1) K0) ∧
    (∀ {g : Equiv.Perm (Fin 360)}, g ∈ omegaT →
      Relation.ReflTransGen (Vtx.StarRel omegaT K0) K0 (conjSub g K0)) ∧
    (∀ {g : Equiv.Perm (Fin 360)}, g ∈ omegaT → conjSub g K0 ≠ K0 →
      conjSub g K0 ≤ Subgroup.normalizer (K0 : Set (Equiv.Perm (Fin 360))) →
      ∃ k ∈ [1, 3, 4], conjSub g K0 = conjSub (wsP.getD k 1) K0) ∧
    (conjSub (wsP.getD 1 1) K0 ≠ K0 ∧
      conjSub (wsP.getD 1 1) K0 ≤ Subgroup.normalizer (K0 : Set (Equiv.Perm (Fin 360)))) := KernelO8.Q125.q125_cert

end Certificates
