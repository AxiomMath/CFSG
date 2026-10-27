module

public import CFSG.GF2Type.Widths1112.Co2FormDefs
import Certificates.Kernel.Co2W11.Glue

public section

open CFSG.GF2Type.Widths1112 CFSG.Sporadic.SmallF2 CFSG.GF2W1112

public section

namespace Certificates

open CertificateChecks.KernelCo2W11

open CFSG.GF2Type.Widths1112 CFSG.Sporadic.SmallF2 CFSG.GF2W1112 in
theorem certificate38955 : ∀ U : Submodule (ZMod 2) Vec22, toVecD 22 (w12Co2Rep 2) ∈ U →
    (∀ u ∈ U, bil₀₂ u (toVecD 22 (w12Co2Rep 2)) = 0) →
    (∀ g : CFSG.Blueprint.NativeSporadic.Co2,
      co2Act g (toVecD 22 (w12Co2Rep 2)) = toVecD 22 (w12Co2Rep 2) → ∀ u ∈ U, co2Act g u ∈ U) →
    ∀ y ∈ U, y ∉ Submodule.span (ZMod 2) {toVecD 22 (w12Co2Rep 2)} →
      ∃ u ∈ U, u ≠ toVecD 22 (w12Co2Rep 2) ∧ u ∈ co2Orbit 0 :=
  fun U hrU hperp hU y hyU hy =>
    f3_rep sep2_ok fix2_ok s2_w s2_tgt (by decide) (f0_row _ _ s2_F0) U hrU hperp hU y hyU hy

end Certificates

end

end
