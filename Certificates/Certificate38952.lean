
module

public import CFSG.GF2Type.Widths1112.Co2FormDefs
import Certificates.Kernel.Co2W11.Glue

public section

open CFSG.GF2Type.Widths1112 CFSG.Sporadic.SmallF2 CFSG.GF2W1112 Matrix

public section

namespace Certificates

open CertificateChecks

open CFSG.GF2Type.Widths1112 CFSG.Sporadic.SmallF2 CFSG.GF2W1112 Matrix in
theorem certificate38952 : (∀ (g : CFSG.Blueprint.NativeSporadic.Co2) (v : Vec22), q₀₂ (co2Act g v) = q₀₂ v) ∧
    (∀ u : Vec22, (∀ v, bil₀₂ u v = 0) → u = 0) ∧
    (∀ c : Vec22, (∀ (g : CFSG.Blueprint.NativeSporadic.Co2) (v : Vec22),
      c ⬝ᵥ co2Act g v = c ⬝ᵥ v) → c = 0) ∧
    (∀ c : Vec22, (∀ g : CFSG.Blueprint.NativeSporadic.Co2,
      co2Act g (toVecD 22 (w12Co2Rep 0)) = toVecD 22 (w12Co2Rep 0) →
        ∀ v : Vec22, c ⬝ᵥ co2Act g v = c ⬝ᵥ v) →
      c = 0 ∨ ∀ v : Vec22, c ⬝ᵥ v = bil₀₂ (toVecD 22 (w12Co2Rep 0)) v) ∧
    (∀ i < 3, toVecD 22 (w12Co2Rep i) ≠ 0 ∧ q₀₂ (toVecD 22 (w12Co2Rep i)) = 0) :=
  ⟨KernelCo2W11.forms_q, KernelCo2W11.forms_nondeg, KernelCo2W11.forms_nofix,
    KernelCo2W11.forms_fixH0, KernelCo2W11.forms_reps⟩

end Certificates

end

end
