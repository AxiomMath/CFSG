module

public import Certificates.Data.J3E27.Words
public import CFSG.Sporadic.J3.Group
public import CFSG.Sporadic.Bridge.TwoGen
import Certificates.Kernel.J3E27.Facts810202

public section

namespace Certificates

open CertificateChecks

open CFSG.Sporadic.J3 CFSG.Sporadic.J3.Native CFSG.Sporadic.Bridge CFSG.Sporadic.Bridge.TwoGen in
theorem certificate810202 : ∀ W₁ W₂ X₃ S T : J j3Data,
    W₁ = wordProd (img2 (CFSG.Sporadic.J3.a j3Data) (b j3Data)) J3E27.wordW1 →
    W₂ = wordProd (img2 (CFSG.Sporadic.J3.a j3Data) (b j3Data)) J3E27.wordW2 →
    X₃ = wordProd (img2 (CFSG.Sporadic.J3.a j3Data) (b j3Data)) J3E27.wordX3 →
    S = wordProd (img2 (CFSG.Sporadic.J3.a j3Data) (b j3Data)) J3E27.wordS →
    T = wordProd (img2 (CFSG.Sporadic.J3.a j3Data) (b j3Data)) J3E27.wordT →
    W₁ ^ 3 = 1 ∧ W₂ ^ 3 = 1 ∧ X₃ ^ 3 = 1 ∧ W₁ * W₂ = W₂ * W₁ ∧ W₁ * X₃ = X₃ * W₁ ∧
      W₂ * X₃ = X₃ * W₂ ∧ S * W₂ * S⁻¹ = W₁ * W₂ ∧ S * X₃ * S⁻¹ = X₃⁻¹ ∧
      T * W₁ * T⁻¹ = W₁⁻¹ ∧ T * W₂ * T⁻¹ = W₂⁻¹ ∧ T * X₃ * T⁻¹ = X₃ ∧
      Function.Injective fun v : Fin 3 × Fin 3 × Fin 3 =>
        W₁ ^ (v.1 : ℕ) * W₂ ^ (v.2.1 : ℕ) * X₃ ^ (v.2.2 : ℕ) := KernelJ3E27.e27_facts

end Certificates
