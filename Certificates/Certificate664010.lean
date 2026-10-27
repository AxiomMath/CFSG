module

public import Certificates.Kernel.TwoM22.Assembly

public section

namespace Certificates

open CertificateChecks

open CFSG.Quasithin.TwoM22.Gens in
theorem certificate664010 :
    (∀ r ∈ CFSG.Sporadic.Recognition.M22Multiplier.m22Cover,
      FreeGroup.lift twoM22Gen (FreeGroup.mk r) = 1) ∧
    twoM22Gen 1 ^ 11 ≠ 1 ∧ twoM22Gen 1 ^ 22 = 1 ∧ twoM22T * twoM22T = 1 ∧
    (∀ i, twoM22T * twoM22Gen i * twoM22T⁻¹ ∈ twoM22M) ∧ twoM22T ∉ twoM22M ∧
    (∀ x : TwoM22W, (∀ m ∈ twoM22M, x * m = m * x) → x = 1 ∨ x = twoM22Gen 1 ^ 11) ∧
    twoM22S ≤ twoM22M ⊔ Subgroup.zpowers twoM22T ∧ Nat.card twoM22S = 2 ^ 9 ∧
    (∀ y ∈ twoM22S, y ∉ twoM22M → y * y ≠ twoM22Gen 1 ^ 11) :=
  TwoM22K.facts

end Certificates
