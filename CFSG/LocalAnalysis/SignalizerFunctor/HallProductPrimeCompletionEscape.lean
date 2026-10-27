module

public import CFSG.LocalAnalysis.SignalizerFunctor.SignalizerFactorization
public import CFSG.LocalAnalysis.SignalizerFunctor.HallProductPrimeEscape

public section

open CFSG.Open

universe groupUniverse

namespace CFSG.SignalizerFunctor.Helpers

variable {GroupType : Type groupUniverse} [Group GroupType] [Finite GroupType]
variable {prime rank groupPrime : ℕ} {actor parent complement factor : Subgroup GroupType}
variable {values : Subgroup GroupType → Subgroup GroupType}

theorem incomplete_abelian_hall_product_prime_completion_escape (kernel : Subgroup GroupType)
    (datum : IncompleteSignalizerHallProduct prime rank groupPrime actor parent complement factor values)
    (abelian : IsMulCommutative factor) (kernel_le : kernel ≤ complement) (kernel_nontrivial : kernel ≠ ⊥)
    (kernel_normal : (kernel.subgroupOf complement).Normal)
    (kernel_normalized : actor ≤ Subgroup.normalizer (kernel : Set GroupType))
    (common_normalized : signalizerCommonFixed prime rank actor values ≤ Subgroup.normalizer (kernel : Set GroupType))
    (kernelPrime : ℕ) (kernelPrime_prime : kernelPrime.Prime)
    (kernelPrime_spectrum : kernelPrime ∈ signalizerSpectrum prime rank actor values)
    (kernel_coprime : Nat.Coprime kernelPrime (Nat.card kernel)) :
    ¬ factor ≤ signalizerPrimeCompletion prime rank actor values
      (signalizerSpectrum prime rank actor values \ {kernelPrime}) := by
  have kernel_compatible := solvable_signalizer_compatible_of_le prime rank actor values complement kernel
    datum.complement_compatible kernel_le kernel_normalized
  have supported : primeSupported (signalizerSpectrum prime rank actor values \ {kernelPrime}) (Nat.card kernel) := by
    intro divisor divisor_prime divides
    obtain ⟨selected, member, value_divides⟩ := signalizer_compatible_prime_support prime rank divisor
      datum.prime_prime divisor_prime actor datum.elementary datum.large values datum.conditions.coprime
      kernel kernel_compatible.1 divides
    refine ⟨⟨divisor_prime, selected, member, value_divides⟩, ?_⟩
    intro same
    exact kernelPrime_prime.coprime_iff_not_dvd.mp kernel_coprime (same ▸ divides)
  let completion := signalizerPrimeCompletion prime rank actor values
    (signalizerSpectrum prime rank actor values \ {kernelPrime})
  have complete := datum.locally_complete.2 kernelPrime kernelPrime_spectrum
  have control := signalizer_prime_completion_control prime rank datum.prime_prime actor datum.elementary
    datum.large values datum.conditions _ complete.1
  have kernel_completion : kernel ≤ completion := control.2.2.2 kernel kernel_compatible.1 supported common_normalized
  have target_compatible := solvable_signalizer_compatible_of_le prime rank actor values completion
    (parent ⊓ completion) ⟨control.1, complete.2⟩ inf_le_right
    (normalizer_inf_of_le actor parent completion datum.parent_normalized control.1.1)
  intro factor_completion
  exact incomplete_abelian_hall_product_normal_kernel_escape kernel (parent ⊓ completion) datum abelian kernel_le
    kernel_nontrivial kernel_normal inf_le_left target_compatible
    (le_inf (kernel_le.trans datum.complement_le) kernel_completion) (le_inf datum.factor_le factor_completion)

end CFSG.SignalizerFunctor.Helpers
