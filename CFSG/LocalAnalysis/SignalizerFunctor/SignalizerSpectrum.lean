module

public import CFSG.LocalAnalysis.SignalizerFunctor.PrimeSubfunctorValues
public import CFSG.LocalAnalysis.SignalizerFunctor.SignalizerImages
public import CFSG.LocalAnalysis.SignalizerFunctor.SignalizerSubgroups

public section

open CFSG.Open

universe groupUniverse imageUniverse

namespace CFSG.SignalizerFunctor.Helpers

variable {GroupType : Type groupUniverse} [Group GroupType]
variable {ImageType : Type imageUniverse} [Group ImageType]

@[expose] def signalizerSpectrum (prime rank : ℕ) (actor : Subgroup GroupType)
    (values : Subgroup GroupType → Subgroup GroupType) : Set ℕ :=
  {groupPrime | groupPrime.Prime ∧
    ∃ selected ∈ signalizerFunctorEk prime rank actor, groupPrime ∣ Nat.card (values selected)}

theorem signalizer_spectrum_finite [Finite GroupType] (prime rank : ℕ)
    (actor : Subgroup GroupType) (values : Subgroup GroupType → Subgroup GroupType) :
    (signalizerSpectrum prime rank actor values).Finite := by
  apply (Nat.card GroupType).primeFactors.finite_toSet.subset
  rintro groupPrime ⟨prime_prime, selected, _, divides⟩
  exact Nat.mem_primeFactors.mpr ⟨prime_prime,
    divides.trans (Subgroup.card_subgroup_dvd_card (values selected)), Nat.card_pos.ne'⟩

theorem signalizer_values_spectrum_supported (prime rank : ℕ)
    (actor : Subgroup GroupType) (values : Subgroup GroupType → Subgroup GroupType)
    (selected : Subgroup GroupType) (member : selected ∈ signalizerFunctorEk prime rank actor) :
    primeSupported (signalizerSpectrum prime rank actor values) (Nat.card (values selected)) := by
  intro groupPrime prime_prime divides
  exact ⟨prime_prime, selected, member, divides⟩

theorem signalizer_spectrum_subset_of_supported (prime rank : ℕ)
    (actor : Subgroup GroupType) (values : Subgroup GroupType → Subgroup GroupType)
    (primes : Set ℕ)
    (supported : ∀ selected ∈ signalizerFunctorEk prime rank actor,
      primeSupported primes (Nat.card (values selected))) :
    signalizerSpectrum prime rank actor values ⊆ primes := by
  rintro groupPrime ⟨prime_prime, selected, member, divides⟩
  exact supported selected member groupPrime prime_prime divides

theorem signalizer_spectrum_of_le [Finite GroupType] (prime rank : ℕ)
    (actor : Subgroup GroupType) (values smallerValues : Subgroup GroupType → Subgroup GroupType)
    (contained : ∀ selected ∈ signalizerFunctorEk prime rank actor,
      smallerValues selected ≤ values selected) :
    signalizerSpectrum prime rank actor smallerValues ⊆ signalizerSpectrum prime rank actor values := by
  rintro groupPrime ⟨prime_prime, selected, member, divides⟩
  exact ⟨prime_prime, selected, member,
    divides.trans (Subgroup.card_dvd_of_le (contained selected member))⟩

theorem signalizer_spectrum_prime_excluded (prime rank : ℕ)
    (prime_prime : prime.Prime) (actor : Subgroup GroupType)
    (values : Subgroup GroupType → Subgroup GroupType)
    (coprime : ∀ selected ∈ signalizerFunctorEk prime rank actor,
      Nat.Coprime prime (Nat.card (values selected))) :
    prime ∉ signalizerSpectrum prime rank actor values := by
  rintro ⟨_, selected, member, divides⟩
  exact prime_prime.coprime_iff_not_dvd.mp (coprime selected member) divides

theorem signalizer_image_spectrum (prime rank : ℕ)
    (homomorphism : GroupType →* ImageType) (actor : Subgroup GroupType)
    (injective : Function.Injective (homomorphism.domRestrict actor))
    (values : Subgroup GroupType → Subgroup GroupType) :
    signalizerSpectrum prime rank (actor.map homomorphism)
      (signalizerImageValues homomorphism actor values) ⊆
        signalizerSpectrum prime rank actor values :=
  signalizer_spectrum_subset_of_supported prime rank _ _ _
    (signalizer_image_supported prime rank homomorphism actor injective values _
      (signalizer_values_spectrum_supported prime rank actor values))

theorem signalizer_subgroup_spectrum (prime rank : ℕ)
    (actor ambient : Subgroup GroupType) (contained : actor ≤ ambient)
    (values : Subgroup GroupType → Subgroup GroupType) :
    signalizerSpectrum prime rank (actor.subgroupOf ambient)
      (signalizerSubgroupValues ambient values) ⊆ signalizerSpectrum prime rank actor values :=
  signalizer_spectrum_subset_of_supported prime rank _ _ _
    (signalizer_subgroup_supported prime rank actor ambient contained values _
      (signalizer_values_spectrum_supported prime rank actor values))

theorem signalizer_prime_subfunctor_spectrum [Finite GroupType]
    (prime rank : ℕ) (prime_prime : prime.Prime)
    (actor : Subgroup GroupType) (elementary : IsElemAbelian prime actor)
    (values : Subgroup GroupType → Subgroup GroupType) (primes : Set ℕ)
    (coprime : ∀ selected ∈ signalizerFunctorEk prime rank actor,
      Nat.Coprime prime (Nat.card (values selected)))
    (normalized : ∀ selected ∈ signalizerFunctorEk prime rank actor,
      actor ≤ Subgroup.normalizer (values selected : Set GroupType))
    (balanced : ∀ selected ∈ signalizerFunctorEk prime rank actor,
      ∀ other ∈ signalizerFunctorEk prime rank actor,
        values selected ⊓ Subgroup.centralizer (other : Set GroupType) ≤ values other)
    (solvable : ∀ selected ∈ signalizerFunctorEk prime rank actor,
      Group.IsSolvable (values selected)) :
    signalizerSpectrum prime rank actor (signalizerPrimeValue prime rank actor values primes) ⊆
      signalizerSpectrum prime rank actor values ∩ primes := by
  intro groupPrime member
  refine ⟨signalizer_spectrum_of_le prime rank actor values _
    (fun selected _ => signalizer_prime_value_le prime rank actor values primes selected) member, ?_⟩
  exact signalizer_spectrum_subset_of_supported prime rank actor _ primes
    (fun selected selected_member => signalizer_prime_value_supported prime rank prime_prime actor
      elementary values primes balanced selected selected_member (coprime selected selected_member)
      (normalized selected selected_member) (solvable selected selected_member)) member

end CFSG.SignalizerFunctor.Helpers
