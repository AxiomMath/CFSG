module

public import CFSG.LocalAnalysis.SignalizerFunctor.CompatibleConjugation
public import CFSG.LocalAnalysis.SignalizerFunctor.HallExistence

public section

universe groupUniverse targetUniverse

namespace CFSG.SignalizerFunctor.Helpers

theorem prime_supported_of_dvd (primes : Set ℕ) {order divisor : ℕ}
    (supported : primeSupported primes order) (divides : divisor ∣ order) :
    primeSupported primes divisor := by
  intro prime prime_prime prime_divides
  exact supported prime prime_prime (prime_divides.trans divides)

theorem prime_supported_complement_eq_one (primes : Set ℕ) (order : ℕ)
    (supported : primeSupported primes order)
    (complement_supported : primeSupported primesᶜ order) : order = 1 := by
  by_contra not_one
  obtain ⟨prime, prime_prime, divides⟩ := Nat.exists_prime_and_dvd not_one
  exact complement_supported prime prime_prime divides (supported prime prime_prime divides)

theorem hall_map_surjective
    {GroupType : Type groupUniverse} [Group GroupType]
    {TargetType : Type targetUniverse} [Group TargetType]
    (primes : Set ℕ) (hom : GroupType →* TargetType) (surjective : Function.Surjective hom)
    (subgroup : Subgroup GroupType) (hall : IsHallSubgroup primes subgroup) :
    IsHallSubgroup primes (subgroup.map hom) :=
  ⟨prime_supported_of_dvd primes hall.1 (Subgroup.card_map_dvd subgroup hom),
    prime_supported_of_dvd primesᶜ hall.2 (Subgroup.index_map_dvd subgroup surjective)⟩

theorem hall_subgroupOf
    {GroupType : Type groupUniverse} [Group GroupType]
    (primes : Set ℕ) (subgroup parent : Subgroup GroupType) (contained : subgroup ≤ parent)
    (hall : IsHallSubgroup primes subgroup) : IsHallSubgroup primes (subgroup.subgroupOf parent) := by
  constructor
  · rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe contained).toEquiv]
    exact hall.1
  · change primeSupported primesᶜ (subgroup.relIndex parent)
    exact prime_supported_of_dvd primesᶜ hall.2 (Subgroup.relIndex_dvd_index_of_le contained)

theorem hall_conjugate
    {GroupType : Type groupUniverse} [Group GroupType]
    (primes : Set ℕ) (subgroup : Subgroup GroupType) (element : GroupType)
    (hall : IsHallSubgroup primes subgroup) :
    IsHallSubgroup primes (conjugateSubgroup element subgroup) := by
  constructor
  · rw [conjugate_subgroup_card]
    exact hall.1
  · change primeSupported primesᶜ (subgroup.map (MulAut.conj element).toMonoidHom).index
    rw [MulEquiv.toMonoidHom_eq_coe, Subgroup.index_map_equiv]
    exact hall.2

theorem hall_eq_top_of_group_supported
    {GroupType : Type groupUniverse} [Group GroupType]
    (primes : Set ℕ) (subgroup : Subgroup GroupType) (hall : IsHallSubgroup primes subgroup)
    (group_supported : primeSupported primes (Nat.card GroupType)) : subgroup = ⊤ := by
  apply Subgroup.index_eq_one.mp
  exact prime_supported_complement_eq_one primes subgroup.index
    (prime_supported_of_dvd primes group_supported (Subgroup.index_dvd_card subgroup)) hall.2

theorem hall_quotient_top
    {GroupType : Type groupUniverse} [Group GroupType]
    (primes : Set ℕ) (normal subgroup : Subgroup GroupType) [normal.Normal]
    (hall : IsHallSubgroup primes subgroup)
    (quotient_supported : primeSupported primes (Nat.card (GroupType ⧸ normal))) :
    subgroup.map (QuotientGroup.mk' normal) = ⊤ :=
  hall_eq_top_of_group_supported primes _
    (hall_map_surjective primes _ (QuotientGroup.mk'_surjective normal) subgroup hall)
    quotient_supported

theorem sup_normal_eq_of_quotient_map_eq
    {GroupType : Type groupUniverse} [Group GroupType]
    (normal first second : Subgroup GroupType) [normal.Normal]
    (mapped_equal : first.map (QuotientGroup.mk' normal) =
      second.map (QuotientGroup.mk' normal)) : first ⊔ normal = second ⊔ normal := by
  have equal := congrArg (Subgroup.comap (QuotientGroup.mk' normal)) mapped_equal
  simpa only [Subgroup.comap_map_eq, QuotientGroup.ker_mk'] using equal

theorem sup_normal_eq_top_of_quotient_map_eq_top
    {GroupType : Type groupUniverse} [Group GroupType]
    (normal subgroup : Subgroup GroupType) [normal.Normal]
    (mapped_top : subgroup.map (QuotientGroup.mk' normal) = ⊤) : subgroup ⊔ normal = ⊤ := by
  have equal := congrArg (Subgroup.comap (QuotientGroup.mk' normal)) mapped_top
  simpa only [Subgroup.comap_map_eq, QuotientGroup.ker_mk', Subgroup.comap_top] using equal

theorem complement_of_normal_sup_disjoint
    {GroupType : Type groupUniverse} [Group GroupType]
    (normal complement : Subgroup GroupType) [normal.Normal]
    (whole : normal ⊔ complement = ⊤) (disjoint : Disjoint normal complement) :
    normal.IsComplement' complement := by
  apply Subgroup.isComplement'_of_disjoint_and_mul_eq_univ disjoint
  ext element
  constructor
  · intro _
    trivial
  · intro _
    have member : element ∈ normal ⊔ complement := by
      rw [whole]
      trivial
    obtain ⟨first, first_member, second, second_member, product⟩ :=
      Subgroup.mem_sup_of_normal_left.mp member
    exact ⟨first, first_member, second, second_member, product⟩

theorem hall_complement_of_quotient_supported
    {GroupType : Type groupUniverse} [Group GroupType]
    (primes : Set ℕ) (normal subgroup : Subgroup GroupType) [normal.Normal]
    (hall : IsHallSubgroup primes subgroup)
    (normal_supported : primeSupported primesᶜ (Nat.card normal))
    (quotient_supported : primeSupported primes (Nat.card (GroupType ⧸ normal))) :
    normal.IsComplement' subgroup := by
  apply complement_of_normal_sup_disjoint normal subgroup
  · rw [sup_comm]
    exact sup_normal_eq_top_of_quotient_map_eq_top normal subgroup
      (hall_quotient_top primes normal subgroup hall quotient_supported)
  · exact Subgroup.disjoint_of_coprime_natCard
      (prime_supported_coprime primes hall.1 normal_supported).symm

end CFSG.SignalizerFunctor.Helpers
