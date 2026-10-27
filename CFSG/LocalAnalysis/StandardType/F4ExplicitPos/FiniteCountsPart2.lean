module

public import CFSG.LocalAnalysis.StandardType.F4ExplicitPos.FiniteCountsPart1

@[expose] public section

public noncomputable section

namespace CFSG.StandardType.F4ExplicitPos.FiniteCounts
open CFSG CFSG.Blueprint.Chevalley CFSG.LieType CFSG.LieType.Chevalley
open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
open CFSG.HardMathSupport.Timmesfeld.Torality
open CFSG.StandardType.F4ExplicitPos.BruhatNo117 CFSG.StandardType.F4ExplicitPos.BruhatUnique
  CFSG.StandardType.F4ExplicitPos.FamilyPosition CFSG.StandardType.F4ExplicitPos.PositiveNo117
open scoped Pointwise
variable {K : Type} [Field K] {ι : Type}

theorem f4_exists_conj_le_of_isPGroup_of_not_dvd_relIndex {Γ : Type*} [Group Γ] [Finite Γ]
    {r : ℕ} [hr : Fact r.Prime] {C N' A : Subgroup Γ} (hA : A ≤ C) (hAp : IsPGroup r A)
    (hI : ¬ r ∣ N'.relIndex C) : ∃ u ∈ C, ∀ x ∈ A, u * x * u⁻¹ ∈ N' := by
  classical
  set N := N'.subgroupOf C
  set A' : Subgroup C := A.subgroupOf C
  have hA'p : IsPGroup r A' := by
    rintro ⟨g, hg⟩
    obtain ⟨k, hk⟩ := hAp ⟨(g : Γ), hg⟩
    refine ⟨k, Subtype.ext (Subtype.ext ?_)⟩
    have := congrArg (fun y : A => (y : Γ)) hk
    simpa using this
  have hcardQ : ¬ r ∣ Nat.card (C ⧸ N) := hI
  obtain ⟨Q, hQ⟩ := hA'p.nonempty_fixed_point_of_prime_not_dvd_card (C ⧸ N) hcardQ
  obtain ⟨z, rfl⟩ := QuotientGroup.mk_surjective Q
  refine ⟨(z : Γ)⁻¹, inv_mem z.2, fun x hx => ?_⟩
  have hxC : x ∈ C := hA hx
  set x' : C := ⟨x, hxC⟩
  have hx' : x' ∈ A' := hx
  have hfix := hQ ⟨x', hx'⟩
  change ((x' * z : C) : C ⧸ N) = (z : C ⧸ N) at hfix
  rw [QuotientGroup.eq] at hfix
  have h1 : (x' * z)⁻¹ * z ∈ N := hfix
  have h2 : z⁻¹ * x' * z ∈ N := by
    have := inv_mem h1
    simpa [mul_assoc] using this
  have h3 := Subgroup.mem_subgroupOf.1 h2
  simpa [mul_assoc] using h3

theorem f4_exists_conj_le_monomial_of_isPGroup
    [Finite K] {r : ℕ} [hr : Fact r.Prime]
    (hqr : ¬ r ∣ Nat.card K) {M : ℕ} (hqM : Nat.card K ≡ 1 [MOD r ^ M])
    (hW : ¬ r ^ M ∣ Nat.card (WeylGroup Tag.F4)) {A : Subgroup (ModGL Tag.F4 K)}
    (hA : A ≤ adjointGroup Tag.F4 K) (hAp : IsPGroup r A) :
    ∃ u ∈ adjointGroup Tag.F4 K, ∀ x ∈ A,
      u * x * u⁻¹ ∈ monomialSubgroup Tag.F4 K := by
  have := finite_modGL (τ := Tag.F4) (K := K)
  exact f4_exists_conj_le_of_isPGroup_of_not_dvd_relIndex hA hAp
    (f4_not_dvd_relIndex_monomial hqr hqM hW)

theorem f4_exists_conj_le_monomial_of_isPGroup_family
    [Finite K]
    (a : ι → Fin Tag.F4.rank → Kˣ) {r : ℕ} [hr : Fact r.Prime]
    (hqr : ¬ r ∣ Nat.card K) {M : ℕ} (hqM : Nat.card K ≡ 1 [MOD r ^ M])
    (hW : ¬ r ^ M ∣ Nat.card (WeylGroup Tag.F4)) {A : Subgroup (ModGL Tag.F4 K)}
    (hA : A ≤ familyCentralizer Tag.F4 K a) (hAp : IsPGroup r A) :
    ∃ u ∈ familyCentralizer Tag.F4 K a, ∀ x ∈ A,
      u * x * u⁻¹ ∈ familyCentralizer Tag.F4 K a ⊓ monomialSubgroup Tag.F4 K := by
  have := finite_modGL (τ := Tag.F4) (K := K)
  exact f4_exists_conj_le_of_isPGroup_of_not_dvd_relIndex hA hAp
    (f4_not_dvd_relIndex_familyCentralizer a hqr hqM hW)

end CFSG.StandardType.F4ExplicitPos.FiniteCounts

end

end
