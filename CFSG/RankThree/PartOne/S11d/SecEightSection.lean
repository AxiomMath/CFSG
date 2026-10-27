module

public import CFSG.RankThree.PartOne.S11d.PlaneAll
public import CFSG.RankThree.PartOne.S11c.Sec68

public section

namespace CFSG.RankThree.PartOne

open Subgroup CFSG CFSG.Assembly CFSG.Assembly.LowTwoRank CFSG.Blueprint.Multiplier
open CFSG.Blueprint (Catalog)
open CFSG.Assembly.RankThreeEven (localRank)

section Rank

variable {G : Type} [Group G] [Finite G] {I : Subgroup G} {Γ : Type} [Group Γ] [Finite Γ]
  {K : Subgroup Γ}

omit [Finite G] [Finite Γ] in
theorem surjective_centerQuotient_comp (π₀ : ↥I →* ↥K) (hπ₀ : Function.Surjective π₀) :
    Function.Surjective ((QuotientGroup.mk' (Subgroup.center ↥K)).comp π₀) :=
  (QuotientGroup.mk'_surjective _).comp hπ₀

theorem sec68_psl_section (he : evenRank G ≤ 3) (π₀ : ↥I →* ↥K) (hπ₀ : Function.Surjective π₀)
    {p ℓ n f : ℕ} (hp : p.Prime) (hp3 : 3 < p) (hloc : localRank p Γ ≤ 3)
    (hmod : StatedClassicalModel (↥K ⧸ Subgroup.center ↥K) .PSL n ℓ f) (hpn : p ∣ n)
    (hpq : p ∣ ℓ ^ f - 1) : False := by
  classical
  have hp2 : p ≠ 2 := by omega
  have hmod0 := hmod
  obtain ⟨⟨hℓ, hf, hn2, -⟩, k, _, hkfin, hk, ⟨e⟩⟩ := hmod
  have hp5 := five_le_of_prime' hp hp3
  have hn5 : 5 ≤ n := le_trans hp5 (Nat.le_of_dvd (by omega) hpn)
  have := Fintype.ofFinite k
  have : Fact ℓ.Prime := ⟨hℓ⟩
  have hchar : CharP k ℓ := charP_of_card_eq_prime_pow (f := f) (by
    rw [← Nat.card_eq_fintype_card, hk])
  have hpk : p ∣ Fintype.card k - 1 := by rwa [← Nat.card_eq_fintype_card, hk]
  let ψ : ↥K ⧸ Subgroup.center ↥K ≃* Matrix.ProjectiveSpecialLinearGroup (Fin n) k :=
    e.trans (projectiveSpecialLinearGroupEquivStatedProj n k).symm
  let φ₂ : ↥K →* Matrix.ProjectiveSpecialLinearGroup (Fin n) k :=
    ψ.toMonoidHom.comp (QuotientGroup.mk' (Subgroup.center ↥K))
  have hφs : Function.Surjective φ₂ := ψ.surjective.comp (QuotientGroup.mk'_surjective _)
  obtain ⟨-, -, -, -, -, -, -, hle⟩ :=
    CFSG.RankThree.CentralCover.linear_split_prime_central_cover_two_local_rank K hℓ hp hp3 hpk
      (by omega) φ₂ hφs (quotient_cover_ker ψ)
  have hn : n = 5 := by
    by_cases hℓ2 : ℓ = 2
    · simp only [hℓ2, hpn, ↓reduceIte] at hle
      by_contra hne
      have h6 : n = 6 := by omega
      exact not_dvd_six hp hp3 (h6 ▸ hpn)
    · simp only [hℓ2, hpn, ↓reduceIte] at hle
      omega
  subst hn
  have hp5' : p = 5 := (Nat.prime_dvd_prime_iff_eq hp Nat.prime_five).mp hpn
  subst hp5'
  have hπ := surjective_centerQuotient_comp π₀ hπ₀
  have h4 : 4 ≤ evenRank G := by
    by_cases hℓ2 : ℓ = 2
    · subst hℓ2
      exact (even_square_field_linear_five_sections_force_two_local_rank_four (G := G)).1 hf
        (even_of_five_dvd_two_pow_sub_one hpq) hmod0 I _ hπ
    · exact (odd_characteristic_split_degree_five_sections_force_two_local_rank_four
        (G := G)).1 hℓ hℓ2 hf (Or.inl rfl) (Or.inl ⟨rfl, hpq⟩) hmod0 I _ hπ
  omega

theorem sec68_psu_section (he : evenRank G ≤ 3) (π₀ : ↥I →* ↥K) (hπ₀ : Function.Surjective π₀)
    {p ℓ n f : ℕ} (hp : p.Prime) (hp3 : 3 < p) (hloc : localRank p Γ ≤ 3)
    (hmod : StatedClassicalModel (↥K ⧸ Subgroup.center ↥K) .PSU n ℓ f) (hpn : p ∣ n)
    (hpq : p ∣ ℓ ^ f + 1) : ℓ = 2 ∧ n = 5 ∧ p = 5 := by
  classical
  have hp2 : p ≠ 2 := by omega
  have hmod0 := hmod
  obtain ⟨⟨hℓ, hf, hn3, -⟩, k, _, hkfin, hk, ⟨e⟩⟩ := hmod
  have hp5 := five_le_of_prime' hp hp3
  have hn5 : 5 ≤ n := le_trans hp5 (Nat.le_of_dvd (by omega) hpn)
  have hU : CFSG.LocalAnalysis.ComponentInitial.UnitaryFieldData ℓ f k :=
    ⟨hℓ, hf, by rw [hk, ← pow_mul, mul_comm]⟩
  let ψ : ↥K ⧸ Subgroup.center ↥K ≃* CFSG.ClassicalGroups.UnitaryFlag.unitaryPSU hU n :=
    e.trans (CFSG.ClassicalGroups.UnitaryFlag.unitaryPSUEquiv hU (by omega)).symm
  let φ₂ : ↥K →* CFSG.ClassicalGroups.UnitaryFlag.unitaryPSU hU n :=
    ψ.toMonoidHom.comp (QuotientGroup.mk' (Subgroup.center ↥K))
  have hφs : Function.Surjective φ₂ := ψ.surjective.comp (QuotientGroup.mk'_surjective _)
  obtain ⟨u, -, hu, V, hV, hVab, hVcard⟩ :=
    CFSG.RankThree.Classical2.unitary_split_prime_central_cover_two_local_rank K hU hp hp3 hpq
      (by omega) φ₂ hφs (quotient_cover_ker ψ)
  have hle := CFSG.RankThree.Classical2.le_localRank_of_involution_elemAbelian hp hu
    (le_inf_iff.mp hV).2 hVab hVcard
  have hn : n = 5 := by
    by_cases hℓ2 : ℓ = 2
    · simp only [hℓ2, hpn, ↓reduceIte] at hle
      by_contra hne
      have h6 : n = 6 := by omega
      exact not_dvd_six hp hp3 (h6 ▸ hpn)
    · simp only [hℓ2, hpn, ↓reduceIte] at hle
      omega
  subst hn
  have hp5' : p = 5 := (Nat.prime_dvd_prime_iff_eq hp Nat.prime_five).mp hpn
  subst hp5'
  by_cases hℓ2 : ℓ = 2
  · exact ⟨hℓ2, rfl, rfl⟩
  · exfalso
    have hπ := surjective_centerQuotient_comp π₀ hπ₀
    have h4 : 4 ≤ evenRank G :=
      (odd_characteristic_split_degree_five_sections_force_two_local_rank_four
        (G := G)).1 hℓ hℓ2 hf (Or.inr rfl) (Or.inr ⟨rfl, hpq⟩) hmod0 I _ hπ
    omega

end Rank

section Main

theorem sec6EightSection_of_tables
    (hGA : CFSG.Open.GriessAllModelsStatement)
    (hAlt : ∀ (K : Type) [Group K] [Finite K] [Group.IsPerfect K] (n : ℕ), 5 ≤ n →
      (K ⧸ Subgroup.center K ≃* alternatingGroup (Fin n)) → ∀ p : ℕ, p.Prime → 3 < p →
      ¬ p ∣ Nat.card (Subgroup.center K))
    (hExc : ExceptionalCenterSmallPrimes) (hSpor : SporadicCenterSmallPrimes) :
    SectionProvider Sec68Hyp := by
  intro G _ _ he I Γ _ _ φ p hp hp5 hloc hK hcat hpZ
  have hp3 : 3 < p := by omega
  have : Group.IsPerfect ↥φ.range := hK.1
  rcases hcat with ⟨q, hq, ⟨e⟩⟩ | ⟨m, hm, ⟨e⟩⟩ | hcl | hex | hsp
  · exfalso
    obtain ⟨a, b, hab⟩ := hK.2.2
    exact hab (e.injective (by rw [map_mul, map_mul]; exact mul_comm _ _))
  · exact absurd hpZ (hAlt ↥φ.range m hm e p hp hp3)
  · obtain ⟨t, n, ℓ, f, hmod⟩ := hcl
    have hdvd := card_center_dvd_of_model hGA hK hmod
    rcases prime_dvd_table hp hp3 (hpZ.trans hdvd) with ⟨rfl, hpn, hpq⟩ | ⟨rfl, hpn, hpq⟩
    · exact (sec68_psl_section he φ.rangeRestrict φ.rangeRestrict_surjective hp hp3 hloc hmod
        hpn hpq).elim
    · obtain ⟨rfl, rfl, rfl⟩ := sec68_psu_section he φ.rangeRestrict φ.rangeRestrict_surjective
        hp hp3 hloc hmod hpn hpq
      have hf : 1 ≤ f := hmod.1.2.1
      have hord : (genericOrders .PSU 5 2 f).1 * (genericOrders .PSU 5 2 f).2 *
          ((exceptionalOrders .PSU 5 2 f).1 * (exceptionalOrders .PSU 5 2 f).2) = 5 := by
        have h1 : genericOrders .PSU 5 2 f = (Nat.gcd 5 (2 ^ f + 1), 1) := rfl
        have h2 : exceptionalOrders .PSU 5 2 f = (1, 1) := by
          unfold exceptionalOrders
          simp
        rw [h1, h2, Nat.gcd_eq_left hpq]
        norm_num
      rw [hord] at hdvd
      exact ⟨rfl, Nat.dvd_antisymm hdvd hpZ, f, hf, hmod⟩
  · exact absurd hpZ (hExc ↥φ.range hK hex p hp hp3)
  · exact absurd hpZ (hSpor ↥φ.range hK hsp p hp hp3)

end Main

end CFSG.RankThree.PartOne
