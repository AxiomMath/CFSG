module

public import CFSG.RankThree.CentralLiftU.UnitaryThreeCoprime
public import CFSG.RankThree.CentralLiftU.UnitaryThreeHeisenberg
public import CFSG.LocalAnalysis.SectionRank.OddCover.CubicCyclic
public import CFSG.LieType.Steinberg.CentralExt.UnitaryThreeLift

public section

namespace CFSG.RankThree.CentralLiftU

open CFSG.LieType.Steinberg CFSG.LieType.Universal.Unitary CFSG.LieType.BorelTits

theorem not_dvd_of_dvd_sq_sub_add_one {p q : ℕ} (hp : p.Prime) (hp3 : 3 < p) (hq : 1 ≤ q)
    (hpq : ¬ p ∣ q) (h : p ∣ q ^ 2 - q + 1) : ¬ p ∣ q ^ 2 * ((q ^ 2) ^ 2 - 1) := by
  have hqq : q ≤ q ^ 2 := Nat.le_self_pow two_ne_zero q
  have hq4 : 1 ≤ (q ^ 2) ^ 2 := Nat.one_le_pow _ _ (Nat.one_le_pow _ _ hq)
  have hp' : Prime (p : ℤ) := Nat.prime_iff_prime_int.mp hp
  have h' : (p : ℤ) ∣ (q : ℤ) ^ 2 - q + 1 := by
    have := Int.natCast_dvd_natCast.2 h
    push_cast [hqq] at this
    exact this
  have hpq' : ¬ (p : ℤ) ∣ (q : ℤ) := fun hd => hpq (Int.natCast_dvd_natCast.1 hd)
  intro hd
  have hd' : (p : ℤ) ∣ (q : ℤ) ^ 2 * (((q : ℤ) - 1) * ((q : ℤ) + 1) * ((q : ℤ) ^ 2 + 1)) := by
    have := Int.natCast_dvd_natCast.2 hd
    push_cast [hq4] at this
    convert this using 1
    ring
  rcases hp'.dvd_or_dvd hd' with h1 | h1
  · exact hpq' (hp'.dvd_of_dvd_pow h1)
  rcases hp'.dvd_or_dvd h1 with h2 | h2
  · rcases hp'.dvd_or_dvd h2 with h3 | h3
    ·
      have h4 : (p : ℤ) ∣ ((q : ℤ) ^ 2 - q + 1) - q * ((q : ℤ) - 1) := dvd_sub h' (h3.mul_left _)
      have h5 : ((q : ℤ) ^ 2 - q + 1) - q * ((q : ℤ) - 1) = 1 := by ring
      rw [h5] at h4
      exact hp'.not_isUnit (isUnit_of_dvd_one h4)
    ·
      have h4 : (p : ℤ) ∣ ((q : ℤ) ^ 2 - q + 1) - ((q : ℤ) - 2) * ((q : ℤ) + 1) :=
        dvd_sub h' (h3.mul_left _)
      have h5 : ((q : ℤ) ^ 2 - q + 1) - ((q : ℤ) - 2) * ((q : ℤ) + 1) = 3 := by ring
      rw [h5] at h4
      have : p ∣ 3 := Int.natCast_dvd_natCast.1 (by exact_mod_cast h4)
      have := Nat.le_of_dvd (by norm_num) this
      omega
  ·
    have h4 : (p : ℤ) ∣ ((q : ℤ) ^ 2 + 1) - ((q : ℤ) ^ 2 - q + 1) := dvd_sub h2 h'
    have h5 : ((q : ℤ) ^ 2 + 1) - ((q : ℤ) ^ 2 - q + 1) = q := by ring
    rw [h5] at h4
    exact hpq' h4

section Cubic

variable {K : Type} [Field K] [Finite K] {ℓ f : ℕ} [Fact ℓ.Prime] [CharP K ℓ]

local notation "σ₀" => unitaryInvolution K ℓ f

theorem ker_eq_bot_SU_three_of_dvd (hK : Nat.card K = (ℓ ^ f) ^ 2) {p : ℕ} [Fact p.Prime]
    (hp3 : 3 < p) (hpℓ : p ≠ ℓ) (hpq : p ∣ (ℓ ^ f) ^ 2 - ℓ ^ f + 1) {R : Type*} [Group R]
    [Finite R] [Group.IsPerfect R] (ρ : R →* SU σ₀ 3) (hcen : ρ.ker ≤ Subgroup.center R)
    (hpk : IsPGroup p ρ.ker) : ρ.ker = ⊥ := by
  obtain ⟨P⟩ : Nonempty (Sylow p R) := inferInstance
  refine ker_eq_bot_of_sylow_commute ρ hcen hpk P (sylow_commute_of_isCyclic_map ρ hcen P ?_)
  have hQ : IsPGroup p ((P : Subgroup R).map ρ) := P.2.map ρ
  set Q := ((P : Subgroup R).map ρ).map (SU σ₀ 3).subtype
  have hQp : IsPGroup p Q := hQ.map _
  have hq1 : 1 ≤ ℓ ^ f := Nat.one_le_pow _ _ (Nat.Prime.pos Fact.out)
  have hnd : ¬ p ∣ Nat.card K * (Nat.card K ^ 2 - 1) := by
    rw [hK]
    refine not_dvd_of_dvd_sq_sub_add_one Fact.out hp3 hq1 (fun hd => hpℓ ?_) hpq
    exact (Nat.prime_dvd_prime_iff_eq Fact.out Fact.out).1 ((Nat.Prime.dvd_of_dvd_pow Fact.out hd))
  have hcyc := (CFSG.SectionRank.OddCover.finite_field_cubic_cyclic_linear_subgroup K).2 p hnd Q
    hQp
  let e := ((P : Subgroup R).map ρ).equivMapOfInjective (SU σ₀ 3).subtype
    (SU σ₀ 3).subtype_injective
  exact isCyclic_of_surjective e.symm.toMonoidHom e.symm.surjective

end Cubic

section Split

variable {K : Type} [Field K] [Finite K] {ℓ f : ℕ} [Fact ℓ.Prime] [CharP K ℓ]

local notation "σ₀" => unitaryInvolution K ℓ f

theorem exists_section_SU_three_large (hK : Nat.card K = (ℓ ^ f) ^ 2) (hℓ2 : ℓ ≠ 2) {p : ℕ}
    (hp : p.Prime) (hp3 : 3 < p) {E : Type*} [Group E] [Finite E] {π : E →* SU σ₀ 3}
    (hπ : Function.Surjective π) (hcen : π.ker ≤ Subgroup.center E) (hpk : IsPGroup p π.ker) :
    ∃ s : SU σ₀ 3 →* E, ∀ x, π (s x) = x := by
  have : Fact p.Prime := ⟨hp⟩
  have : Group.IsPerfect (SU σ₀ 3) := isPerfect_SU_three hK hℓ2
  by_cases hpq : p = ℓ ∨ p ∣ (ℓ ^ f) ^ 2 - ℓ ^ f + 1
  ·
    obtain ⟨hperf, hsurj, hkcen⟩ := derived_restrict_facts π hπ hcen
    have : Group.IsPerfect (commutator E) := hperf
    have hpk' := isPGroup_ker_comp_subtype π hpk (commutator E)
    refine exists_section_of_ker_comp_eq_bot π (commutator E) hsurj ?_
    rcases hpq with rfl | hdvd
    · exact ker_eq_bot_SU_three_of_eq_char hK hp3 _ hsurj hkcen hpk'
    · by_cases hpℓ : p = ℓ
      · subst hpℓ
        exact ker_eq_bot_SU_three_of_eq_char hK hp3 _ hsurj hkcen hpk'
      · exact ker_eq_bot_SU_three_of_dvd hK hp3 hpℓ hdvd _ hkcen hpk'
  · push Not at hpq
    obtain ⟨hpℓ, hndvd⟩ := hpq
    obtain ⟨P, hP⟩ := exists_wittMatrix hK 3
    set e := conjEquiv P hP
    have hker : (e.toMonoidHom.comp π).ker = π.ker := by
      ext x
      rw [MonoidHom.mem_ker, MonoidHom.mem_ker, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom,
        map_eq_one_iff _ e.injective]
    obtain ⟨s, hs⟩ := exists_section_SUid_three_of_coprime hK hℓ2 hp hp3 hpℓ hndvd
      (π := e.toMonoidHom.comp π) (e.surjective.comp hπ) (hker ▸ hcen) (hker ▸ hpk)
    refine ⟨s.comp e.toMonoidHom, fun x => e.injective ?_⟩
    exact hs (e x)

end Split

end CFSG.RankThree.CentralLiftU
