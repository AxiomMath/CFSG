module

public import CFSG.Quasithin.EmptyFaithful.R3c3Inner

public section

namespace CFSG.Quasithin.R3c5

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank
  CFSG.ComponentClassification.OuterAutomorphisms
open scoped commutatorElement

section S3

theorem perm_three_pow_three_eq_one_of_odd {g : Equiv.Perm (Fin 3)} (hg : Odd (orderOf g)) :
    g ^ 3 = 1 := by
  have h6 : g ^ 6 = 1 := by
    have : ∀ x : Equiv.Perm (Fin 3), x ^ 6 = 1 := by decide +kernel
    exact this g
  have hm : g ^ orderOf g = 1 := pow_orderOf_eq_one g
  have hgcd := pow_gcd_eq_one.2 ⟨hm, h6⟩
  obtain ⟨d, hd⟩ : ∃ d, d = Nat.gcd (orderOf g) 6 := ⟨_, rfl⟩
  rw [← hd] at hgcd
  have hd1 : d ∣ 6 := hd ▸ Nat.gcd_dvd_right _ _
  have hd2 : Odd d := hd ▸ hg.of_dvd_nat (Nat.gcd_dvd_left _ _)
  have hd3 : d ∣ 3 := by
    have hle : d ≤ 6 := Nat.le_of_dvd (by norm_num) hd1
    rw [Nat.odd_iff] at hd2
    interval_cases d <;> omega
  obtain ⟨k, hk⟩ := hd3
  have h3 : g ^ 3 = g ^ (d * k) := congrArg (fun n => g ^ n) hk
  rw [pow_mul, hgcd, one_pow] at h3
  exact h3

variable {G : Type} [Group G]

theorem rho_eq_one_of_s3 [Finite G] {H Y : Subgroup G} {A : Type} [Group A] (hA : ∀ a b : A, a * b = b * a)
    (hYH : Y ≤ H) (hY : oTwoUpper Y = Y) (ψ : ↥H →* Equiv.Perm (Fin 3))
    (hψs : Function.Surjective ψ) (hψk : ψ.ker = (pCoreOf 2 H).subgroupOf H) (ρ : ↥H →* A) :
    ∀ (y : G) (hy : y ∈ Y), ρ ⟨y, hYH hy⟩ = 1 := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hodd : ∀ (y : G) (hy : y ∈ Y), Odd (orderOf y) → ρ ⟨y, hYH hy⟩ = 1 := by
    intro y hy hyo
    have hyH : y ∈ H := hYH hy
    have hord : Odd (orderOf (⟨y, hyH⟩ : ↥H)) := by
      have : orderOf (⟨y, hyH⟩ : ↥H) = orderOf y := Subgroup.orderOf_mk _ _
      rwa [this]
    have hψo : Odd (orderOf (ψ ⟨y, hyH⟩)) := hord.of_dvd_nat (orderOf_map_dvd ψ _)
    have hψ3 : ψ ⟨y, hyH⟩ ^ 3 = 1 := perm_three_pow_three_eq_one_of_odd hψo
    obtain ⟨a, b, hab⟩ := R3c3.exists_commutator_perm_three _ hψ3
    obtain ⟨a', rfl⟩ := hψs a
    obtain ⟨b', rfl⟩ := hψs b
    obtain ⟨k, hkdef⟩ : ∃ k : ↥H, k = a' * b' * a'⁻¹ * b'⁻¹ := ⟨_, rfl⟩
    have hρk : ρ k = 1 := by
      rw [hkdef, map_mul, map_mul, map_mul, map_inv, map_inv, hA (ρ a') (ρ b')]
      group
    have hr : k⁻¹ * ⟨y, hyH⟩ ∈ ψ.ker := by
      rw [MonoidHom.mem_ker, map_mul, map_inv, hkdef, map_mul, map_mul, map_mul, map_inv, map_inv,
        ← hab]
      group
    rw [hψk, Subgroup.mem_subgroupOf] at hr
    obtain ⟨j, hj⟩ := (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 H) ⟨_, hr⟩
    have hj' : (k⁻¹ * ⟨y, hyH⟩) ^ 2 ^ j = 1 := Subtype.ext (by simpa using congrArg Subtype.val hj)
    have hρo : ρ ⟨y, hYH hy⟩ ^ 2 ^ j = 1 := by
      have h1 : ρ (k⁻¹ * ⟨y, hyH⟩) = ρ ⟨y, hYH hy⟩ := by
        rw [map_mul, map_inv, hρk, inv_one, one_mul]
      rw [← h1, ← map_pow, hj', map_one]
    have hordρ : Odd (orderOf (ρ ⟨y, hYH hy⟩)) :=
      hord.of_dvd_nat (orderOf_map_dvd ρ _)
    have h3 : orderOf (ρ ⟨y, hYH hy⟩) ∣ 2 ^ j := orderOf_dvd_of_pow_eq_one hρo
    have hcop : Nat.Coprime (orderOf (ρ ⟨y, hYH hy⟩)) (2 ^ j) :=
      Nat.Coprime.pow_right j (Nat.coprime_two_right.mpr hordρ)
    exact orderOf_eq_one_iff.mp (Nat.Coprime.eq_one_of_dvd hcop h3)
  intro y hy
  have hYk : Y ≤ (ρ.ker).map H.subtype := by
    rw [← hY]
    refine (Subgroup.closure_le _).2 ?_
    rintro y ⟨hy, hyo⟩
    exact ⟨⟨y, hYH hy⟩, hodd y hy hyo, rfl⟩
  obtain ⟨z, hz, hzy⟩ := hYk hy
  have : z = ⟨y, hYH hy⟩ := Subtype.ext hzy
  rw [← this]
  exact hz

end S3

end CFSG.Quasithin.R3c5
