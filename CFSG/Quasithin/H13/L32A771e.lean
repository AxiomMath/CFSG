module

public import CFSG.Quasithin.EmptyFaithful.S1422Basic
public import CFSG.Quasithin.H13.L32AL24

public section

namespace CFSG.Quasithin.H13.L32A

open CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique CFSG.LieType.BorelTits CFSG.Quasithin.RuType
open scoped MatrixGroups commutatorElement

variable {G : Type} [Group G] [Finite G]

theorem f4_three : ∀ v : Fin 2 → F4, v + v + v = v := by decide

theorem sl24_eq_one_of_fix : ∀ A : SL(2, F4),
    (∀ v : Fin 2 → F4, (A : Matrix (Fin 2) (Fin 2) F4).mulVec v = v) → A = 1 := by
  decide +kernel

omit [Finite G] in
theorem fixed_mem_of_isL24Section {K X Y : Subgroup G} (h : IsL24Section K X Y) {k : G}
    (hk : k ∈ K) (hk3 : k ^ 3 = 1) (hkO : k ∉ pCoreOf 2 K) {w : G} (hw : w ∈ X)
    (hkw : k * w * k⁻¹ * w⁻¹ ∈ Y) : w ∈ Y := by
  obtain ⟨hKX, π, β, -, hπk, -, hβk, hβe⟩ := h
  have hπ3 : π ⟨k, hk⟩ ^ 3 = 1 := by
    rw [← map_pow]
    have e : (⟨k, hk⟩ : ↥K) ^ 3 = 1 := Subtype.ext (by simpa using hk3)
    rw [e, map_one]
  have hπ1 : π ⟨k, hk⟩ ≠ 1 := fun h1 => by
    have h2 : (⟨k, hk⟩ : ↥K) ∈ π.ker := h1
    rw [hπk, Subgroup.mem_subgroupOf] at h2
    exact hkO h2
  have hkwX : k * w * k⁻¹ ∈ X := (Subgroup.mem_normalizer_iff.mp (hKX hk) w).mp hw
  have h1 := hβe ⟨k, hk⟩ ⟨w, hw⟩ ⟨_, hkwX⟩ rfl
  have h2 : β (⟨_, hkwX⟩ * (⟨w, hw⟩ : ↥X)⁻¹) = 1 := by
    rw [← MonoidHom.mem_ker, hβk, Subgroup.mem_subgroupOf]
    simpa using hkw
  rw [map_mul, map_inv, h1, mul_inv_eq_one] at h2
  have hfix : ((π ⟨k, hk⟩ : SL(2, F4)) : Matrix (Fin 2) (Fin 2) F4).mulVec
      (Multiplicative.toAdd (β ⟨w, hw⟩)) = Multiplicative.toAdd (β ⟨w, hw⟩) := by
    have := congrArg Multiplicative.toAdd h2
    rwa [toAdd_ofAdd] at this
  have h3 := sl24_order_three _ hπ3 hπ1 (Multiplicative.toAdd (β ⟨w, hw⟩))
  rw [hfix, hfix, f4_three] at h3
  have h4 : β ⟨w, hw⟩ = 1 := by
    apply Multiplicative.toAdd.injective
    rw [h3, toAdd_one]
  rw [← MonoidHom.mem_ker, hβk, Subgroup.mem_subgroupOf] at h4
  exact h4

theorem not_dvd_card_of_isPGroup_two {P : Subgroup G} (hP : IsPGroup 2 ↥P) {p : ℕ}
    (hp : p.Prime) (hp2 : p ≠ 2) : ¬ p ∣ Nat.card ↥P := by
  obtain ⟨n, hn⟩ := hP.exists_card_eq
  rw [hn]
  intro h
  exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp (hp.dvd_of_dvd_pow h))

theorem eq_four_of_dvd_sixteen {r : ℕ} (hr : r ∣ 16) (h3 : r ≡ 1 [MOD 3]) (h1 : r ≠ 1)
    (h16 : r ≠ 16) : r = 4 := by
  have : r ∈ Nat.divisors 16 := Nat.mem_divisors.mpr ⟨hr, by norm_num⟩
  rw [show Nat.divisors 16 = {1, 2, 4, 8, 16} by decide] at this
  unfold Nat.ModEq at h3
  simp only [Finset.mem_insert, Finset.mem_singleton] at this
  omega

theorem le_four_of_dvd_sixteen {r : ℕ} (hr : r ∣ 16) (h3 : r ≡ 1 [MOD 3]) (h16 : r ≠ 16) :
    r ≤ 4 := by
  have : r ∈ Nat.divisors 16 := Nat.mem_divisors.mpr ⟨hr, by norm_num⟩
  rw [show Nat.divisors 16 = {1, 2, 4, 8, 16} by decide] at this
  unfold Nat.ModEq at h3
  simp only [Finset.mem_insert, Finset.mem_singleton] at this
  omega

omit [Finite G] in
theorem relIndex_modEq_one_of_card {p : ℕ} (hp : p.Prime) {D₁ D₂ : Subgroup G} (h12 : D₁ ≤ D₂)
    (hc : Nat.card ↥D₂ ≡ Nat.card ↥D₁ [MOD p]) (hp1 : ¬ p ∣ Nat.card ↥D₁) :
    D₁.relIndex D₂ ≡ 1 [MOD p] := by
  have h4 := Subgroup.relIndex_mul_card D₁ D₂
  rw [inf_eq_left.mpr h12] at h4
  rw [← h4, show Nat.card ↥D₁ = 1 * Nat.card ↥D₁ from (one_mul _).symm] at hc
  have hcop : Nat.Coprime p (Nat.card ↥D₁) := (Nat.Prime.coprime_iff_not_dvd hp).mpr hp1
  exact Nat.ModEq.cancel_right_of_coprime hcop (by simpa using hc)

end CFSG.Quasithin.H13.L32A
