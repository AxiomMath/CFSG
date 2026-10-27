module

public import CFSG.Quasithin.Background.A3StructureDefs

public section

namespace CFSG.Quasithin.R3c2

theorem pRank_three_range_eq {X Y : Type*} [Group X] [Finite X] [Group Y] (ψ : X →* Y)
    [Finite ψ.range] (hk : ¬ 3 ∣ Nat.card ψ.ker) :
    CFSG.Open.pRank 3 (⊤ : Subgroup ψ.range) = CFSG.Open.pRank 3 (⊤ : Subgroup X) := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  rw [← CFSG.SectionRank.pRank_quotient_eq ψ.ker hk]
  exact (CFSG.SectionRank.pRank_top_eq_of_mulEquiv (p := 3) (by norm_num)
    (QuotientGroup.quotientKerEquivRange ψ)).symm

theorem exists_orderOf_three_lift {X Y : Type*} [Group X] [Finite X] [Group Y] (ψ : X →* Y)
    (hk : ∀ x ∈ ψ.ker, orderOf x ≠ 3) {y : Y} (hy : y ∈ ψ.range) (hy3 : orderOf y = 3) :
    ∃ x : X, ψ x = y ∧ orderOf x = 3 := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨x₀, rfl⟩ := hy
  set m := orderOf x₀ with hm
  have hm0 : m ≠ 0 := (orderOf_pos x₀).ne'
  have h3m : 3 ∣ m := by
    rw [← hy3]
    exact orderOf_map_dvd ψ x₀
  obtain ⟨a, b, hb, hab⟩ := Nat.exists_eq_pow_mul_and_not_dvd hm0 3 (by norm_num)
  have hb0 : b ≠ 0 := by
    rintro rfl
    simp at hab
    exact hm0 hab
  set x₁ := x₀ ^ b with hx₁
  have hbm : b ∣ m := by rw [hab]; exact Dvd.intro_left _ rfl
  have hox₁ : orderOf x₁ = 3 ^ a := by
    rw [hx₁, orderOf_pow_of_dvd hb0 hbm, ← hm, hab, Nat.mul_div_cancel _ (Nat.pos_of_ne_zero hb0)]
  have hcop : Nat.Coprime (orderOf (ψ x₀)) b := by
    rw [hy3]
    exact (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).2 hb
  have hψx₁ : orderOf (ψ x₁) = 3 := by
    rw [hx₁, map_pow, Nat.Coprime.orderOf_pow hcop, hy3]
  have ha1 : 1 ≤ a := by
    by_contra ha
    have : a = 0 := by omega
    rw [this, pow_zero] at hox₁
    have := orderOf_map_dvd ψ x₁
    rw [hψx₁, hox₁] at this
    omega
  have ha : a = 1 := by
    by_contra ha
    have ha2 : 2 ≤ a := by omega
    have hker : x₁ ^ 3 ∈ ψ.ker := by
      rw [MonoidHom.mem_ker, map_pow, ← hψx₁]
      exact pow_orderOf_eq_one _
    have hpos : 0 < 3 := by norm_num
    have hord : orderOf (x₁ ^ 3) = 3 ^ (a - 1) := by
      rw [orderOf_pow_of_dvd (by norm_num) (by rw [hox₁]; exact dvd_pow_self 3 (by omega)), hox₁]
      rw [show 3 ^ a = 3 ^ (a - 1) * 3 by rw [← pow_succ]; congr 1; omega]
      exact Nat.mul_div_cancel _ hpos
    have hord2 : orderOf ((x₁ ^ 3) ^ 3 ^ (a - 2)) = 3 := by
      rw [orderOf_pow_of_dvd (by positivity) (by rw [hord]; exact pow_dvd_pow 3 (by omega)), hord]
      rw [show 3 ^ (a - 1) = 3 ^ (a - 2) * 3 by rw [← pow_succ]; congr 1; omega]
      exact Nat.mul_div_cancel_left _ (by positivity)
    exact hk _ (Subgroup.pow_mem _ hker _) hord2
  subst ha
  rw [pow_one] at hox₁
  have hbb : (b * b) % 3 = 1 := by
    have : b % 3 = 1 ∨ b % 3 = 2 := by omega
    rcases this with h | h <;> simp [Nat.mul_mod, h]
  refine ⟨x₁ ^ b, ?_, ?_⟩
  · rw [hx₁, ← pow_mul, map_pow, ← pow_mod_orderOf, hy3, hbb, pow_one]
  · rw [Nat.Coprime.orderOf_pow (by rw [hox₁]; exact (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).2 hb),
      hox₁]

theorem perm_three_cases : ∀ σ τ : Equiv.Perm (Fin 3), σ ^ 3 = 1 → τ ^ 3 = 1 → τ ≠ 1 →
    σ = 1 ∨ σ = τ ∨ σ = τ ^ 2 := by decide

theorem eq_one_of_cube_of_perm_three {F Q : Type*} [Group F] [Group Q] (ψ : F →* Q)
    (φ : F →* Equiv.Perm (Fin 3)) (hker : ∀ f : F, φ f = 1 → ∃ k : ℕ, f ^ 2 ^ k = 1)
    {x : F} (hx3 : x ^ 3 = 1) (hψx : ψ x = 1) (hφx : φ x ≠ 1) {y : F} (hy3 : y ^ 3 = 1) :
    ψ y = 1 := by
  have hφx3 : φ x ^ 3 = 1 := by rw [← map_pow, hx3, map_one]
  have hφy3 : φ y ^ 3 = 1 := by rw [← map_pow, hy3, map_one]
  obtain ⟨n, hn, hψn⟩ : ∃ n : F, φ n = φ y ∧ ψ n = 1 := by
    rcases perm_three_cases _ _ hφy3 hφx3 hφx with h | h | h
    · exact ⟨1, by rw [map_one, h], by simp⟩
    · exact ⟨x, h.symm, hψx⟩
    · refine ⟨x ^ 2, by rw [map_pow, h], ?_⟩
      rw [map_pow, hψx, one_pow]
  obtain ⟨k, hk⟩ := hker (y * n⁻¹) (by rw [map_mul, map_inv, hn, mul_inv_cancel])
  have h1 : ψ (y * n⁻¹) = ψ y := by
    rw [map_mul, map_inv, hψn, inv_one, mul_one]
  have h2 : (ψ y) ^ 2 ^ k = 1 := by
    rw [← h1, ← map_pow, hk, map_one]
  have h3 : (ψ y) ^ 3 = 1 := by
    rw [← map_pow, hy3, map_one]
  have hd1 : orderOf (ψ y) ∣ 3 := orderOf_dvd_of_pow_eq_one h3
  have hd2 : orderOf (ψ y) ∣ 2 ^ k := orderOf_dvd_of_pow_eq_one h2
  have hcop : Nat.Coprime 3 (2 ^ k) := Nat.Coprime.pow_right _ (by norm_num)
  have := Nat.Coprime.eq_one_of_dvd (Nat.Coprime.coprime_dvd_left hd1 hcop) hd2
  exact orderOf_eq_one_iff.1 this

variable {G : Type} [Group G]

theorem map_thetaOf_top (H : Subgroup G) :
    (CFSG.Quasithin.thetaOf (⊤ : Subgroup ↥H)).map H.subtype = CFSG.Quasithin.thetaOf H := by
  rw [CFSG.Quasithin.thetaOf, CFSG.Quasithin.thetaOf, MonoidHom.map_closure]
  congr 1
  ext x
  constructor
  · rintro ⟨y, ⟨-, hy⟩, rfl⟩
    exact ⟨y.2, by rw [Subgroup.coe_subtype, Subgroup.orderOf_coe, hy]⟩
  · rintro ⟨hx, hk⟩
    exact ⟨⟨x, hx⟩, ⟨trivial, by rw [← Subgroup.orderOf_coe]; exact hk⟩, rfl⟩

end CFSG.Quasithin.R3c2
