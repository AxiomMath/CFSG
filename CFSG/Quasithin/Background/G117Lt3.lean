module

public import CFSG.Assembly.LowTwoRankDefs
public import CFSG.Quasithin.Vol2.Ch12Sec8NonabG101Def

public section

namespace CFSG.Quasithin

namespace G11

namespace G117

theorem perm3_conj_inv : ∀ τ σ : Equiv.Perm (Fin 3), τ * τ = 1 → τ ≠ 1 → σ ^ 3 = 1 → σ ≠ 1 →
    τ * σ * τ⁻¹ = σ⁻¹ := by decide

theorem perm3_fix_sq : ∀ σ : Equiv.Perm (Fin 3), (∃ i, σ i = i) → σ * σ = 1 := by decide

theorem natCard_perm3 : Nat.card (Equiv.Perm (Fin 3)) = 6 := by
  rw [Nat.card_eq_fintype_card, Fintype.card_perm]
  decide

theorem exists_S3_perm3 : ∃ t c : Equiv.Perm (Fin 3), t * t = 1 ∧ t ≠ 1 ∧ c ^ 3 = 1 ∧ c ≠ 1 ∧
    t * c * t⁻¹ = c⁻¹ := by decide

theorem card_eq_three_of_injective {C : Type*} [Group C] [Finite C]
    (ρ : C →* Equiv.Perm (Fin 3)) (hρ : Function.Injective ρ) (h2 : 2 ≤ Nat.card C)
    (hno2 : Nat.card C ≠ 2) (hno6 : Nat.card C ≠ 6) : Nat.card C = 3 := by
  have hdvd : Nat.card C ∣ 6 := by
    have := Subgroup.card_dvd_of_injective ρ hρ
    rwa [natCard_perm3] at this
  have hle : Nat.card C ≤ 6 := Nat.le_of_dvd (by norm_num) hdvd
  generalize Nat.card C = n at *
  interval_cases n <;> simp_all

theorem exists_S3_of_card_six {C : Type*} [Group C] [Finite C]
    (ρ : C →* Equiv.Perm (Fin 3)) (hρ : Function.Injective ρ) (h6 : Nat.card C = 6) :
    ∃ t c : C, t * t = 1 ∧ t ≠ 1 ∧ c ^ 3 = 1 ∧ c ≠ 1 ∧ t * c * t⁻¹ = c⁻¹ := by
  have hbij : Function.Bijective ρ := by
    refine ⟨hρ, ?_⟩
    have : Nat.card (Equiv.Perm (Fin 3)) ≤ Nat.card C := by
      rw [natCard_perm3, h6]
    exact (Function.Injective.bijective_of_nat_card_le hρ this).2
  obtain ⟨t₀, c₀, h1, h2, h3, h4, h5⟩ := exists_S3_perm3
  obtain ⟨t, rfl⟩ := hbij.2 t₀
  obtain ⟨c, rfl⟩ := hbij.2 c₀
  refine ⟨t, c, hρ ?_, fun h => h2 (by rw [h, map_one]), hρ ?_, fun h => h4 (by rw [h, map_one]),
    hρ ?_⟩
  · rw [map_mul, map_one]
    exact h1
  · rw [map_pow, map_one]
    exact h3
  · rw [map_mul, map_mul, map_inv, map_inv]
    exact h5

end G117

end G11

end CFSG.Quasithin
