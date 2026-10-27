module

public import CFSG.Quasithin.Vol2.Ch5Sec2LocalLem528SKG
public import CFSG.Permutation.AlternatingAutomorphism.Conjugation

public section

namespace CFSG.Quasithin.H13.KGAutA7

open Equiv Equiv.Perm Subgroup

theorem not_sixty_dvd_card_centralizer {τ : Perm (Fin 7)} (hτ : orderOf τ = 3) :
    ¬ 60 ∣ Nat.card (centralizer ({τ} : Set (Perm (Fin 7)))) := by
  have h3 : ∀ n ∈ τ.cycleType, n = 3 := by
    intro n hn
    have h1 := dvd_of_mem_cycleType hn
    rw [hτ] at h1
    have h2 := two_le_of_mem_cycleType hn
    have h4 := Nat.le_of_dvd (by norm_num) h1
    interval_cases n
    · norm_num at h1
    · rfl
  have hrep : τ.cycleType = Multiset.replicate (Multiset.card τ.cycleType) 3 :=
    Multiset.eq_replicate_card.mpr h3
  have hsum := sum_cycleType_le τ
  rw [hrep, Multiset.sum_replicate, Fintype.card_fin, smul_eq_mul] at hsum
  have hne : τ ≠ 1 := by
    rintro rfl
    simp at hτ
  have hk : Multiset.card τ.cycleType ≠ 0 := fun h => hne (card_cycleType_eq_zero.mp h)
  rw [nat_card_centralizer, hrep]
  have : Multiset.card τ.cycleType = 1 ∨ Multiset.card τ.cycleType = 2 := by omega
  rcases this with h | h <;> rw [h] <;> decide

theorem autA7Fact_holds : CFSG.Quasithin.H13.AutA7Fact := by
  intro φ hφ3 H hH hfix
  obtain ⟨σ, hσ⟩ := CFSG.AlternatingAutomorphism.exists_perm_conj_of_degree_eq_five_or_seven_le
    (n := 7) (Or.inr le_rfl) φ
  have hφ : φ = MulAut.conjNormal σ :=
    MulEquiv.ext fun g => Subtype.ext (by rw [hσ g, MulAut.conjNormal_apply])
  have hcomm : ∀ h ∈ H, Commute σ (h : Perm (Fin 7)) := by
    intro h hh
    have h1 := hσ h
    rw [hfix h hh] at h1
    show σ * (h : Perm (Fin 7)) = h * σ
    calc σ * (h : Perm (Fin 7)) = (σ * h * σ⁻¹) * σ := by group
      _ = h * σ := by rw [← h1]
  have h3 : ¬ 3 ∣ orderOf σ := by
    intro h3
    have hτ := orderOf_pow_orderOf_div (orderOf_pos σ).ne' h3
    apply not_sixty_dvd_card_centralizer hτ
    rw [← hH]
    have hle : H.map (alternatingGroup (Fin 7)).subtype ≤
        centralizer ({σ ^ (orderOf σ / 3)} : Set (Perm (Fin 7))) := by
      rintro _ ⟨h, hh, rfl⟩
      rw [Subgroup.mem_centralizer_singleton_iff]
      exact ((hcomm h hh).pow_left _).eq.symm
    have := Subgroup.card_dvd_of_le hle
    rwa [Subgroup.card_map_of_injective (alternatingGroup (Fin 7)).subtype_injective] at this
  have hcop : Nat.Coprime 3 (orderOf σ) :=
    (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mpr h3
  have hdvd : orderOf φ ∣ orderOf σ := hφ ▸ orderOf_map_dvd MulAut.conjNormal σ
  exact orderOf_eq_one_iff.mp
    (Nat.eq_one_of_dvd_coprimes hcop (orderOf_dvd_of_pow_eq_one hφ3) hdvd)

end CFSG.Quasithin.H13.KGAutA7
