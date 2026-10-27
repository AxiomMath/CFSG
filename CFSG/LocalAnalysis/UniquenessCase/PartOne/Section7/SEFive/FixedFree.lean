module

public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section7.SEFive.Defs
import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section7.SEFive.CoverLift
import CFSG.LinearAlgebra.CoprimeActions.FixedFreePowersDimension

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartOne.Section7.SEFive

theorem coverActsTriviallyOnSmall_of_fixedFreeFive {p q : ℕ} [Fact q.Prime] (hq : q = 2 ∨ q = p)
    {L : Type*} [Group L] [IsSimpleGroup L] (h : FixedFreeFive q L) :
    CoverActsTriviallyOnSmall p L := by
  intro J _ _ hJ φ hφ hcop hsol ℓ hℓ hℓ2 hℓp V _ _ hVcomm hVpow hVcard ρ
  rcases ker_le_or_eq_one hJ φ hφ hsol ρ with hker | hρ
  · exfalso
    obtain ⟨S, hSq, hS1, hScomm, t, ht, hfree⟩ := h
    have hq2p : q ∣ 2 * p := by rcases hq with rfl | rfl <;> simp
    have hqk : Nat.Coprime q (Nat.card φ.ker) := (Nat.Coprime.coprime_dvd_right hq2p hcop).symm
    obtain ⟨S', t', hS'q, hS'map, hinj, ht', rfl⟩ := exists_lift φ hφ hqk hSq ht
    have hmem : ∀ s ∈ S', φ s ∈ S := fun s hs => hS'map ▸ Subgroup.mem_map_of_mem φ hs
    have hone : ∀ s ∈ S', φ s = 1 → s = 1 := fun s hs h1 =>
      hinj hs S'.one_mem (by rw [h1, map_one])
    have hS'1 : S' ≠ ⊥ := by
      rintro rfl
      exact hS1 (by rw [← hS'map, Subgroup.map_bot])
    have hS'comm : ∀ a ∈ S', ∀ b ∈ S', a * b = b * a := fun a ha b hb =>
      hinj (S'.mul_mem ha hb) (S'.mul_mem hb ha) (by
        rw [map_mul, map_mul]
        exact hScomm _ (hmem a ha) _ (hmem b hb))
    have hcopℓ : Nat.Coprime (Nat.card S') ℓ := by
      obtain ⟨k, hk⟩ := hS'q.exists_card_eq
      rw [hk]
      refine Nat.Coprime.pow_left k ((Nat.coprime_primes Fact.out hℓ).mpr ?_)
      rcases hq with rfl | rfl
      · exact fun h => hℓ2 h.symm
      · exact fun h => hℓp h.symm
    have hfaith : ∀ s ∈ S', ρ s = 1 → s = 1 := fun s hs h1 =>
      hone s hs (hker (MonoidHom.mem_ker.mpr h1))
    have hfree' : ∀ k : ℕ, 0 < k → k < 5 → ∀ s ∈ S', t' ^ k * s * (t' ^ k)⁻¹ = s → s = 1 := by
      intro k hk0 hk5 s hs hfix
      refine hone s hs (hfree k hk0 hk5 (φ s) (hmem s hs) ?_)
      simpa only [map_mul, map_inv, map_pow] using congrArg φ hfix
    have hle := CFSG.LinearAlgebra.CoprimeActions.FixedFreePowersDimension.pow_le_card_of_fixedFree
      hℓ hVcomm hVpow ρ S' hS'1 hS'comm hcopℓ hfaith t' ht' 5 hfree'
    have hlt : ℓ ^ 4 < ℓ ^ 5 := Nat.pow_lt_pow_right hℓ.one_lt (by norm_num)
    omega
  · exact hρ

end CFSG.LocalAnalysis.UniquenessCase.PartOne.Section7.SEFive
