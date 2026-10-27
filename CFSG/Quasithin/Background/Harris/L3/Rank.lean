module

public import CFSG.Quasithin.Background.Harris.L3.RankLift
public import CFSG.Quasithin.Background.Harris.L3.RankTwist

public section

namespace CFSG.Quasithin.G11.Harris.L3

open scoped MatrixGroups
open Matrix CFSG.QuasithinUnique.Setup.X7a CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.LinearFlag CFSG.Quasithin.B42SL3

theorem card_le_of_sl3 {f : ℕ} (hf : 1 ≤ f) {F : Type} [Field F] [Fintype F]
    (hF : Fintype.card F = 2 ^ f) {U : Type} [AddCommGroup U] [Module (ZMod 2) U] [Finite U]
    (ρ : Representation (ZMod 2) SL(3, F) U) (hirr : ρ.IsIrreducible)
    (hker : ∀ g : SL(3, F), ρ g = 1 → g ∈ Subgroup.center SL(3, F))
    (hsd : ¬ Nonempty (ρ.Equiv ρ.dual)) (A : Subgroup (U ≃ₗ[ZMod 2] U))
    [CFSG.IsElementaryAbelian 2 A] (hA : ∀ a ∈ A, ∀ x : SL(3, F), ∃ y, Intertwines ρ a x y) :
    Nat.card A ≤ 2 ^ (2 * f) := by
  classical
  have hNat : Nat.card F = 2 ^ f := by rw [Nat.card_eq_fintype_card, hF]
  have hchar : CharP F 2 := finite_field_prime_power_characteristic Nat.prime_two hf hNat
  have hker' : ∀ x : SL(3, F), ρ x = 1 → x ∈ scalars 3 F := fun x hx => by
    rw [scalars_eq_center]
    exact hker x hx
  have hS2 : ∀ s ∈ liftGroup ρ hker' A, s * s = 1 := fun s hs => hs.1
  have hSc : ∀ s ∈ liftGroup ρ hker' A, ∀ t ∈ liftGroup ρ hker' A, s * t = t * s := by
    rintro s ⟨hs2, a, haA, ha⟩ t ⟨ht2, b, hbA, hb⟩
    exact commute_of_mem_lift ρ hker' A hs2 ht2 haA hbA ha hb
  have hinner := card_innerPart_le_card_liftGroup ρ hker' A hA hf hNat hirr
  by_cases h : ∀ a : ↥A, a ∈ innerPart ρ hker' A hA
  · have h1 : Nat.card ↥A ≤ Nat.card ↥(innerPart ρ hker' A hA) :=
      Nat.card_le_card_of_injective (fun a => (⟨a, h a⟩ : ↥(innerPart ρ hker' A hA)))
        (fun a b hab => congrArg Subtype.val hab)
    have h2 := card_le_of_involutions (liftGroup ρ hker' A) hS2 hSc
    calc Nat.card ↥A ≤ Nat.card F ^ 2 := h1.trans (hinner.trans h2)
      _ = 2 ^ (2 * f) := by rw [hNat, ← pow_mul, mul_comm]
  · push Not at h
    obtain ⟨a₀, ha₀⟩ := h
    obtain ⟨M, σ, hMσ⟩ := mem_semilinearAutGroup_iff.mp
      (mem_semilinear_of_not_selfDual ρ hker' A hA hf hF hirr hsd a₀)
    have hsq : normalizerHom ρ hker' A hA a₀ * normalizerHom ρ hker' A hA a₀ = 1 := by
      rw [← map_mul, elem_mul_self A a₀, map_one]
    have hσ1 : σ ≠ 1 := by
      intro h1
      apply ha₀
      rw [mem_innerPart, hMσ, h1, map_one, mul_one]
      refine mem_inner_of_sq_conjAut ?_
      rwa [hMσ, h1, map_one, mul_one] at hsq
    rw [hMσ, conjAut_mul_fieldAut_mul] at hsq
    obtain ⟨hσσ, c, hc⟩ := eq_one_of_conjAut_mul_fieldAut_eq_one (K := F) (n := 3) le_rfl _ _ hsq
    obtain ⟨hfe, hσpow⟩ := even_and_eq_pow_of_involution hf hNat hσ1 hσσ
    obtain ⟨k, hk⟩ := hfe
    have hk1 : 1 ≤ k := by omega
    have hfk : f / 2 = k := by omega
    have hF2 : Nat.card F = 2 ^ (2 * k) := by rw [hNat, hk]; ring_nf
    have hσ : ∀ x, σ x = x ^ 2 ^ k := fun x => by rw [hσpow, hfk]
    have hbound := card_le_of_twisted_fixed hk1 hF2 hσ M c hc.symm (liftGroup ρ hker' A) hS2 hSc
      (fun s hs => twist_fixed_of_mem_lift ρ hker' A hA hMσ hs)
    have hAle := card_le_two_mul_innerPart ρ hker' A hA hf hF hirr hsd
    calc Nat.card ↥A ≤ 2 * Nat.card ↥(innerPart ρ hker' A hA) := hAle
      _ ≤ 2 * 2 ^ (2 * k) := Nat.mul_le_mul_left 2 (hinner.trans hbound)
      _ = 2 ^ (2 * k + 1) := by rw [pow_succ]; ring
      _ ≤ 2 ^ (2 * f) := Nat.pow_le_pow_right (by norm_num) (by omega)

end CFSG.Quasithin.G11.Harris.L3
