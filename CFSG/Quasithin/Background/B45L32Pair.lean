module

public import CFSG.Quasithin.Background.B45L32Field
import CFSG.Quasithin.Background.SmithD37Card
import CFSG.LinearAlgebra.CharTwoOrderFour
import CFSG.GroupTheory.SylowIntersectionControl.AltCore.GLSquares

public section

namespace CFSG.Quasithin.B45L32

open CFSG.QuasithinUnique.Setup.Family

theorem exists_card_eq_two_pow_of_pair {U : Type} [CommGroup U] [Finite U] [Nontrivial U]
    (hU : ∀ u : U, u ^ 2 = 1) {L₁ L₂ : Subgroup (MulAut U)} (e₁ : ↥L₁ ≃* GL32)
    (e₂ : ↥L₂ ≃* GL32) (hcomm : ∀ x ∈ L₁, ∀ y ∈ L₂, x * y = y * x)
    (hirr : ∀ J : Subgroup U, (∀ g ∈ L₁ ⊔ L₂, ∀ u ∈ J, g u ∈ J) → J = ⊥ ∨ J = ⊤) :
    ∃ n : ℕ, Nat.card U = 2 ^ n ∧ 9 ≤ n ∧ (n ≤ 16 → n = 9) := by
  classical
  obtain ⟨F, hFld, hFin, hCharP, V₀, V₁, hAdd₀, hAdd₁, hMod₀, hMod₁, hFD₀, hFD₁, ρ₀, ρ₁,
    hnt₀, hnt₁, hinj₀, hinj₁, hirr₀, hirr₁, hcard⟩ :=
    CFSG.Quasithin.SmithD37.exists_tensor_card hU hcomm hirr
  obtain ⟨g, hg2, hg4⟩ :=
    CFSG.GroupTheory.AltCore.exists_sq_ne_one_pow_four_eq_one_GL_two (e := 3) (by norm_num)
  have hg : orderOf g = 4 := by
    have h := orderOf_eq_prime_pow (p := 2) (n := 1) (x := g) (by simpa using hg2)
      (by simpa using hg4)
    simpa using h
  have hd₀ : 3 ≤ Module.finrank F V₀ :=
    CFSG.LinearAlgebra.three_le_finrank_of_injective_of_orderOf_eq_four hinj₀ (by
      rw [MulEquiv.orderOf_eq e₁.symm g, hg])
  have hd₁ : 3 ≤ Module.finrank F V₁ :=
    CFSG.LinearAlgebra.three_le_finrank_of_injective_of_orderOf_eq_four hinj₁ (by
      rw [MulEquiv.orderOf_eq e₂.symm g, hg])
  have : Algebra (ZMod 2) F := ZMod.algebra F 2
  have : Module.Finite (ZMod 2) F := Module.Finite.of_finite
  have hcardF : Nat.card F = 2 ^ Module.finrank (ZMod 2) F := by
    have h := Module.natCard_eq_pow_finrank (K := ZMod 2) (V := F)
    rwa [Nat.card_zmod] at h
  have hk : 1 ≤ Module.finrank (ZMod 2) F := by
    have h1 : 1 < Nat.card F := Finite.one_lt_card
    rw [hcardF] at h1
    exact Nat.pos_of_ne_zero fun h => by simp [h] at h1
  have h9 : 3 * 3 ≤ Module.finrank F V₀ * Module.finrank F V₁ := Nat.mul_le_mul hd₀ hd₁
  refine ⟨Module.finrank (ZMod 2) F * (Module.finrank F V₀ * Module.finrank F V₁),
    by rw [hcard, hcardF, ← pow_mul], h9.trans (Nat.le_mul_of_pos_left _ hk), fun hn => ?_⟩
  have hk1 : Module.finrank (ZMod 2) F = 1 := by
    by_contra hne
    have h18 := Nat.mul_le_mul (show 2 ≤ Module.finrank (ZMod 2) F by omega) h9
    omega
  have hcardF2 : Nat.card F = 2 := by rw [hcardF, hk1, pow_one]
  rcases finrank_eq_three_or_eight_of_field e₁ hcardF2 (ρ := ρ₀) hinj₀ hirr₀ with h₀ | h₀ <;>
    rcases finrank_eq_three_or_eight_of_field e₂ hcardF2 (ρ := ρ₁) hinj₁ hirr₁ with h₁ | h₁ <;>
    rw [h₀, h₁] at hn ⊢ <;> omega

end CFSG.Quasithin.B45L32
