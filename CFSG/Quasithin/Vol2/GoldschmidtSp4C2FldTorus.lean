module

public import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.L2_5_7FinSp4
public import CFSG.Quasithin.Vol2.Ch3E213MP6BD
public import CFSG.Quasithin.Vol2.Ch3E213MP6BE

public section

namespace CFSG.Quasithin.Ch3E213M.Sp4C2

open CFSG.ComponentClassification.UnbalancedCatalog.SpChain (antiSp uElt antiUnipotentCenter)
open CFSG.QuasithinUnique.Fin257.Sp4 (dSp dSp_conj_uElt dSp_mem_normalizer)
open CFSG.Quasithin.SteinbergBS (upper_of_mem_normalizer)

theorem exists_dSp_of_coset {k : Type} [Field k] [CharP k 2] [Finite k]
    {W : Subgroup (antiSp k)} (hWZ : W ≤ antiUnipotentCenter k) (F₀ : Subfield k) (a : ℕ)
    {κ β₀ : k} (hκ : κ ≠ 0) (hβ₀ : β₀ ≠ 0)
    (hW : ∀ b c : k, uElt 0 b c 0 ∈ W →
      (∃ f ∈ F₀, b = β₀ * f) ∧ c = κ * b ^ 2 ^ (a + 1)) :
    ∃ d : antiSp k, IsUpper d ∧ W ≤ (szCentre F₀ a).map (MulAut.conj d).toMonoidHom := by
  have hsq : ∀ y : k, ∃ x : k, x ^ 2 = y := by
    have hinj : Function.Injective (fun x : k => x ^ 2) := fun x y h =>
      P6B.eq_of_pow_two_pow_eq (r := 1) (by simpa using h)
    exact fun y => Finite.injective_iff_surjective.mp hinj y
  obtain ⟨s, hs⟩ := hsq (κ * β₀ ^ 2 ^ (a + 1))
  have hs0 : s ≠ 0 := by
    intro h0
    apply mul_ne_zero hκ (pow_ne_zero (2 ^ (a + 1)) hβ₀)
    rw [← hs, h0]
    norm_num
  have ht0 : β₀ / s ≠ 0 := div_ne_zero hβ₀ hs0
  refine ⟨dSp (Units.mk0 s hs0) (Units.mk0 (β₀ / s) ht0),
    upper_of_mem_normalizer (dSp_mem_normalizer _ _), ?_⟩
  intro w hw
  obtain ⟨b, c, rfl⟩ := hWZ hw
  obtain ⟨⟨f, hf, hbf⟩, hc⟩ := hW b c hw
  refine ⟨uElt 0 f (f ^ 2 ^ (a + 1)) 0, ⟨f, hf, rfl⟩, ?_⟩
  show dSp (Units.mk0 s hs0) (Units.mk0 (β₀ / s) ht0) * uElt 0 f (f ^ 2 ^ (a + 1)) 0 *
    (dSp (Units.mk0 s hs0) (Units.mk0 (β₀ / s) ht0))⁻¹ = uElt 0 b c 0
  rw [dSp_conj_uElt]
  simp only [Units.val_mk0, mul_zero]
  congr 1
  · rw [hbf]
    field_simp
  · rw [hc, hbf, mul_pow, ← mul_assoc, ← hs]
