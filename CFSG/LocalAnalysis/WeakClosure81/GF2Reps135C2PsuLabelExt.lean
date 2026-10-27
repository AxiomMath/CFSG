module

public import CFSG.LocalAnalysis.WeakClosure81.GF2Reps135C2PsuClauses
import CFSG.LocalAnalysis.WeakClosure81.GF2Reps135C2PsuDescent

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open Matrix Module Finset
open CFSG.LieType.SpecialLinear.ExteriorModel
open CFSG.LieType.Universal.Unitary CFSG.LieType.BorelTits
open CFSG.HardMathSupport.Meierfrankenfeld.PSUScalar
open scoped MonoidAlgebra

theorem w135c2_psu_label_ext {m f : ℕ} (hm : 3 ≤ m) (hf : 0 < f) {K : Type} [Field K]
    [Finite K] [CharP K 2] (hK : Nat.card K = (2 ^ f) ^ 2) {W : Type} [AddCommGroup W]
    [Module (ZMod 2) W] [Finite W]
    (ρ : Representation (ZMod 2) (SU (unitaryInvolution K 2 f) m) W)
    (hirr : ρ.IsIrreducible) (hne : ∃ g, ρ g ≠ 1) :
    ∃ (s : ℕ) (ε : Fin f → Finset (Fin m)), 1 ≤ s ∧
      Nat.card (Module.End (MonoidAlgebra (ZMod 2) (SU (unitaryInvolution K 2 f) m))
        ρ.asModule) = 2 ^ s ∧
      (∀ r, (⟨0, by omega⟩ : Fin m) ∉ ε r) ∧ (∃ r, ε r ≠ ∅) ∧
      f ≤ s * (univ.filter fun r => ε r ≠ ∅).card ∧
      ((univ.filter fun r => ε r ≠ ∅).card ≤ 2 → (∃ r, (ε r).image labelStar ≠ ε r) →
        2 * f ≤ s) ∧
      (∀ y : SU (unitaryInvolution K 2 f) m, y * y = 1 → y ≠ 1 →
        s * movedTop (by omega : 2 ≤ m) ε ≤
          2 * finrank (ZMod 2) (LinearMap.range (ρ y - 1))) ∧
      (∃ (k : Type) (_ : Field k) (_ : CharP k 2),
        Nat.card W = 2 ^ (s * finrank k (BModel k ε))) ∧
      (∀ (r₀ : Fin f) (j : Fin m), (∀ r, r ≠ r₀ → ε r = ∅) → ε r₀ = {j} →
        ((j : ℕ) = 1 ∨ (j : ℕ) + 1 = m) →
        ∃ β : W ≃+ (Fin m → K), ∀ (g : SU (unitaryInvolution K 2 f) m) (w : W),
          β (ρ g w) = ((g : GL (Fin m) K) : Matrix (Fin m) (Fin m) K) *ᵥ β w) ∧
      (rotEps hf)^[s] ε = ε ∧
      (∀ p : ℕ, 0 < p → p < s → (rotEps hf)^[p] ε ≠ ε) ∧
      ((∀ r, (ε r).image labelStar = ε r) → s ≤ f) := by
  classical
  haveI : ρ.IsIrreducible := hirr
  obtain ⟨s, hs0, hE⟩ := exists_card_endField_eq_two_pow (ρ := ρ)
  obtain ⟨ε, hε, ht⟩ := exists_hasUnitaryLabel (by omega : 2 ≤ m) hK ρ hne
  have h0 := w135c2_psu_zero_not_mem_of_hasUnitaryLabel (by omega : 2 ≤ m) hK ρ hε
  obtain ⟨hper, hns, hrank, hcard⟩ := w135c2_psu_clauses hm hK ρ hε hE hs0 ht
  refine ⟨s, ε, hs0, hE, h0, ht, hper, hns, hrank, hcard, ?_,
    w135c2_psu_rotate_of_hasUnitaryLabel hm hf hK ρ hε hE,
    w135c2_psu_minimal_of_hasUnitaryLabel hm hf hK ρ hε hE,
    fun hsd => w135c2_psu_le_of_selfDual hm hf hK ρ hε hE hsd⟩
  intro r₀ j hrest h₀ hj
  have hact : (univ.filter fun r => ε r ≠ ∅).card ≤ 2 := by
    have hsub : (univ.filter fun r => ε r ≠ ∅) ⊆ {r₀} := by
      intro r hr
      rw [Finset.mem_filter] at hr
      rw [Finset.mem_singleton]
      by_contra hne'
      exact hr.2 (hrest r hne')
    exact (Finset.card_le_card hsub).trans (by simp)
  have hnsd : ∃ r, (ε r).image labelStar ≠ ε r := by
    refine ⟨r₀, ?_⟩
    rw [h₀, Finset.image_singleton]
    intro h
    have hv : ((labelStar j : Fin m) : ℕ) = (j : ℕ) :=
      congrArg Fin.val (Finset.singleton_injective h)
    rw [labelStar_apply] at hv
    rcases hj with hj | hj
    · rw [hj, Nat.mod_eq_of_lt (by omega)] at hv
      omega
    · have h1 : m - (j : ℕ) = 1 := by omega
      rw [h1, Nat.mod_eq_of_lt (by omega)] at hv
      omega
  exact w135c2_psu_descent hm hK ρ hε hE (hns hact hnsd) r₀ j hrest h₀ hj

end CFSG.LocalAnalysis.WeakClosure81
