module

public import CFSG.LocalAnalysis.WeakClosure81.GF2Reps135C2PslLabelExt

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open Matrix Module Finset
open CFSG.LieType.SpecialLinear CFSG.LieType.SpecialLinear.ExteriorModel
open CFSG.HardMathSupport.Meierfrankenfeld.PSUScalar

theorem w135c2_psl_label {m f : ℕ} (hm : 1 ≤ m) {K : Type} [Field K] [Fintype K] [CharP K 2]
    (hK : Fintype.card K = 2 ^ f) {W : Type} [AddCommGroup W] [Module (ZMod 2) W] [Finite W]
    (ρ : Representation (ZMod 2) (SpecialLinearGroup (Fin (m + 1)) K) W)
    (hirr : ρ.IsIrreducible) (hne : ∃ g, ρ g ≠ 1) :
    ∃ (s : ℕ) (ε : Fin f → Finset (Fin (m + 1))), 1 ≤ s ∧
      (∀ r, (⟨0, by omega⟩ : Fin (m + 1)) ∉ ε r) ∧ (∃ r, ε r ≠ ∅) ∧
      f ≤ s * (univ.filter fun r => ε r ≠ ∅).card ∧
      (∀ y : SpecialLinearGroup (Fin (m + 1)) K, y * y = 1 → y ≠ 1 →
        s * movedTop (by omega : 2 ≤ m + 1) ε ≤
          2 * finrank (ZMod 2) (LinearMap.range (ρ y - 1))) ∧
      (∃ (k : Type) (_ : Field k) (_ : CharP k 2),
        Nat.card W = 2 ^ (s * finrank k (BModel k ε))) ∧
      (∀ (r₀ : Fin f) (j : Fin (m + 1)), (∀ r, r ≠ r₀ → ε r = ∅) → ε r₀ = {j} →
        ∃ β : W ≃+ (Set.powersetCard (Fin (m + 1)) (j : ℕ) → K),
          ∀ g w, β (ρ g w) = extTwist (m + 1) (j : ℕ) (r₀ : ℕ) K g *ᵥ β w) := by
  obtain ⟨s, ε, hs1, -, h0, hact, hper, hrank, hcard, hdesc, -, -⟩ :=
    w135c2_psl_label_ext hm hK ρ hirr hne
  exact ⟨s, ε, hs1, h0, hact, hper, hrank, hcard, hdesc⟩

end CFSG.LocalAnalysis.WeakClosure81
