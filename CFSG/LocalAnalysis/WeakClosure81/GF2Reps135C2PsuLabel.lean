module

public import CFSG.LieType.SpecialLinear.ExteriorModel.Binary
public import CFSG.HardMathSupport.Meierfrankenfeld.PSUScalar.CaseAnalysis
public import CFSG.HardMathSupport.Meierfrankenfeld.PSUScalar.FieldDegree
import CFSG.LocalAnalysis.WeakClosure81.GF2Reps135C2PsuLabelExt

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open Matrix Module Finset
open CFSG.LieType.SpecialLinear.ExteriorModel
open CFSG.LieType.Universal.Unitary CFSG.LieType.BorelTits
open CFSG.HardMathSupport.Meierfrankenfeld.PSUScalar

theorem w135c2_psu_label {m f : ℕ} (hm : 3 ≤ m) {K : Type} [Field K] [Finite K] [CharP K 2]
    (hK : Nat.card K = (2 ^ f) ^ 2) {W : Type} [AddCommGroup W] [Module (ZMod 2) W] [Finite W]
    (ρ : Representation (ZMod 2) (SU (unitaryInvolution K 2 f) m) W)
    (hirr : ρ.IsIrreducible) (hne : ∃ g, ρ g ≠ 1) :
    ∃ (s : ℕ) (ε : Fin f → Finset (Fin m)), 1 ≤ s ∧
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
          β (ρ g w) = ((g : GL (Fin m) K) : Matrix (Fin m) (Fin m) K) *ᵥ β w) := by
  have hf : 0 < f := by
    rcases Nat.eq_zero_or_pos f with h | h
    · exfalso
      rw [h, pow_zero, one_pow] at hK
      have := Finite.one_lt_card (α := K)
      omega
    · exact h
  obtain ⟨s, ε, hs1, -, h0, hact, hper, hns, hrank, hcard, hdesc, -, -, -⟩ :=
    w135c2_psu_label_ext hm hf hK ρ hirr hne
  exact ⟨s, ε, hs1, h0, hact, hper, hns, hrank, hcard, hdesc⟩

end CFSG.LocalAnalysis.WeakClosure81
