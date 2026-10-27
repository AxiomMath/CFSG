module

public import CFSG.LocalAnalysis.WeakClosure81.GF2Reps135C2PslClauses
public import CFSG.LocalAnalysis.WeakClosure81.GF2Reps135C2PslRotate
public import CFSG.LocalAnalysis.WeakClosure81.GF2Reps135C2PslMinimal
import CFSG.HardMathSupport.Meierfrankenfeld.PSUScalar.EndFieldModel

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open Matrix Module Finset
open CFSG.LieType.SpecialLinear CFSG.LieType.SpecialLinear.ExteriorModel
open CFSG.HardMathSupport.Meierfrankenfeld.PSUScalar

theorem w135c2_psl_label_ext {m f : ℕ} (hm : 1 ≤ m) {K : Type} [Field K] [Fintype K] [CharP K 2]
    (hK : Fintype.card K = 2 ^ f) {W : Type} [AddCommGroup W] [Module (ZMod 2) W] [Finite W]
    (ρ : Representation (ZMod 2) (SpecialLinearGroup (Fin (m + 1)) K) W)
    (hirr : ρ.IsIrreducible) (hne : ∃ g, ρ g ≠ 1) :
    ∃ (s : ℕ) (ε : Fin f → Finset (Fin (m + 1))), 1 ≤ s ∧
      Nat.card (Module.End (MonoidAlgebra (ZMod 2) (SpecialLinearGroup (Fin (m + 1)) K))
        ρ.asModule) = 2 ^ s ∧
      (∀ r, (⟨0, by omega⟩ : Fin (m + 1)) ∉ ε r) ∧ (∃ r, ε r ≠ ∅) ∧
      f ≤ s * (univ.filter fun r => ε r ≠ ∅).card ∧
      (∀ y : SpecialLinearGroup (Fin (m + 1)) K, y * y = 1 → y ≠ 1 →
        s * movedTop (by omega : 2 ≤ m + 1) ε ≤
          2 * finrank (ZMod 2) (LinearMap.range (ρ y - 1))) ∧
      (∃ (k : Type) (_ : Field k) (_ : CharP k 2),
        Nat.card W = 2 ^ (s * finrank k (BModel k ε))) ∧
      (∀ (r₀ : Fin f) (j : Fin (m + 1)), (∀ r, r ≠ r₀ → ε r = ∅) → ε r₀ = {j} →
        ∃ β : W ≃+ (Set.powersetCard (Fin (m + 1)) (j : ℕ) → K),
          ∀ g w, β (ρ g w) = extTwist (m + 1) (j : ℕ) (r₀ : ℕ) K g *ᵥ β w) ∧
      (∀ r : Fin f, ε ⟨(r + s) % f, Nat.mod_lt _ r.pos⟩ = ε r) ∧
      (∀ p : ℕ, 0 < p → p < s → ∃ r : Fin f, ε ⟨(r + p) % f, Nat.mod_lt _ r.pos⟩ ≠ ε r) := by
  classical
  haveI := hirr
  obtain ⟨ε, hε, hact⟩ := exists_hasTwistedLabel hK ρ hne
  obtain ⟨s, hs0, hE⟩ := exists_card_endField_eq_two_pow (ρ := ρ)
  have h0 : ∀ r, (⟨0, by omega⟩ : Fin (m + 1)) ∉ ε r := by
    obtain ⟨k, _, _, _, _, y, χ, J, h0, -⟩ := hε
    exact fun r => by simpa using h0 r
  obtain ⟨hper, hrk, hcard, hdesc⟩ := w135c2_clauses_of_hasTwistedLabel hm hK ρ hε hE hact
  exact ⟨s, ε, hs0, hE, h0, hact, hper, hrk, hcard, hdesc,
    w135c2_rotate_of_hasTwistedLabel hK ρ hε hE, w135c2_minimal_of_hasTwistedLabel hK ρ hε hE⟩

end CFSG.LocalAnalysis.WeakClosure81
