module

public import CFSG.LocalAnalysis.WeakClosure81.GF2Reps135C2FinLinearHasLabel

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.HardMathSupport.Meierfrankenfeld.PSUScalar CFSG.LieType.SpecialLinear

theorem exists_label_of_irreducible_specialLinear {K : Type} [Field K] [Fintype K] [CharP K 2]
    (hK : Fintype.card K = 2) {n : ℕ} (hn : 3 ≤ n) {W : Type} [AddCommGroup W]
    [Module (ZMod 2) W] [Finite W]
    (ρ : Representation (ZMod 2) (Matrix.SpecialLinearGroup (Fin n) K) W)
    (hirr : ρ.IsIrreducible) (hne : ∃ x, ρ x ≠ 1) :
    ∃ S : Finset (Fin n), (⟨0, by omega⟩ : Fin n) ∉ S ∧ S ≠ ∅ ∧
      2 ^ orbitSize S ≤ Nat.card W ∧
      ((S = {⟨1, by omega⟩} ∨ S = {⟨n - 1, by omega⟩}) → Nat.card W = 2 ^ n) ∧
      (∀ y : Matrix.SpecialLinearGroup (Fin n) K, y * y = 1 → y ≠ 1 →
        movedOrbit (by omega : 2 ≤ n) S ≤
          2 * Module.finrank (ZMod 2) (LinearMap.range (ρ y - 1))) ∧
      ((∃ (d : W ≃ₗ[ZMod 2] W) (B : Matrix.GeneralLinearGroup (Fin n) K) (τ : K ≃+* K),
          IsUpperGL B ∧ d * d = 1 ∧ ∀ (x : Matrix.SpecialLinearGroup (Fin n) K) (w : W),
            d (ρ x w) = ρ (borelStd n K B τ 1 x) (d w)) →
        ∀ (j : Fin n) (hj : 1 ≤ j.val), (j ∈ S ↔ (⟨n - j.val, by omega⟩ : Fin n) ∈ S)) := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  haveI : ρ.IsIrreducible := hirr
  obtain ⟨S, hS, h0, hne'⟩ := exists_hasLabel hK (by omega) ρ hne
  obtain ⟨hcard, hnat⟩ := card_of_hasLabel hK (by omega) ρ hS hne'
  refine ⟨S, h0, hne', hcard, ?_, ?_, ?_⟩
  · rintro (h | h)
    · exact hnat (Or.inl h)
    · exact hnat (Or.inr (by simpa using h))
  · intro y hy hy1
    exact movedOrbit_le_of_hasLabel hK (by omega) ρ hS hy hy1
  · intro hgraph j hj
    exact symmetric_of_hasLabel hK (by omega) ρ hS hgraph j hj

end CFSG.LocalAnalysis.WeakClosure81
