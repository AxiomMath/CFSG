module

public import CFSG.LocalAnalysis.WeakClosure81.GF2Reps135C2FinLinearLabel

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.HardMathSupport.Meierfrankenfeld.PSUScalar

theorem sub_two_le_finrank_range_sub_one {K : Type} [Field K] [Fintype K] [CharP K 2]
    (hK : Fintype.card K = 2) {n : ℕ} (hn : 6 ≤ n) {W : Type} [AddCommGroup W]
    [Module (ZMod 2) W] [Finite W]
    (ρ : Representation (ZMod 2) (Matrix.SpecialLinearGroup (Fin n) K) W)
    (hirr : ρ.IsIrreducible) (hne : ∃ x, ρ x ≠ 1) (hnat : Nat.card W ≠ 2 ^ n)
    {y : Matrix.SpecialLinearGroup (Fin n) K} (hy : y * y = 1) (hy1 : y ≠ 1) :
    n - 2 ≤ Module.finrank (ZMod 2) (LinearMap.range (ρ y - 1)) := by
  obtain ⟨S, h0, hS, -, hnatS, hmoved, -⟩ :=
    exists_label_of_irreducible_specialLinear hK (by omega) ρ hirr hne
  have hnon : ¬ (S = {⟨1, by omega⟩} ∨ S = {⟨n - 1, by omega⟩}) := fun h => hnat (hnatS h)
  have h1 := two_mul_pred_le_movedOrbit_of_nonnatural (n := n) (S := S) (by omega) (by omega)
    h0 hS hnon
  have h2 := hmoved y hy hy1
  omega

end CFSG.LocalAnalysis.WeakClosure81
