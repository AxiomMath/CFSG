module

public import CFSG.LieType.Universal.Spin.Action
public import CFSG.LieType.Universal.Spin.Forms
import CFSG.LieType.Universal.SpinOmega.Range
import CFSG.RankThree.GF2n.Stroth80.Sec41iiIrred
import CFSG.RankThree.GF2n.Stroth80.Sec78NatIrredOmega

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.LieType.Universal.Spin
open scoped Matrix

theorem omq_omMinus_natural_addSubgroup_simple {n : ℕ} (hn : 4 ≤ n) {K : Type} [Field K] [Finite K]
    [CharP K 2] {b c : K} (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0)
    (A : AddSubgroup (Fin (n - 1) ⊕ Fin (n - 1) ⊕ Fin 2 → K))
    (hA : ∀ (g : spinGroup (quadMinus n K b c)) (v : Fin (n - 1) ⊕ Fin (n - 1) ⊕ Fin 2 → K),
      v ∈ A → (spinMatrix (quadMinus n K b c) g : Matrix (Fin (n - 1) ⊕ Fin (n - 1) ⊕ Fin 2)
        (Fin (n - 1) ⊕ Fin (n - 1) ⊕ Fin 2) K) *ᵥ v ∈ A) :
    A = ⊥ ∨ A = ⊤ := by
  by_cases h0 : A = ⊥
  · exact Or.inl h0
  · refine Or.inr (CFSG.RankThree.GF2n.Stroth80.eq_top_of_addInvariant
      (CFSG.RankThree.GF2n.Stroth80.natIrred_statedOmegaMinus_of_three_le (by omega) hirr)
      (CFSG.RankThree.GF2n.Stroth80.addCommutantScalar_statedOmegaMinus (by omega) hirr) h0
      fun g hg v hv => ?_)
    obtain ⟨x, rfl⟩ : g ∈ (spinMatrix (quadMinus n K b c)).range :=
      (range_spinMatrix_quadMinus hn hirr).symm ▸ hg
    exact hA x v hv

end CFSG.LocalAnalysis.WeakClosure81
