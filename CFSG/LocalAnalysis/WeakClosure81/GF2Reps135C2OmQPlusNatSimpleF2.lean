module

import CFSG.RankThree.GF2n.Stroth80.Sec41iiIrred
import CFSG.RankThree.GF2n.Stroth80.Sec78NatIrredOmega
public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.LieType.Universal.SpinOmega.Range
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.LieType.Universal.Spin
open scoped Matrix

theorem omq_omPlus_natural_addSubgroup_simple {n : ℕ} (hn : 3 ≤ n) {F : Type} [Field F]
    [Finite F] [CharP F 2] (A : AddSubgroup (Fin n ⊕ Fin n → F))
    (hA : ∀ (g : spinGroup (quadPlus n F)) (v : Fin n ⊕ Fin n → F), v ∈ A →
      (spinMatrix (quadPlus n F) g : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) F) *ᵥ v ∈ A) :
    A = ⊥ ∨ A = ⊤ := by
  by_cases h0 : A = ⊥
  · exact Or.inl h0
  · refine Or.inr (CFSG.RankThree.GF2n.Stroth80.eq_top_of_addInvariant
      (CFSG.RankThree.GF2n.Stroth80.natIrred_statedOmegaPlus hn)
      (CFSG.RankThree.GF2n.Stroth80.addCommutantScalar_statedOmegaPlus hn) h0
      fun g hg v hv => ?_)
    obtain ⟨x, rfl⟩ : g ∈ (spinMatrix (quadPlus n F)).range :=
      (range_spinMatrix_quadPlus (K := F) hn).symm ▸ hg
    exact hA x v hv

end CFSG.LocalAnalysis.WeakClosure81
