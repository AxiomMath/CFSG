module

public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.BGsection5.theorem_5_3_b

namespace CFSG
end CFSG
open CFSG

/-! # Theorem 5.3(c) from BG Section 5 -/

public theorem CFSG.theorem_5_3_c
    {p : ℕ} [Fact p.Prime] (hpodd : p ≠ 2)
    {R : Type*} [Group R] [Finite R] (hnarrow : IsNarrowPGroup p R) (hR : 3 ≤ groupRank R) :
    (CΩ₁Z₂ p R).Characteristic ∧ (CΩ₁Z₂ p R).index = p := by
  obtain ⟨E, hE, hEmax⟩ :=
    (theorem_5_3 (p := p) hpodd (R := R) hnarrow.1 hR).mp hnarrow
  exact lemma_5_2_c (p := p) hpodd (R := R) hnarrow.1 hR hE hEmax
