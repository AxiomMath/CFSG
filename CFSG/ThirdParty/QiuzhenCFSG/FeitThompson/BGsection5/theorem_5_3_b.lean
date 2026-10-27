module

public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.BGsection5.theorem_5_3_a

namespace CFSG
end CFSG
open CFSG

/-! # Theorem 5.3(b) from BG Section 5 -/

public theorem CFSG.theorem_5_3_b
    {p : ℕ} [Fact p.Prime] (hpodd : p ≠ 2)
    {R : Type*} [Group R] [Finite R] (hnarrow : IsNarrowPGroup p R) (hR : 3 ≤ groupRank R) :
    Nat.card (Ω₁Z p R) = p ∧ Ω₁Z₂ p R ∈ elementaryAbelianSubgroupsOfRank p 2 R := by
  obtain ⟨E, hE, hEmax⟩ :=
    (theorem_5_3 (p := p) hpodd (R := R) hnarrow.1 hR).mp hnarrow
  exact lemma_5_2_b (p := p) hpodd (R := R) hnarrow.1 hR hE hEmax
