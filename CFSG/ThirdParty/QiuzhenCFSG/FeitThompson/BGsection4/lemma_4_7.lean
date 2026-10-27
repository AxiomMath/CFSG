module

public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.BGsection4.gorenstein_5_4_15

namespace CFSG
end CFSG
open CFSG

/-! # Lemma 4.7 from BG Section 4 -/

section Main

open scoped FixedPoints
public theorem CFSG.lemma_4_7 {R : Type*} [Group R] [Finite R] {p : Nat} [Fact p.Prime]
    (hpodd : p ≠ 2) :
    IsPGroup p R -> (selfCentralizingAbelianSubgroupsAtLeast R 3 = ∅ ↔ groupRank R ≤ 2) := by
  intro hRp
  constructor
  · intro hA3
    exact (gorenstein_theorem_5_4_15 (R := R) (p := p) hpodd hRp hA3).1
  · intro hrank
    exact selfCentralizingAbelianSubgroupsAtLeast_eq_empty_of_groupRank_le_two
      (R := R) (p := p) hRp hrank


end Main
