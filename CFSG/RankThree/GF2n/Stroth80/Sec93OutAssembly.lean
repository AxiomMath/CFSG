module

public import CFSG.RankThree.GF2n.Stroth80.Sec93OutBender
public import CFSG.RankThree.GF2n.Stroth80.Sec93OutLinear
public import CFSG.RankThree.GF2n.Stroth80.Sec93OutSmall
public import CFSG.RankThree.GF2n.Stroth80.Sec93FinalListFacts

public section

namespace CFSG.RankThree.GF2n.Stroth80

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open
open CFSG.ComponentClassification.OuterAutomorphisms (Outer)

@[expose] def OutBoundMathieuStatement : Prop :=
  ∀ (S : Type) [Group S] [Finite S],
    (CFSG.Blueprint.NativeSporadic.IsSporadic S .M22 ∨
      CFSG.Blueprint.NativeSporadic.IsSporadic S .M23 ∨
      CFSG.Blueprint.NativeSporadic.IsSporadic S .M24) →
    ∀ A : Subgroup (Outer S), IsElemAbelian 2 A → Nat.card A ≤ 4

theorem outBoundMathieu_holds
    : OutBoundMathieuStatement := by
  intro S _ _ hS A hA
  rcases hS with h22 | h23 | h24
  · obtain ⟨e⟩ := h22
    exact listOutBound_m22 e A
  · obtain ⟨e⟩ := h23
    exact listOutBound_m23 e A
  · obtain ⟨e⟩ := h24
    exact listOutBound_m24 e A

theorem listOutElemAbelianBound_of_mathieu
    (hM : OutBoundMathieuStatement) : ListOutElemAbelianBoundStatement := by
  intro S _ _ hS A hA
  rcases hS with ⟨m, s, hm, hs, hmod⟩ | ⟨s, hs, hmod⟩ | ⟨s, hs, hs3, hmod⟩ |
    ⟨k, hk6, hk9, ⟨e⟩⟩ | h22 | h23 | h24
  · rcases (show m = 2 ∨ 3 ≤ m by omega) with rfl | hm3
    · exact listOutBound_psl2 hmod A hA
    · obtain ⟨-, K, _, _, hK, ⟨e⟩⟩ := hmod
      exact card_elemAbelian_outer_le_four_of_psl hm3 K hK e A hA
  · exact listOutBound_psu3 hs hmod A hA
  · exact listOutBound_sz hmod A hA
  · exact listOutBound_alt hk6 hk9 e A
  · exact hM S (Or.inl h22) A hA
  · exact hM S (Or.inr (Or.inl h23)) A hA
  · exact hM S (Or.inr (Or.inr h24)) A hA

theorem listOutElemAbelianBound_holds
    : ListOutElemAbelianBoundStatement :=
  listOutElemAbelianBound_of_mathieu outBoundMathieu_holds

end CFSG.RankThree.GF2n.Stroth80
