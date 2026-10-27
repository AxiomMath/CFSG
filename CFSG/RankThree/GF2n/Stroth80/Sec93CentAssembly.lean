module

public import CFSG.RankThree.GF2n.Stroth80.Sec93CentBender
public import CFSG.RankThree.GF2n.Stroth80.Sec93CentLinear
public import CFSG.RankThree.GF2n.Stroth80.Sec93CentOneClass
public import CFSG.RankThree.GF2n.Stroth80.Sec93CentM24
public import CFSG.RankThree.GF2n.Stroth80.Sec93FinalListFacts

public section

namespace CFSG.RankThree.GF2n.Stroth80

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open

@[expose] def MathieuCentralizerInvolutionsStatement : Prop :=
  ∀ (S : Type) [Group S] [Finite S],
    (CFSG.Blueprint.NativeSporadic.IsSporadic S .M22 ∨
      CFSG.Blueprint.NativeSporadic.IsSporadic S .M23 ∨
      CFSG.Blueprint.NativeSporadic.IsSporadic S .M24) →
    ∀ T : Subgroup S, 4 ≤ Nat.card T → CorBHyp T →
      ∀ x ∈ Subgroup.centralizer (T : Set S), x * x = 1 → x ∈ T

theorem mathieuCentralizerInvolutions_holds
    : MathieuCentralizerInvolutionsStatement := by
  intro S _ _ hS T h4 hT x hx hx2
  have hWC : IsWC T := isWC_of_corBHyp hT
  have hT1 : T ≠ ⊥ := ne_bot_of_four_le_card h4
  rcases hS with h22 | h23 | h24
  · exact mem_of_mul_self_eq_one_m22 h22 hWC hT1 hx hx2
  · exact mem_of_mul_self_eq_one_m23 h23 hWC hT1 hx hx2
  · exact mem_of_mul_self_eq_one_m24 h24 hWC h4 hx hx2

theorem listCentralizerInvolutions_of_mathieu
    (hM : MathieuCentralizerInvolutionsStatement) : ListCentralizerInvolutionsStatement := by
  intro S _ _ hS T h4 hT x hx hx2
  have hWC : IsWC T := isWC_of_corBHyp hT
  have hT1 : T ≠ ⊥ := ne_bot_of_four_le_card h4
  rcases hS with ⟨m, s, hm, hs, hmod⟩ | ⟨s, hs, hmod⟩ | ⟨s, hs, hs3, hmod⟩ |
    ⟨k, hk6, hk9, ⟨e⟩⟩ | h22 | h23 | h24
  · rcases (show m = 2 ∨ 3 ≤ m by omega) with rfl | hm3
    · exact mem_of_mul_self_eq_one_psl2 hmod hWC hT1 hx hx2
    · obtain ⟨-, K, _, _, hK, ⟨e⟩⟩ := hmod
      haveI : CharP K 2 := charP_two_of_card hK
      exact centralizer_le_of_psl hm3 e hWC hT1 hx
  · exact mem_of_mul_self_eq_one_psu3 hs hmod hWC hT1 hx hx2
  · exact mem_of_mul_self_eq_one_sz hmod hWC hT1 hx hx2
  · rcases (show k ≤ 7 ∨ k = 8 ∨ k = 9 by omega) with hk7 | rfl | rfl
    · exact mem_of_mul_self_eq_one_alt67 hk6 hk7 e hT.1 h4 hx hx2
    · exact centralizer_le_of_alt_eight e hWC hT1 hx
    · exact mem_of_mul_self_eq_one_alt_nine e hWC hT1 hx hx2
  · exact hM S (Or.inl h22) T h4 hT x hx hx2
  · exact hM S (Or.inr (Or.inl h23)) T h4 hT x hx hx2
  · exact hM S (Or.inr (Or.inr h24)) T h4 hT x hx hx2

theorem listCentralizerInvolutions_holds
    : ListCentralizerInvolutionsStatement :=
  listCentralizerInvolutions_of_mathieu mathieuCentralizerInvolutions_holds

end CFSG.RankThree.GF2n.Stroth80
