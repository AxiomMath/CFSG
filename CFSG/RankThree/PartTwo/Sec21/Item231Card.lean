module

public import CFSG.RankThree.PartTwo.Sec21.Item231Of
public import CFSG.RankThree.PartTwo.KFacts.KS21Terminal
public import CFSG.RankThree.PartTwo.Sec21.Item22DStar
public import CFSG.RankThree.PartTwo.Sec21.Item231
public import CFSG.RankThree.PartTwo.Sec21.Item23Tools

public section

namespace CFSG.RankThree.PartTwo.Sec21

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo

theorem card_eq_of_item222 (h222 : Item222) {G : Type} [Group G] [Finite G]
    {A E U : Subgroup G} {c : G} {L : Subgroup G} (hpair : Sec21Pair G A E U c L) :
    Nat.card A = 3 ^ 3 ∨ Nat.card A = 3 ^ 4 := by
  obtain ⟨-, ⟨φ, hφL, hφD⟩, hcase⟩ := h222 G A E U c L hpair
  rcases hcase φ hφL hφD with h | h | h | h | h <;> first
    | exact Or.inl h.1
    | exact Or.inr h.1

theorem item231IStar_of_item222 (h226 : Item226) (h229 : Item229) (h2130 : Item2130)
    (h222 : Item222) (hKW : KOfWellDefinedAll) (hAut : KFacts.KS21.TerminalAutomizer) :
    Item231IStar := by
  intro G _ _ A E U c L hpair
  have hK := hKW G A E U c L hpair
  have hle := closure_dStar_le_starOf_iGroup h222 hpair hK
  have hAI := le_iGroup h2130 h222 hpair hK
  have hAe' := isElemAbelian_subgroupOf hpair.mem_S.1.1 (iGroup A)
  have hcardA' : Nat.card (A.subgroupOf (iGroup A)) = Nat.card A :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hAI).toEquiv
  refine (Subgroup.eq_of_le_of_card_ge hle ?_).symm
  rcases card_eq_of_item222 h222 hpair with h27 | h81
  · rcases h229 G A E U c L hpair h27 with ⟨⟨eD⟩, ⟨eI⟩⟩ | ⟨hWD, -, -⟩
    · have hb := (hAut (iGroup A) (A.subgroupOf (iGroup A)) hAe').2 ⟨eI⟩ (hcardA'.trans h27)
      rw [Nat.card_congr eD.toEquiv, Nat.card_perm, Nat.card_eq_fintype_card (α := Fin 4),
        Fintype.card_fin]
      exact card_starOf_le_of_le hAI hb
    · rw [← hWD]
      exact Subgroup.card_le_of_le (starOf_le_wStar A _)
  · obtain ⟨⟨eD⟩, ⟨eI⟩⟩ := h226 G A E U c L hpair h81
    have hb := (hAut (iGroup A) (A.subgroupOf (iGroup A)) hAe').1 ⟨eI⟩ (hcardA'.trans h81)
    rw [Nat.card_congr eD.toEquiv, Nat.card_perm, Nat.card_eq_fintype_card (α := Fin 5),
      Fintype.card_fin]
    exact card_starOf_le_of_le hAI hb

theorem rank3II_23_1_of_item222 (h226 : Item226) (h229 : Item229) (h222 : Item222)
    (hstar : Item231IStar) : Item231 := by
  intro G _ _ A E U c L hpair
  have hI := hstar G A E U c L hpair
  rcases card_eq_of_item222 h222 hpair with h27 | h81
  · rcases h229 G A E U c L hpair h27 with ⟨⟨eD⟩, hI4⟩ | ⟨hWD, ⟨eW⟩, hI6⟩
    · exact Or.inr (Or.inl ⟨hI4, ⟨(MulEquiv.subgroupCongr hI).trans eD⟩, h27⟩)
    · exact Or.inr (Or.inr ⟨hI6,
        ⟨(MulEquiv.subgroupCongr (hI.trans hWD.symm)).trans eW⟩, h27⟩)
  · obtain ⟨⟨eD⟩, hI5⟩ := h226 G A E U c L hpair h81
    exact Or.inl ⟨hI5, ⟨(MulEquiv.subgroupCongr hI).trans eD⟩, h81⟩

end CFSG.RankThree.PartTwo.Sec21
