module

public import CFSG.RankThree.PartTwo.Sec21.Item232
public import CFSG.RankThree.PartTwo.Sec21.Item22DStar
public import CFSG.RankThree.PartTwo.Sec21.SylowThree
public import CFSG.RankThree.PartTwo.KFacts.KS21Terminal
import CFSG.RankThree.PartTwo.Sec4.LThreePiAct
public import CFSG.RankThree.PartTwo.Sec21.Item231

public section

namespace CFSG.RankThree.PartTwo.Sec21

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open CFSG.Assembly.RankThreeEven (projSL projSU projSp)

variable {G : Type} [Group G]

theorem mem_of_mem_centralizer_of_orderOf_eq_three {A : Subgroup G} (hA : A ∈ partTwoF G)
    {x : G} (hx : x ∈ Subgroup.centralizer (A : Set G)) (hx3 : orderOf x = 3) : x ∈ A :=
  Sec4.mem_of_maximal_of_commute ⟨hA.1, fun B hB hAB => (hA.2.1 B hB hAB).le⟩
    (by rw [← hx3]; exact pow_orderOf_eq_one x) fun a ha => Subgroup.mem_centralizer_iff.mp hx a ha

theorem rank3II_23_2_of (h231 : Item231) (h2130 : Item2130) (h222 : Item222)
    (hKW : KOfWellDefinedAll) (hSyl : KFacts.KS21.TerminalSylowThree) : Item232 := by
  intro G _ _ A E U c L hpair
  have hK := hKW G A E U c L hpair
  have hAI := le_iGroup h2130 h222 hpair hK
  have hW := normalizer_le_nGroup hK
  refine ⟨hAI, fun P hAP => ?_⟩
  have hcase : (Nonempty (iGroup A ≃* projSU 5 2 3) ∧ Nat.card A = 3 ^ 4) ∨
      (Nonempty (iGroup A ≃* projSL 4 (GaloisField 2 2)) ∧ Nat.card A = 3 ^ 3) ∨
      (Nonempty (iGroup A ≃* projSp 3 (GaloisField 2 2)) ∧ Nat.card A = 3 ^ 3) := by
    rcases h231 G A E U c L hpair with ⟨he, -, hc⟩ | ⟨he, -, hc⟩ | ⟨he, -, hc⟩
    · exact Or.inl ⟨he, hc⟩
    · exact Or.inr (Or.inl ⟨he, hc⟩)
    · exact Or.inr (Or.inr ⟨he, hc⟩)
  obtain ⟨h1, h2, Q, hQ⟩ := hSyl G (iGroup A) (nGroup A) A (iGroup_le_nGroup A) le_rfl hAI
    hpair.mem_S.1.1 hcase
    (fun x _ hx hx3 => mem_of_mem_centralizer_of_orderOf_eq_three hpair.mem_S.1 hx hx3) P hAP
  refine ⟨h1, h2, hW, ?_⟩
  obtain ⟨S, hS⟩ := rank3II_23_2_four Q (by rw [hQ]; exact h2) hW
  exact ⟨S, hS.trans hQ⟩

end CFSG.RankThree.PartTwo.Sec21
