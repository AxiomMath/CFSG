module

public import CFSG.RankThree.PartTwo.Sec21.Item211ResProofSplitBloomA
public import CFSG.RankThree.PartTwo.Sec21.Item211ResProofSplitBloomB
public import CFSG.RankThree.PartTwo.Sec21.Item211ResProofSplitBloomC
public import CFSG.RankThree.PartTwo.Toolkit.Bloom
public import Certificates.Certificate8171
public import Certificates.Certificate8172
public import Certificates.Certificate8173
public import CFSG.Assembly.OrderReductions.InvertedSubgroup
public import CFSG.Assembly.OrderReductions.OddInversion
public import CFSG.GroupTheory.LocalCores.Fitting
public import CFSG.LieType.Chevalley.LangRootArithmetic
public import CFSG.LocalAnalysis.ComponentInitial.SuzukiModelSchreier
public import CFSG.LocalAnalysis.ShultStronglyClosedTI.SuzukiModelPointStructure
public import CFSG.RankThree.PartTwo.Sec4.LThreePiSLOn
public import CFSG.RankThree.PartTwo.Sec8.Pairs
public import CFSG.RankThree.PartTwo.Sec8.Statements
public import CFSG.StronglyEmbedded.ParityCriterion
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Defs

public section

namespace CFSG.RankThree.PartTwo.Sec21

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo Item2130SplitProof

theorem Item2130SplitProof.SplitHyp.card_B {G : Type} [Group G] [Finite G] {A B N : Subgroup G}
    (h : SplitHyp A B N) : Nat.card B = 3 ^ 2 ∨ Nat.card B = 3 ^ 3 := by
  have hBp : IsPGroup 3 B := fun x => ⟨1, Subtype.ext (by simpa using h.cube (h.le x.2))⟩
  obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp hBp
  have h9 := h.nine
  have h81 := h.le81
  have hc := h.card
  rw [hk] at h9 hc
  have hk2 : 2 ≤ k := by
    by_contra hlt
    have : 3 ^ k ≤ 3 ^ 1 := Nat.pow_le_pow_right (by norm_num) (by omega)
    omega
  have hk3 : k ≤ 3 := by
    by_contra hlt
    have : 3 ^ 4 ≤ 3 ^ k := Nat.pow_le_pow_right (by norm_num) (by omega)
    omega
  interval_cases k
  · exact Or.inl hk
  · exact Or.inr hk

theorem item2130Split :
    Item2130Split := by
  intro G _ _ A B N hA hBA hcard hB9 hA81 hNA hNB hirr hfaith
  have h : SplitHyp A B N :=
    { elem := hA, le := hBA, card := hcard, normA := hNA, normB := hNB, nine := hB9,
      le81 := hA81, irr := hirr, faith := hfaith }
  by_cases hex : ∃ w ∈ N, (∀ b ∈ B, w * b * w⁻¹ = b) ∧ ∃ a ∈ A, w * a * w⁻¹ ≠ a
  · obtain ⟨w, hw, hwB, hwA⟩ := hex
    exact h.exists_of_trivial_on hw hwB hwA
  have hfB : ∀ w ∈ N, (∀ b ∈ B, w * b * w⁻¹ = b) → ∀ a ∈ A, w * a * w⁻¹ = a := by
    intro w hw hwB a ha
    by_contra hne
    exact hex ⟨w, hw, hwB, a, ha, hne⟩
  rcases h.card_B with h9 | h27
  · exact h.concl_of_card_nine h9 hfB
  · obtain ⟨f⟩ := Sec12.exists_coords h.elemB h27
    have hA81' : Nat.card A = 3 ^ 4 := by
      rw [hcard, h27]
      norm_num
    rcases (Toolkit.toolkit_clause2 _ (h.isIrreducibleOn_M1 f)).1 with hCA | hCB | hCC
    · exact h.concl_of_bloomCaseA f hfB hCA
    · exact h.concl_of_statedSL f hfB hA81' (Toolkit.statedSL_le_of_caseB hCB)
    · exact h.concl_of_bloomCaseC f hfB hCC

theorem item2130_of_lStar_local
    (h2115 : Item2115) (hL : Item2130LStar)
    (hLoc : Item2130Local) : Item2130 :=
  item2130_of h2115 hL item2130Split hLoc

end CFSG.RankThree.PartTwo.Sec21
