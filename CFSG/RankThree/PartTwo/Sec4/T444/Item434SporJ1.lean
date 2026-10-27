module

public import CFSG.RankThree.PartTwo.Sec4.T444.Item434Spor
public import CFSG.Sporadic.Schreier.J1Outer
import CFSG.Sporadic.Bridge.J1
import CFSG.RankThree.PartTwo.Sec4.T444.Item434L34

public section

namespace CFSG.RankThree.PartTwo.Sec4

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo CFSG.Blueprint

theorem pRank_three_mulAut_J1_le_one :
    CFSG.pRank 3 (MulAut NativeSporadic.J1) ≤ 1 := by
  have hsurj : Function.Surjective
      (MulAut.conj : NativeSporadic.J1 →* MulAut NativeSporadic.J1) := by
    intro φ
    obtain ⟨g, hg⟩ := CFSG.Sporadic.Schreier.at_j1_schreier.2.1 φ
    exact ⟨g, hg.symm⟩
  have hdvd : Nat.card (MulAut NativeSporadic.J1) ∣ 175560 := by
    rw [← CFSG.Sporadic.J1.card_J1]
    exact Subgroup.card_dvd_of_surjective hsurj
  refine csSup_le' ?_
  rintro r ⟨B, -, hcard⟩
  have h3 : 3 ^ r ∣ 175560 := hcard ▸ (Subgroup.card_subgroup_dvd_card B).trans hdvd
  by_contra hr
  have h9 : 3 ^ 2 ∣ 3 ^ r := Nat.pow_dvd_pow 3 (by omega)
  have := h9.trans h3
  norm_num at this

section Families


theorem item434SporJ1 : Item434SporAt .J1 := by
  intro G₀ _ _ hG₀ H G _ _ f hf hker A M Q hc hL
  obtain ⟨e₀⟩ := hL
  obtain ⟨b⟩ := CFSG.Sporadic.Bridge.J1.nonempty_mulEquiv
  have b' : NativeSporadic.J1 ≃* Spor .J1 := b
  exact (hc.false_of_pRank_mulAut_le_one (e₀.trans b'.symm) pRank_three_mulAut_J1_le_one).elim

end Families

end CFSG.RankThree.PartTwo.Sec4
