module

public import CFSG.Timmesfeld.CorollaryBMain
public import CFSG.LargeExtraspecial.S8CorBStatement
import CFSG.CGT.Timmesfeld75.BenderInputs3

public section

namespace CFSG.Timmesfeld

open CFSG.BenderSuzuki CFSG.LargeExtraspecial

namespace CorB

private theorem statedClassicalModel_psl2 {K : Type} [Group K] {n : ℕ} (hn : 2 ≤ n)
    (e : K ≃* PSL2Model n) : CFSG.Assembly.LowTwoRank.StatedClassicalModel K .PSL 2 2 n :=
  CFSG.CGT.Timmesfeld75.statedClassicalModel_psl2_of_mulEquiv hn e

private theorem statedClassicalModel_psu3 {K : Type} [Group K] {n : ℕ} (hn : 2 ≤ n)
    (e : K ≃* PSU3Model n) : CFSG.Assembly.LowTwoRank.StatedClassicalModel K .PSU 3 2 n :=
  CFSG.CGT.Timmesfeld75.statedClassicalModel_psu3_of_mulEquiv hn e

private theorem lieModel_twistedB2 {K : Type} [Group K] {a : ℕ} (ha : 1 ≤ a)
    (e : K ≃* SzModel a) : CFSG.Blueprint.LieModel K .twistedB2 0 2 (2 * a + 1) :=
  CFSG.CGT.Timmesfeld75.lieModel_twistedB2_of_mulEquiv_szModel ha e

theorem corBList_of_isBenderGroup {Y : Type} [Group Y] (h : IsBenderGroup Y) : S8.CorBList Y := by
  rcases h with ⟨n, hn, e⟩ | ⟨a, ha, e⟩ | ⟨n, hn, e⟩
  · exact Or.inl ⟨n, Or.inl ⟨by decide, statedClassicalModel_psl2 hn e⟩⟩
  · exact Or.inr (Or.inr (Or.inl ⟨2 * a + 1, lieModel_twistedB2 ha e⟩))
  · exact Or.inr (Or.inl ⟨n, Or.inl ⟨by decide, statedClassicalModel_psu3 hn e⟩⟩)

theorem corBList_of_outcomeTwo {Y : Type} [Group Y] {D : Set Y} (h : OutcomeTwo Y D) :
    S8.CorBList Y := by
  rcases h with ⟨f, -, -, hL⟩ | ⟨f, -, -, hL⟩ | ⟨f, -, -, hL⟩ | hU | hA | hJ
  · exact Or.inr (Or.inr (Or.inr (Or.inl ⟨f, hL⟩)))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨f, hL⟩))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨f, hL⟩))))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hU)))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hA)))))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hJ)))))))

end CorB

theorem timmesfeldCorBInput : S8.TimmesfeldCorBInput := by
  intro X _ _ t ht hW2 hW3 hfus
  have h : CorB.Setup t := ⟨ht, hW2, hW3, hfus⟩
  rcases CorB.main h with hi | hii | ⟨-, hB⟩ | ⟨-, hO⟩
  · exact Or.inl hi
  · exact Or.inr (Or.inl hii)
  · exact Or.inr (Or.inr (CorB.corBList_of_isBenderGroup hB))
  · exact Or.inr (Or.inr (CorB.corBList_of_outcomeTwo hO))

end CFSG.Timmesfeld
