module

public import CFSG.LocalAnalysis.StandardType.GGQ2S08TwoNodeBasics
public import CFSG.LocalAnalysis.StandardType.GGDepED4ReadDefs
public import CFSG.LocalAnalysis.StandardType.GGDepED4RowSmall

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

theorem ggQ2s08_ce6_resHyp {G : Type} [Group G] [Finite G] {B Bs : Subgroup G} {x y : G}
    {L D J K : Subgroup G} (hS : GGQTwoSetting 3 B Bs x L D J) (hK : GGNbr 3 B x D J y K)
    (hRG : GGReflGenerated 3 (ggAutomizer K Bs)) : GGResHyp 3 B Bs x L D J y K :=
  ⟨hS.1.1, hS.1.2.1, hS.1.2.2.1, hS.1.2.2.2.1, hK, hRG,
    Or.inl (ggScalarsPmOne_of_prime_three hS.1.1 rfl)⟩

theorem ggQ2s08_ce6_rowAt {G : Type} [Group G] {p : ℕ} {X J : Subgroup G}
    (h : GGQ2S08RowTwE6 p X J) : p = 3 ∧ GGResRowAt ggRowTwoNodeSmallJD 3 J X := by
  obtain ⟨labX, labJ, hmX, hmJ, htJ, hrJ, htX, hn, hp, hdiv⟩ := h
  obtain ⟨lX, hΛX, hlX, hhX⟩ :=
    FrameRoute.ggFrameQTwo_exists_hasLabel (P := fun lab => lab = labX) hmX
  obtain ⟨lJ, hΛJ, hlJ, hhJ⟩ :=
    FrameRoute.ggFrameQTwo_exists_hasLabel (P := fun lab => lab = labJ) hmJ
  subst hlX hlJ
  refine ⟨hp, lJ, lX, hΛJ, hΛX, hhJ, hhX, ?_⟩
  obtain ⟨tX, rX, nX⟩ := lX
  obtain ⟨tJ, rJ, nJ⟩ := lJ
  dsimp only at htJ hrJ htX hn
  subst htJ hrJ htX hn
  have hrX : rX = 0 := hΛX.2
  subst hrX
  subst hp
  refine ⟨⟨Or.inr (Or.inr (Or.inr ⟨rfl, rfl, hdiv, rfl⟩)), by show (0 : ℕ) ≤ 9; omega⟩, rfl⟩

end CFSG.StandardType

end
