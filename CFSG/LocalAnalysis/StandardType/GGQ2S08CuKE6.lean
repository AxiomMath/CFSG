module

public import CFSG.LocalAnalysis.StandardType.GGQ2S08Ce6Close
public import CFSG.LocalAnalysis.StandardType.GGQ2S08TwoNode

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

@[expose] def GGQ2S08PosE6 : GGQ2S08Pos := fun p X J => GGQ2S08RowE6 p X J

@[expose] def GGQ2S08PosASmall : GGQ2S08Pos := fun p X J =>
  ∃ N, N < 12 ∧ GGQ2S08RowA p N X J

theorem ggQ2s08_ce6_rowAtE6 {G : Type} [Group G] {p : ℕ} {X J : Subgroup G}
    (h : GGQ2S08RowE6 p X J) : p = 3 ∧ GGResRowAt ggRowTwoNodeSmallJD 3 J X := by
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
  refine ⟨⟨Or.inr (Or.inr (Or.inl ⟨rfl, rfl, hdiv, rfl⟩)), by show (0 : ℕ) ≤ 9; omega⟩, rfl⟩

theorem ggQ2s08_ceE6K_holds (hIn : GGQ2S08Ce6In)
    (hRGK : ∀ {G : Type} [Group G] [Finite G] {p : ℕ} [Fact p.Prime] {B Bs : Subgroup G}
      {x : G} {L D J : Subgroup G}, GGQTwoSetting p B Bs x L D J → ∀ {y : G} {K : Subgroup G},
      GGNbr p B x D J y K → GGReflGenerated p (ggAutomizer K Bs)) :
    GGQ2S08NoNbrCellK GGQ2S08PosE6 := by
  intro G _ _ p _ hp B Bs x L D J hS hI1 y K hnb hrow hyK
  subst hp
  have hH := ggQ2s08_ce6_resHyp hS hnb (hRGK hS hnb)
  exact ggQ2s08_ce6_K hIn hH hI1 (ggQ2s08_ce6_rowAtE6 hrow).2 hyK

end CFSG.StandardType

end
