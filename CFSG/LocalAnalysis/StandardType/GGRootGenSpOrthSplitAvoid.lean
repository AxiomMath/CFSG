module

public import CFSG.LocalAnalysis.StandardType.GGOmegaPlusRootGenAvoid
import CFSG.LocalAnalysis.StandardType.GGSpRootGenAvoid
import CFSG.LocalAnalysis.StandardType.GGCorFiveTwentySp
import CFSG.LocalAnalysis.StandardType.GGCorFiveTwentyRefl

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.Open

@[expose] def GGRootGenSpSplitLabel (p : ℕ) (lab : LargeEvenLabel) : Prop :=
  p ∣ 2 ^ lab.n - 1 ∧ (lab.tag = .B ∨ lab.tag = .C) ∧ 3 ≤ lab.rank

theorem ggRootGenKGAvoidOn_spSplit :
    GGRootGenKGAvoidOn GGRootGenSpSplitLabel := by
  rintro p ⟨t, l, n⟩ hp hp2 hlab ⟨hpn, ht, hl⟩
  dsimp only at ht hpn hl
  have hn1 : 1 ≤ n := hlab.1
  have hn : 2 ≤ n := by
    by_contra h
    have hn' : n = 1 := by omega
    subst hn'
    norm_num at hpn
    exact hp.one_lt.ne' hpn
  exact SpAvoid.largeEvenLabelAll_rootGenAvoidKG_symplectic ht hp hp2 hpn hn hl

@[expose] def GGRootGenSpOrthSplitLabel (p : ℕ) (lab : LargeEvenLabel) : Prop :=
  GGRootGenSpSplitLabel p lab ∨ GGRootGenOrthSplitLabel p lab

theorem ggRootGenKGAvoidOn_spOrthSplit :
    GGRootGenKGAvoidOn GGRootGenSpOrthSplitLabel := by
  intro p lab hp hp2 hlab hS
  rcases hS with hS | hS
  · exact ggRootGenKGAvoidOn_spSplit p lab hp hp2 hlab hS
  · exact ggRootGenKGAvoidOn_orthSplit p lab hp hp2 hlab hS

theorem ggRootGenLInputOnNS_spOrthSplit :
    GGRootGenLInputOnNS GGRootGenSpOrthSplitLabel := by
  intro G _ _ p B Bs x L D J hHyp _ _ _ hL
  exact ggRootCompGenAvoiding_L_of_avoidOn ggRootGenKGAvoidOn_spOrthSplit hHyp hL

theorem ggRootGenNbrInputOnNS_spOrthSplit :
    GGRootGenNbrInputOnNS GGRootGenSpOrthSplitLabel := by
  intro G _ _ p B Bs x L D J hHyp _ _ _ y K hnb hK
  exact ggRootCompGenAvoiding_nbr_of_avoidOn ggRootGenKGAvoidOn_spOrthSplit hHyp hnb hK

theorem ggRootGenLInputOnNS_open_of_not_spOrthSplit
    (h : GGRootGenLInputOnNS fun p lab =>
      GGRootGenOpenLabel p lab ∧ ¬ GGRootGenSpOrthSplitLabel p lab) :
    GGRootGenLInputOnNS GGRootGenOpenLabel := by
  intro G _ _ p B Bs x L D J hHyp hq hN hW hL
  rcases (GGInnerDiagOnLabel.mono_label (T := fun p lab => GGRootGenSpOrthSplitLabel p lab ∨
      (GGRootGenOpenLabel p lab ∧ ¬ GGRootGenSpOrthSplitLabel p lab))
      (fun lab hlab => (em (GGRootGenSpOrthSplitLabel p lab)).imp_right fun hn => ⟨hlab, hn⟩)
      hL).elim_or with h₁ | h₂
  · exact ggRootGenLInputOnNS_spOrthSplit G p B Bs x L D J hHyp hq hN hW h₁
  · exact h G p B Bs x L D J hHyp hq hN hW h₂

theorem ggRootGenNbrInputOnNS_open_of_not_spOrthSplit
    (h : GGRootGenNbrInputOnNS fun p lab =>
      GGRootGenOpenLabel p lab ∧ ¬ GGRootGenSpOrthSplitLabel p lab) :
    GGRootGenNbrInputOnNS GGRootGenOpenLabel := by
  intro G _ _ p B Bs x L D J hHyp hq hN hW y K hnb hK
  rcases (GGInnerDiagOnLabel.mono_label (T := fun p lab => GGRootGenSpOrthSplitLabel p lab ∨
      (GGRootGenOpenLabel p lab ∧ ¬ GGRootGenSpOrthSplitLabel p lab))
      (fun lab hlab => (em (GGRootGenSpOrthSplitLabel p lab)).imp_right fun hn => ⟨hlab, hn⟩)
      hK).elim_or with h₁ | h₂
  · exact ggRootGenNbrInputOnNS_spOrthSplit G p B Bs x L D J hHyp hq hN hW y K hnb h₁
  · exact h G p B Bs x L D J hHyp hq hN hW y K hnb h₂

end CFSG.StandardType

end
