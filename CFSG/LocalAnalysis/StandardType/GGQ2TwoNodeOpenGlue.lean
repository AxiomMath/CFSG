module

public import CFSG.LocalAnalysis.StandardType.GGQ2TwoNodeOpenDefs
public import CFSG.LocalAnalysis.StandardType.GGQ2S08CuKE6

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly

theorem ggQ2TwoNodeRest_of_open
    (hIn : GGQ2S08Ce6In)
    (hRGK : ∀ {G : Type} [Group G] [Finite G] {p : ℕ} [Fact p.Prime] {B Bs : Subgroup G}
      {x : G} {L D J : Subgroup G}, GGQTwoSetting p B Bs x L D J → ∀ {y : G} {K : Subgroup G},
      GGNbr p B x D J y K → GGReflGenerated p (ggAutomizer K Bs))
    (h : GGQ2TwoNodeOpenInput) : GGQ2TwoNodeRestInput := by
  intro G _ _ p _ hp B Bs x L D J hS hI1 y K hnb hrow hbig hBL hBK hsel9 hsel9K
  have hc3 : GGQ2S08NoNbrCell (GGQ2S08PosTwA 3) := ggQ2s08_tn3_holds
  have hce6 : GGQ2S08NoNbrCell GGQ2S08PosTwE6 := ggQ2s08_ce6_holds hIn hRGK
  have hcuL : GGQ2S08NoNbrCellL GGQ2S08PosUntw := ggQ2s08_untwL_holds
  have hceK : GGQ2S08NoNbrCellK GGQ2S08PosE6 := ggQ2s08_ceE6K_holds hIn hRGK
  rcases hrow with ⟨hr, hx⟩ | ⟨hr, hy⟩
  · rcases ggQ2s08_pos_cases hp hr with h' | h' | h' | h' | h' | h'
    · exact (hcuL hp hS hI1 hnb h' hx).elim
    · exact (hce6 hp hS hI1 hnb (Or.inl ⟨h', hx⟩)).elim
    · exact (hc3 hp hS hI1 hnb (Or.inl ⟨h', hx⟩)).elim
    · exact h hp hS hI1 hnb (Or.inl ⟨Or.inl h', hx⟩) hbig hBL hBK hsel9 hsel9K
    · exact h hp hS hI1 hnb (Or.inl ⟨Or.inr h', hx⟩) hbig hBL hBK hsel9 hsel9K
    · exact (hbig (Or.inl ⟨h', hx⟩)).elim
  · rcases ggQ2s08_pos_cases hp hr with h' | h' | h' | h' | h' | h'
    · rcases h' with ⟨N, hN⟩ | h'
      · have h12 : N < 12 := by
          by_contra h12
          exact hbig (Or.inr (Or.inr ⟨⟨N, by omega, hN⟩, hy⟩))
        exact h hp hS hI1 hnb (Or.inr ⟨Or.inr (Or.inr ⟨N, h12, hN⟩), hy⟩) hbig hBL hBK hsel9 hsel9K
      · exact (hceK hp hS hI1 hnb h' hy).elim
    · exact (hce6 hp hS hI1 hnb (Or.inr ⟨h', hy⟩)).elim
    · exact (hc3 hp hS hI1 hnb (Or.inr ⟨h', hy⟩)).elim
    · exact h hp hS hI1 hnb (Or.inr ⟨Or.inl h', hy⟩) hbig hBL hBK hsel9 hsel9K
    · exact h hp hS hI1 hnb (Or.inr ⟨Or.inr (Or.inl h'), hy⟩) hbig hBL hBK hsel9 hsel9K
    · exact (hbig (Or.inr (Or.inl ⟨h', hy⟩))).elim

end CFSG.StandardType

end
