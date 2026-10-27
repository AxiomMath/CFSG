module

public import CFSG.LocalAnalysis.StandardType.GGQ2S08TwoNodeBasics
public import CFSG.LocalAnalysis.StandardType.GGQTwoAssemble

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly

@[expose] def GGQ2S08TNCellL (P : GGQ2S08Pos) : Prop :=
  ∀ {G : Type} [Group G] [Finite G] {p : ℕ} [Fact p.Prime], p = 3 →
    ∀ {B Bs : Subgroup G} {x : G} {L D J : Subgroup G}, GGQTwoSetting p B Bs x L D J →
      GGQTwoI1 Bs D J → ∀ {y : G} {K : Subgroup G}, GGNbr p B x D J y K →
      P p L J → x ∉ L →
        Subgroup.normalizer (Bs : Set G) ≤ Subgroup.normalizer (ggG0 p B x L D J : Set G)

@[expose] def GGQ2S08NoNbrCellK (P : GGQ2S08Pos) : Prop :=
  ∀ {G : Type} [Group G] [Finite G] {p : ℕ} [Fact p.Prime], p = 3 →
    ∀ {B Bs : Subgroup G} {x : G} {L D J : Subgroup G}, GGQTwoSetting p B Bs x L D J →
      GGQTwoI1 Bs D J → ∀ {y : G} {K : Subgroup G}, GGNbr p B x D J y K →
      P p K J → y ∉ K → False

theorem ggQ2s08_tnCell_of_LK {P : GGQ2S08Pos} (hL : GGQ2S08TNCellL P) (hK : GGQ2S08TNCellK P) :
    GGQ2S08TNCell P := by
  intro G _ _ p _ hp B Bs x L D J hS hI1 y K hnb hrow
  rcases hrow with ⟨hP, hx⟩ | ⟨hP, hy⟩
  · exact hL hp hS hI1 hnb hP hx
  · exact hK hp hS hI1 hnb hP hy

end CFSG.StandardType

end
