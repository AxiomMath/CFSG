module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC23Rank
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC7SixtyTwoBar2
public import CFSG.LocalAnalysis.UniquenessCase.UC22P22a

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22

variable {G : Type} [Group G] [Finite G]

theorem c23_hyp141_of_case2 (D : Data G) (hx : DataExt D) (h115 : F11.R115 D) (h127 : R127 D)
    (h1217 : R1217 D) {V L : Subgroup G} {hV : IsElemAbelian 2 V} (hS : Sect16 D ⊥ V L hV)
    (hc : Case167_2 D ⊥ V hV L) {K₁ K₂ X : Subgroup G} (hK₁ : K₁ ∈ calC D.M)
    (hK₂ : K₂ ∈ calC D.M) (hne : K₁ ≠ K₂) (hL₁ : IsL3 ↥(barSub ⊥ V hV K₁) 1)
    (hL₂ : IsL3 ↥(barSub ⊥ V hV K₂) 1) (hXsyl : CFSG.ABGLocalTools.IsSylowOf 3 X (K₁ ⊔ K₂))
    (hperm : Permutes X D.T) : Hyp141 D K₁ K₂ X := by
  have hP := hS.setting.hyp16.hyp125.pairFacts
  have hMs : D.M ≤ stabTil ⊥ V := le_stabTil hP.le_normalizer hP.le_normalizer₀
  have hK₁M : K₁ ≤ D.M := uc22p22a_le_of_isSubnormal hK₁.1
  have hK₂M : K₂ ≤ D.M := uc22p22a_le_of_isSubnormal hK₂.1
  exact ⟨hc.2.2.2, c23_evenRank_eq_three D hx h115 h127 h1217 hS (Or.inl hc), hK₁, hK₂, hne,
    (s16c7_bar2_of_calC hV hMs hK₁M hK₁.2.2 hL₁).1, (s16c7_bar2_of_calC hV hMs hK₂M hK₂.2.2 hL₂).1,
    hXsyl, hperm⟩

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
