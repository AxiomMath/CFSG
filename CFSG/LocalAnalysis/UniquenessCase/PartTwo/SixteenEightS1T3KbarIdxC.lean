module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenEightS1T3KbarIdxCB

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22

variable {W : Type} [CommGroup W] [Finite W] {A L T : Subgroup (MulAut W)}

theorem s16t3_exists_section_hom (h : ThreeNat A L T) (h7 : Nat.card ↥(irrSet L) = 7) :
    ∃ (J₀ : Subgroup W) (g : ↥A →* MulAut (↥J₀ ⧸ (J₀ ⊓ fixV L).subgroupOf J₀)),
      J₀ ∈ irrSet L ∧ g.ker = (s1t3KBar A L).subgroupOf A ∧
      ∀ l : ↥A, (l : MulAut W) ∈ L → ∀ u : ↥J₀, ∀ hu : (l : MulAut W) (u : W) ∈ J₀,
        g l (QuotientGroup.mk u) = QuotientGroup.mk ⟨(l : MulAut W) (u : W), hu⟩ := by
  have hpos : 0 < Nat.card ↥(irrSet L) := by rw [h7]; norm_num
  obtain ⟨J₀, hJ₀⟩ : ∃ J₀ : Subgroup W, J₀ ∈ irrSet L := by
    have hne : Nonempty ↥(irrSet L) := (Nat.card_pos_iff.mp hpos).1
    exact ⟨(Classical.choice hne : ↥(irrSet L)), (Classical.choice hne).2⟩
  obtain ⟨g, hker, hg⟩ := s16t3_exists_section_hom_of_mem h h7 hJ₀
  exact ⟨J₀, g, hJ₀, hker, hg⟩

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
