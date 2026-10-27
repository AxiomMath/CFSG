module

public import CFSG.RankThree.PartOne.S12.Sec12A
public import CFSG.RankThree.PartOne.S12.Skeleton
import CFSG.RankThree.PartOne.S10.AmbientTheta

public section

namespace CFSG.RankThree.PartOne

open CFSG CFSG.Assembly CFSG.Assembly.RankThreeEven CFSG.RankThree CFSG.RankThree.LocalRank
  CFSG.RankThree.GroupTheory

variable {G : Type} [Group G] [Finite G] {p : ℕ} {A : Subgroup G} {c : G} {L E : Subgroup G}

theorem Sec12Hyp.setup_of_admissible (h : Sec12Hyp G p A c L E) {B : Subgroup G}
    (hB : B ∈ admissibleTriples p E) : SteinbergBM.SectionTenSetup G p B := by
  obtain ⟨-, hBel, hBcard, S, hS1, hS2, hBS⟩ := hB
  obtain ⟨hsimple, hnonab, hK, hchar, he, hQ, -, -, -, hpref⟩ := h.setup
  exact ⟨hsimple, hnonab, hK, hchar, he, hQ, hBel, hBcard, ⟨S, hS1, hS2, hBS⟩, hpref⟩

theorem sec13_one_b (h11 : Sec11One) (h126 : Node126) (h127 : Node127) (h128 : Node128)
    (h129 : Node129) (h : Sec12Hyp G p A c L E) (hT : ¬ Outcome152Five p E A (lieGenerated p E))
    {B : Subgroup G} (hB : B ∈ admissibleTriples p E) :
    sectionTenZeroStar p B ⊆ sectionTenOne p B := by
  obtain ⟨-, hnotrans, -⟩ := sec13_one_of_nodes h126 h127 h128 h129 h hT
  obtain ⟨L', hL'0, hL'1⟩ := h11 G p B (h.setup_of_admissible hB)
  obtain ⟨c', hc'B, hc'1, hL'c'⟩ := mem_thetaComponentFamily_iff.mp
    ((sectionTenZeroStar_subset p B).2.2.1 hL'0.2)
  have hB' : Sec12Hyp G p B c' L' E := h.reinstantiate hB hc'B hc'1 ⟨⟨hL'0, hL'1⟩, hL'c'⟩
  intro X hX
  by_contra hX1
  have hX0 := (sectionTenZeroStar_subset p B).2.2.1 hX.2
  have hX2 : X ∈ sectionTenTwo p B := ⟨hX0, hX1⟩
  exact hnotrans (h128 G p B c' L' E hB' ⟨X, hX, hX2⟩)

end CFSG.RankThree.PartOne
