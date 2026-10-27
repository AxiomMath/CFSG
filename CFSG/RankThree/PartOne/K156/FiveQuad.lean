module

public import CFSG.RankThree.PartOne.K156.FiveTrans
import CFSG.RankThree.PartOne.S10.AmbientTheta

public section

namespace CFSG.RankThree.PartOne.K156

open CFSG CFSG.Assembly CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.GroupTheory
  CFSG.RankThree.PartOne
open CFSG.LocalAnalysis.ComponentInitial (SchreierFor)

variable {G : Type} [Group G] [Finite G] {p : ℕ} {A : Subgroup G} {c : G} {L E : Subgroup G}

theorem sectionTenZeroStar_subset_one_five (h11 : Sec11One) (h128 : Node128)
    (hnot : ¬ torusHasTransvection p E) (h : Sec12Hyp G p A c L E) {B : Subgroup G}
    (hB : B ∈ admissibleTriples p E) : sectionTenZeroStar p B ⊆ sectionTenOne p B := by
  obtain ⟨L', hL'0, hL'1⟩ := h11 G p B (h.setup_of_admissible hB)
  obtain ⟨c', hc'B, hc'1, hL'c'⟩ := mem_thetaComponentFamily_iff.mp
    ((sectionTenZeroStar_subset p B).2.2.1 hL'0.2)
  have hB' : Sec12Hyp G p B c' L' E := h.reinstantiate hB hc'B hc'1 ⟨⟨hL'0, hL'1⟩, hL'c'⟩
  intro X hX
  by_contra hX1
  have hX0 := (sectionTenZeroStar_subset p B).2.2.1 hX.2
  have hX2 : X ∈ sectionTenTwo p B := ⟨hX0, hX1⟩
  exact hnot (h128 G p B c' L' E hB' ⟨X, hX, hX2⟩)

theorem outcome152Five_of_admissible (h : Sec12Hyp G p A c L E)
    (hout : Outcome152Five p E A (lieGenerated p E)) {B : Subgroup G}
    (hB : B ∈ admissibleTriples p E) : Outcome152Five p E B (lieGenerated p E) := by
  obtain ⟨f, hf1, hpf, hI, hX, hcardE, -, hev⟩ := hout
  refine ⟨f, hf1, hpf, hI, hX, hcardE, fun hEB => ?_, hev⟩
  obtain ⟨-, -, hBcard, -⟩ := hB
  have hp := h.prime
  rw [← hEB, hcardE] at hBcard
  have hlt : p ^ 3 < p ^ 4 := Nat.pow_lt_pow_right hp.one_lt (by norm_num)
  omega

theorem exists_quad_five (hS : SchreierFor InCatalog) (hTwo : TwoActionInputs)
    (h106 : SectionTenMaximalMovingThetaComponentsQuasisimple) (h11 : Sec11One)
    (h122 : Node122) (h122b : Node122b) (h123 : Node123) (h124 : Node124) (h125 : Node125)
    (h128 : Node128) (hMod : KFU5Mod) (h15 : Sec15Hyp G p A c L E)
    (hF : Sec12Facts G p A c L E) (hout : Outcome152Five p E A (lieGenerated p E))
    {B : Subgroup G} (hB : B ∈ admissibleTriples p E) {Y : Subgroup G}
    (hY : Y ∈ sectionTenZeroStar p B) :
    ∃ c' : G, c' ∈ B ∧ c' ≠ 1 ∧ Y ∈ thetaComponentsAt p c' ∧ Sec12Hyp G p B c' Y E ∧
      Sec12Facts G p B c' Y E ∧ Sec15Hyp G p B c' Y E ∧
        Outcome152Five p E B (lieGenerated p E) ∧ Y ∈ thetaCompZeroStarE p E := by
  have h := h15.h12
  have hnot := not_torusHasTransvection_five hMod h15 hF hout
  have hone := sectionTenZeroStar_subset_one_five h11 h128 hnot h hB
  obtain ⟨c', hc'B, hc'1, hYc⟩ := mem_thetaComponentFamily_iff.mp
    ((sectionTenZeroStar_subset p B).2.2.1 hY.2)
  have h' : Sec12Hyp G p B c' Y E := h.reinstantiate hB hc'B hc'1 ⟨⟨hY, hone hY⟩, hYc⟩
  refine ⟨c', hc'B, hc'1, hYc, h', Sec12Facts.of_nodes h122 h122b h123 h124 h125 h',
    ⟨h', h15.I_ne_top⟩, outcome152Five_of_admissible h hout hB, ?_⟩
  refine Sec12Hyp.mem_thetaCompZeroStarE hS hTwo h106 h' ?_
  rcases h122 G p B c' Y E h' with hG | hS5
  · exact Sec12Three.hCE_generic h' hG.center_pPrime (h'.restr_of_generic hG)
  · exact Sec12Three.hCE_su5 hS5

end CFSG.RankThree.PartOne.K156
