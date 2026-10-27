module

public import CFSG.RankThree.PartOne.S12.Sec13
import CFSG.RankThree.PartOne.S10.AmbientTheta
public import CFSG.RankThree.PartOne.S12.Facts

public section

namespace CFSG.RankThree.PartOne.U5E

open CFSG CFSG.Assembly CFSG.Assembly.RankThreeEven CFSG.RankThree CFSG.RankThree.LocalRank
  CFSG.RankThree.GroupTheory CFSG.RankThree.PartOne
open CFSG.LocalAnalysis.ComponentInitial (SchreierFor)

@[expose] def Reinst5 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (p : ℕ) (A : Subgroup G) (c : G) (L E : Subgroup G),
    Sec15Hyp G p A c L E → Sec12Facts G p A c L E → Outcome152Five p E A (lieGenerated p E) →
    ∀ B ∈ admissibleTriples p E, ∃ (c' : G) (L' : Subgroup G),
      Sec15Hyp G p B c' L' E ∧ Sec12Facts G p B c' L' E ∧ Outcome152Five p E B (lieGenerated p E)

theorem reinst5_of_nodes (h11 : Sec11One) (h122 : Node122) (h122b : Node122b) (h123 : Node123)
    (h124 : Node124) (h125 : Node125) : Reinst5 := by
  intro G _ _ p A c L E h15 hF hout B hB
  have h := h15.h12
  obtain ⟨L', hL'0, hL'1⟩ := h11 G p B (h.setup_of_admissible hB)
  obtain ⟨c', hc'B, hc'1, hL'c'⟩ := mem_thetaComponentFamily_iff.mp
    ((sectionTenZeroStar_subset p B).2.2.1 hL'0.2)
  have hB' : Sec12Hyp G p B c' L' E := h.reinstantiate hB hc'B hc'1 ⟨⟨hL'0, hL'1⟩, hL'c'⟩
  refine ⟨c', L', ⟨hB', h15.I_ne_top⟩, Sec12Facts.of_nodes h122 h122b h123 h124 h125 hB', ?_⟩
  obtain ⟨f, hf1, hpf, hI, hX, hcardE, -, hev⟩ := hout
  refine ⟨f, hf1, hpf, hI, hX, hcardE, fun hEB => ?_, hev⟩
  obtain ⟨-, -, hBcard, -⟩ := hB
  have hp := h.prime
  rw [← hEB, hcardE] at hBcard
  have hlt : p ^ 3 < p ^ 4 := Nat.pow_lt_pow_right hp.one_lt (by norm_num)
  omega

end CFSG.RankThree.PartOne.U5E
