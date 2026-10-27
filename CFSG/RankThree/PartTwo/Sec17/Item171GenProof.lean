module

public import CFSG.RankThree.PartTwo.Sec17.Item171Proof
import CFSG.RankThree.PartTwo.Sec17.Item171GenProofA7
import CFSG.RankThree.PartTwo.Sec17.Item171GenProofV
import CFSG.RankThree.PartTwo.Sec17.Item171GenProofA10

public section

namespace CFSG.RankThree.PartTwo.Sec17

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
  CFSG.RankThree.PartTwo.Sec13 CFSG.RankThree.PartTwo.Sec14 CFSG.RankThree.PartTwo.Sec15

theorem kFact171_of (h1514 : Item1514S17) (hMeets : Claim1715Meets) (h142 : Concl142S14) :
    KFact171 := by
  intro G _ _ A c L Y₀ h _
  have hD := h.toSec13Data
  have h142' := h142 G A c L h.toSec14Std
  rcases h1514 G A c L Y₀ h Y₀ h.mem_y0Star (hMeets G A c L Y₀ h) with
    ⟨-, -, hΩ, -⟩ | ⟨hA7, -⟩ | ⟨-, -, -, -, hnot, -⟩
  ·
    exact Proof171.le_delta_of_cover hD h142' h.mem_y0Star.prop.1 h.le_y0
      (Proof171.cover_of_omega h (h1514 G A c L Y₀ h) (hMeets G A c L Y₀ h) hΩ)
  ·
    refine (Proof171Gen.le_sSup_invariantPiSubgroups_of_sec13Data hD hA7).trans
      (sSup_le fun Q hQ => ?_)
    obtain ⟨hQL, hQ3, hAQ⟩ := hQ
    exact le_delta (Proof171.mem_scriptQ_of_le_L hD h142' hQL
      ((isPiSubgroup_piCompl_iff Nat.prime_three Q).mp hQ3) hAQ) hQL
  ·
    exact absurd h.le_y0 (hnot Y₀ h.mem_y0Star)

theorem step171GenA10_of (h1514 : Item1514S17) (hMeets : Claim1715Meets) : Step171GenA10 := by
  intro G _ _ A c L Y₀ h hA10
  rcases h1514 G A c L Y₀ h Y₀ h.mem_y0Star (hMeets G A c L Y₀ h) with
    ⟨-, -, hΩ, -⟩ | ⟨hA7, -, hT, -⟩ | ⟨-, -, -, -, hnot, -⟩
  ·
    refine (Proof171.le_yc_of_cover h (Proof171.cover_of_omega h (h1514 G A c L Y₀ h)
      (hMeets G A c L Y₀ h) hΩ)).trans (le_iSup_of_le 1 (le_iSup_of_le (one_mem _) ?_))
    rw [Late.map_conj_one]
  ·
    exact Proof171Gen.le_iSup_of_le_sup_pCoreOf h
      (Proof171Gen.le_iSup_sup_pCoreOf_of_a10 h hA10 hA7 hT)
  ·
    exact absurd h.le_y0 (hnot Y₀ h.mem_y0Star)

theorem item171S17_of_steps (h1514 : Item1514S17) (hMeets : Claim1715Meets)
    (h142 : Concl142S14) (hComm : Step171Comm) (hD0 : Step171Delta0) : Item171S17 :=
  item171S17_of h1514 hMeets h142 (step171GenA10_of h1514 hMeets) (kFact171_of h1514 hMeets h142)
    hComm hD0

end CFSG.RankThree.PartTwo.Sec17
