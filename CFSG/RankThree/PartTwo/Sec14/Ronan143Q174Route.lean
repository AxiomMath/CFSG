module

public import CFSG.RankThree.PartTwo.Sec17.Item17Res14ProofRoute
public import CFSG.RankThree.PartTwo.Sec14.Ronan143Q174
public import CFSG.RankThree.PartTwo.Sec15.HypS

public section

namespace CFSG.RankThree.PartTwo.Sec14.Ronan143Q

section

open CFSG.RankThree.PartTwo.Sec17
open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
  CFSG.RankThree.PartTwo.Sec13 CFSG.RankThree.PartTwo.Sec14 CFSG.RankThree.PartTwo.Sec15
  CFSG.RankThree.PartTwo.Sec16 CFSG.RankThree.PartTwo.Late CFSG.GH74.GLS
  CFSG.RankThree.PartTwo.Sec17.HeadProof

open CFSG.RankThree.PartTwo.Sec17.Proof17Res14 in
theorem step174KbOThree_of_splitQ
    (h143 : Ronan148Q.Item143QS14) (hΩ : Step174KbOOmega)
    (hHJ : Step174KbOHJ) : Step174KbOThree := by
  intro G _ _ A c L Y₀ h X hXΔ hX3 K hK hSz hθ hcen hAK hY3 b hb hb1 hO2 hD3
  by_cases hbΩ : Subgroup.zpowers b ∈ omegaA A
  · have hA10 : Nonempty (↥Y₀ ⧸ CFSG.pCore 2 ↥Y₀ ≃* alternatingGroup (Fin 10)) := by
      refine h.a10_or_omega.resolve_right fun hΩc => ?_
      have hcL : c ∉ L := h.toSec15R.hypS.2.2 c h.zpowers_mem_omegaA L h.mem_lA
      rw [hΩc, Set.mem_singleton_iff] at hbΩ
      apply hcL
      have hcb : c ∈ Subgroup.zpowers b := hbΩ ▸ Subgroup.mem_zpowers c
      exact Subgroup.zpowers_le.mpr hb.2 hcb
    exact hΩ G A c L Y₀ h hA10 X hXΔ hX3 K hK hSz hθ hcen hAK hY3 b hb hb1 hbΩ hO2 hD3
  · obtain ⟨Qs, hQs⟩ := maxInvariantPiSubgroups_nonempty
      (Sec14.delta A (Sec14.lB A) (Subgroup.centralizer ({b} : Set G))) A (piCompl 3)
    obtain ⟨-, halt⟩ := h143 G A c L h.toSec14Std b hb.1 hb1 hbΩ Qs hQs
    rcases halt with h1 | ⟨b', -, Lb, hb'Ω, hLb, hJ2, -⟩
    · exact absurd (h1 ▸ hD3) (not_three_dvd_card_sup_pPrimeCoreOf hb.1)
    · exact hHJ G A c L Y₀ h X hXΔ hX3 K hK hSz hθ hcen hAK hY3 b hb hb1 hbΩ
        ⟨b', Lb, hb'Ω, hLb, hJ2⟩ hO2 hD3

end

section

open CFSG.RankThree.PartTwo.Sec17
open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
  CFSG.RankThree.PartTwo.Sec13 CFSG.RankThree.PartTwo.Sec14 CFSG.RankThree.PartTwo.Sec15
  CFSG.RankThree.PartTwo.Sec16 CFSG.RankThree.PartTwo.Late CFSG.GH74.GLS
  CFSG.RankThree.PartTwo.Sec17.HeadProof

theorem step174KbM_of_splitQ
    (h166 : Item166S17) (h146 : Item146S14)
    (h143 : Ronan148Q.Item143QS14)
    (hΩ : Step174KbOOmega) (hHJ : Step174KbOHJ) : Step174KbM :=
  step174KbM_of_O h166 h146 (step174KbO_of_three h146 (step174KbOThree_of_splitQ h143 hΩ hHJ))

end

section

open CFSG.RankThree.PartTwo.Sec17
open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
  CFSG.RankThree.PartTwo.Sec13 CFSG.RankThree.PartTwo.Sec14 CFSG.RankThree.PartTwo.Sec15
  CFSG.RankThree.PartTwo.Sec16 CFSG.RankThree.PartTwo.Late CFSG.GH74.GLS
  CFSG.RankThree.PartTwo.Sec17.HeadProof

theorem step174KbM_of_HJQ
    (h166 : Item166S17) (h146 : Item146S14)
    (h143 : Ronan148Q.Item143QS14)
    (h1514 : Item1514S17) (hMeets : Claim1715Meets) (hHJ : Step174KbOHJ) : Step174KbM :=
  step174KbM_of_splitQ h166 h146 h143 (step174KbOOmega_holds h146 h1514 hMeets) hHJ

end

section

open CFSG.RankThree.PartTwo.Sec17
open CFSG CFSG.RankThree CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec13
  CFSG.RankThree.PartTwo.Sec14 CFSG.RankThree.PartTwo.Sec15 CFSG.RankThree.PartTwo.Sec16

theorem step174KbM_of_res15Q (h166 : Item166S17) (h146 : Item146S14) (h45 : Sec4.Item4_5)
    (h143 : Ronan148Q.Item143QS14)
    (h1514 : Item1514S17) (hMeets : Claim1715Meets) : Step174KbM :=
  step174KbM_of_HJQ h166 h146 h143 h1514 hMeets (step174KbOHJ_holdsQ h45 h143 h146)

end

end CFSG.RankThree.PartTwo.Sec14.Ronan143Q
