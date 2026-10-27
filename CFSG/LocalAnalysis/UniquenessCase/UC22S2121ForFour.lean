module

public import CFSG.LocalAnalysis.UniquenessCase.UC22S2121ForCore
public import CFSG.LocalAnalysis.UniquenessCase.UC22InE229S13xpZ
public import CFSG.LocalAnalysis.UniquenessCase.UC22R847G4

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

open CFSG.Open
open CFSG.Yardstones.Mf4cdcdf2e013 (Standing4 Setup4 PartIAt)
open CFSG.LocalAnalysis.UniquenessCase.PartOne.Section7 (StronglyEmbeddedFive BadNoStrongThree)

variable {G : Type} [Group G] [Finite G]

private theorem r847E4_of_r847G4 {D : Data G} (h : R847G4 D) (he : 3 < evenRank G) :
    R847E4 D := by
  intro Y hY X hXY q hq hq2 hXq p hp hcase
  rcases h Y hY X hXY q hq hq2 hXq p hp hcase with h1 | ⟨_, _, _, _, _, he3, _⟩ |
      ⟨_, _, _, _, _, he3, _⟩
  · exact h1
  · omega
  · omega

private theorem evenRank_three_of_hyp2120For
    (hThin : PartTwo.ThinList13)
    (hCyc : CFSG.RankThree.PartTwo.Sec11.CyclicSylowThreeOutAbelian) {D : Data G}
    {Ch : Choice2011 G} (hSig : UC6S846.SigmaStd D) (h61 : UC6.R6_1 D)
    (h4 : ∀ p ∈ D.sig, 4 ≤ CFSG.Open.pRank p D.M) (h136 : R136bFour D) (h847 : R847Four D)
    (h211 : S21_1 D Ch) (h216 : S21_16 D Ch) (h218 : S21_18 D Ch) (h219 : S21_9N D Ch)
    (h19 : S21_19 D Ch) (h1930 : H1930 D) (c : Ctx21 D Ch) {L X : Subgroup G}
    (hX : X ∈ calB1 D.T D.M L) (hXM : X ≤ D.M) (hXne : X ≠ ⊥) (hH : Hyp2120For D X) :
    CFSG.Open.evenRank G = 3 := by
  by_contra he
  obtain ⟨p, hp⟩ := hSig.nonempty
  have hH0 := hyp2120_withBot h61 c hX hH
  have hsig := uc22s13xe_sig_eq_sig1 hSig h61 c.withBot hH0
  have hH131 :=
    uc22s13xe_hyp131 hThin hCyc hSig h61 h847 h211 h216 h218 h219 h19 h1930 c.withBot hH0 he hsig
  have h3 := h136 hsig hH131 p hp X
    (case136b_of_hyp2120For hThin hCyc hSig hH131.thinOrU3 hH131.normal hsig hX hXM hXne hH hp)
  have h4p := h4 p hp
  omega

theorem s21_21For_setup4_of_r7_8R3p3
    (hSE : StronglyEmbeddedFive) (hB3 : BadNoStrongThree)
    (hThin : PartTwo.ThinList13)
    (hCyc : CFSG.RankThree.PartTwo.Sec11.CyclicSylowThreeOutAbelian) (hS : Standing4 G)
    (hU : CFSG.Open.uniqueFourUnique G) (S : Setup4 G) (hσ : S.InMSigma) (hPart : PartIAt S.M)
    {Ch : Choice2011 G} (h78 : R7_8R3p3 (UC6.dataOfSetup4 hS hU S))
    (h846 : F08.R846 (UC6.dataOfSetup4 hS hU S)) (h847 : R847G4 (UC6.dataOfSetup4 hS hU S))
    (h211 : S21_1 (UC6.dataOfSetup4 hS hU S) Ch) (h216 : S21_16 (UC6.dataOfSetup4 hS hU S) Ch)
    (h218 : S21_18 (UC6.dataOfSetup4 hS hU S) Ch) (h219 : S21_9N (UC6.dataOfSetup4 hS hU S) Ch)
    (h19 : S21_19 (UC6.dataOfSetup4 hS hU S) Ch) : S21_21For (UC6.dataOfSetup4 hS hU S) Ch := by
  have he : 3 < CFSG.Open.evenRank G := by
    have := hS.rank
    omega
  have hE4 := r847E4_of_r847G4 h847 he
  intro h1930 c _ _ X hX hXM hXne hH _ _
  exact absurd (evenRank_three_of_hyp2120For hThin hCyc (UC6S846.sigmaStd_dataOfSetup4 hS hU S)
    (UC6.r6_1_dataOfSetup4 hS hU S) (fun _ hp => UC6.four_le_pRank_of_sigma hp)
    (r136bFour_setup4_of_r7_8R3p3 hSE hB3 hThin hCyc hS hU S hσ hPart h78 h846
      (r847_of_r847E4 hE4))
    (r847Four_of_r847E4 hE4) h211 h216 h218 h219 h19 h1930 c hX hXM hXne hH) (by omega)

end CFSG.LocalAnalysis.UniquenessCase.UC22
