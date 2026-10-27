module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.FifteenGapFourRank
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.FifteenGapFourFaith
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.FifteenThreeY
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC56R38M3

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22

variable {G : Type} [Group G] [Finite G]

theorem s15GapFour_pRank_Mbar_le_two (hAut : RAutRank153) (hAbs : RAbsIrr153)
    (hSimple : RSimple153) (D : Data G) (h1217 : R1217 D) {V₀ V L K₀ : Subgroup G}
    (h : Hyp151 D V₀ V L) (hV : IsElemAbelian 2 V) (hshape : s15Shape D V₀ V hV L K₀)
    (hperf : s15KNatPerf ↥(barSub V₀ V hV K₀) (barSub (v1Sub D.M V₀ V hV L) V hV K₀)
      (commSub ⊤ (barSub (v1Sub D.M V₀ V hV L) V hV K₀)))
    (hL2 : IsL3 ↥(barSub V₀ V hV K₀) 1 ∨ UC22.IsAlt ↥(barSub V₀ V hV K₀) 5)
    (hrs : s15Rs D V₀ V hV L K₀ = 2) {q : ℕ} (hq : q.Prime) (hq2 : q ≠ 2) :
    CFSG.Open.pRank q (Mbar D.M V₀ V hV) ≤ 2 := by
  have hcard : Set.ncard {X : Subgroup (MulAut (Vtil V₀ V hV)) |
      ∃ φ ∈ Mbar D.M V₀ V hV, X = (barSub V₀ V hV K₀).map (MulAut.conj φ).toMonoidHom} ≤ 2 :=
    (s15GapFour_ncard_conj_le (Mbar D.M V₀ V hV) (barSub V₀ V hV K₀)
      (barSub V₀ V hV L)).trans (le_of_eq hrs)
  have hZ : Subgroup.center ↥(barSub V₀ V hV K₀) = ⊥ := (hSimple _ _ _ _ hperf).2
  exact s15GapFour_pRank_le_two hAut hL2 hZ hcard
    (fun y hy hcen => s15GapFour_eq_one_of_centralizes hAbs D h1217 h hV hshape hperf hy hcen)
    hq hq2

theorem s15GapFour_pRank_le_three_of_small (hAut : RAutRank153) (hAbs : RAbsIrr153)
    (hSimple : RSimple153) (D : Data G) (h61 : UC6.R6_1 D) (h127 : R127 D) (h1217 : R1217 D)
    {V₀ V L K₀ : Subgroup G} (h : Hyp151 D V₀ V L) (hV : IsElemAbelian 2 V)
    (hshape : s15Shape D V₀ V hV L K₀)
    (hperf : s15KNatPerf ↥(barSub V₀ V hV K₀) (barSub (v1Sub D.M V₀ V hV L) V hV K₀)
      (commSub ⊤ (barSub (v1Sub D.M V₀ V hV L) V hV K₀)))
    (hL2 : IsL3 ↥(barSub V₀ V hV K₀) 1 ∨ UC22.IsAlt ↥(barSub V₀ V hV K₀) 5)
    (hrs : s15Rs D V₀ V hV L K₀ = 2) (hsmall : Nat.card V₀ ≤ 4) {q : ℕ} (hq : q ∈ D.sig) :
    CFSG.Open.pRank q D.M ≤ 3 := by
  obtain ⟨hqprime, hq2⟩ := D.sig_prime q hq
  have hadd := r38m3_pRank_le_add hV h.hyp125.pairFacts hqprime
  have hC : CFSG.Open.pRank q (F11.CTilde D.M V₀ V) ≤ 1 :=
    uc22p22q_pRank_ctilde_le_one D h61 (Hyp125.hyp11 h127 h.hyp125) hsmall hq
  have hMb := s15GapFour_pRank_Mbar_le_two hAut hAbs hSimple D h1217 h hV hshape hperf hL2 hrs
    hqprime hq2
  omega

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
