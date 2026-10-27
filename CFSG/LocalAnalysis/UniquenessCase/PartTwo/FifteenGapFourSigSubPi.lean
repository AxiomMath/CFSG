module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.FifteenGapFourConj
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.FifteenGapFourCent
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.FifteenGapFourFaith
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.FifteenThreeIE
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.FifteenThreeY
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.FifteenThreeS

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22

variable {G : Type} [Group G] [Finite G]

theorem s15ThreeSigSubPiGap_holds (D : Data G) (hAut : RAutRank153) (hAbs : RAbsIrr153)
    (hSimple : RSimple153) (h127 : R127 D) (h1111 : R1111_153 D) (h1217 : R1217 D) :
    S15ThreeSigSubPiGap D := by
  intro _ _ _ _ V₀ V L K₀ h hV hshape hperf hL2 hrs _ _ _ _ q hq hqK
  exfalso
  have hqprime : q.Prime := (D.sig_prime q hq).1
  have hq2 : q ≠ 2 := (D.sig_prime q hq).2
  have hqodd : Odd q := hqprime.odd_of_ne_two hq2
  have hpf := h.hyp125.pairFacts
  have hMs : D.M ≤ stabTil V₀ V := le_stabTil hpf.le_normalizer hpf.le_normalizer₀
  haveI := s15_Three_cTilde_normal (D := D) hV hMs
  have hH11 : F11.Hyp11 D V₀ V := Hyp125.hyp11 h127 h.hyp125
  have hrk : 1 ≤ CFSG.Open.pRank q (Mbar D.M V₀ V hV) := by
    have h1 := h1111 V₀ V hH11 q hq
    have h2 := s15_Three_pRank_MBar11 hV hMs q
    rw [CFSG.SectionRank.pRank_eq_pRank_top_subgroup]
    omega
  obtain ⟨y, hyM, hyord⟩ := CFSG.GroupTheory.exists_mem_orderOf_eq_of_one_le_pRank hqprime hrk
  have hyq : y ^ q = 1 := hyord ▸ pow_orderOf_eq_one y
  have hy1 : y ≠ 1 := by
    intro h1
    rw [h1, orderOf_one] at hyord
    exact hqprime.ne_one hyord.symm
  have hcard : Set.ncard {X : Subgroup (MulAut (Vtil V₀ V hV)) |
      ∃ φ ∈ Mbar D.M V₀ V hV, X = (barSub V₀ V hV K₀).map (MulAut.conj φ).toMonoidHom} ≤ 2 :=
    (s15GapFour_ncard_conj_le (Mbar D.M V₀ V hV) (barSub V₀ V hV K₀)
      (barSub V₀ V hV L)).trans (le_of_eq hrs)
  have hZ : Subgroup.center ↥(barSub V₀ V hV K₀) = ⊥ := (hSimple _ _ _ _ hperf).2
  have hcen : ∀ x ∈ Mbar D.M V₀ V hV,
      x * y * x⁻¹ ∈ centralizer (barSub V₀ V hV K₀ : Set (MulAut (Vtil V₀ V hV))) := by
    intro x hx
    have hxy : x * y * x⁻¹ ∈ Mbar D.M V₀ V hV :=
      (Mbar D.M V₀ V hV).mul_mem ((Mbar D.M V₀ V hV).mul_mem hx hyM)
        ((Mbar D.M V₀ V hV).inv_mem hx)
    have hxq : (x * y * x⁻¹) ^ q = 1 := by rw [conj_pow, hyq]; simp
    have hnorm : x * y * x⁻¹ ∈ normalizer (barSub V₀ V hV K₀ : Set (MulAut (Vtil V₀ V hV))) :=
      s15GapFour_mem_normalizer_of_odd (Mbar D.M V₀ V hV) (barSub V₀ V hV K₀) hcard hxy hqodd hxq
    exact s15GapFour_centralizes_of_normalizes hAut hL2 hZ hnorm hqprime hqK hxq
  exact hy1 (s15GapFour_eq_one_of_centralizes hAbs D h1217 h hV hshape hperf hyM hcen)

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
