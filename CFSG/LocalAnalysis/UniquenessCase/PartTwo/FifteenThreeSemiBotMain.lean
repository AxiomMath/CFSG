module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.FifteenThreeSemiBotBridge
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.FifteenThreeSemiBotFix
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.FifteenThreeSemiBotIrr
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.FifteenThreeSemiBotPair
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.FifteenThreeSemiBotStruct

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22
open scoped commutatorElement Pointwise

section Concrete

variable {G : Type} [Group G] [Finite G] {D : Data G} {V₀ V L : Subgroup G}

theorem s15_semiBot_sSup_irr_star_of_shape (h1217 : R1217 D) (h : Hyp151 D V₀ V L)
    (hL : barSub V₀ V h.isElemAbelian L ≠ ⊥)
    (hsh : Odd (Nat.card ↥(⨆ m : D.M, barSub V₀ V h.isElemAbelian (conjSubgroup L (m : G)))) ∨
      ∃ K ∈ compBar D.M V₀ V h.isElemAbelian,
        (⨆ m : D.M, barSub V₀ V h.isElemAbelian (conjSubgroup L (m : G))) =
          ⨆ φ ∈ Mbar D.M V₀ V h.isElemAbelian, K.map (MulAut.conj φ).toMonoidHom) :
    sSup {I : Subgroup (vStar D.M V₀ V h.isElemAbelian L) |
      IsIrrOn (lStar D.M V₀ V h.isElemAbelian L) I ⊥} = ⊤ := by
  have hYne : (⨆ m : D.M, barSub V₀ V h.isElemAbelian (conjSubgroup L (m : G))) ≠ ⊥ := by
    intro hbot
    apply hL
    have hle := s15_semi_le_iSup_barSub h
    rw [hbot] at hle
    exact le_bot_iff.1 hle
  exact s15_semiBot_sSup_irr_star_of_irrSet h (s15_semiBot_imgTil_v1Sub_eq_fixV h1217 h hL)
    (h1217 V₀ V h.hyp125 _ hYne (s15_Infra_iSup_barSub_le h) (s15_Infra_iSup_barSub_normal h) hsh)

theorem s15_semiBot_sSup_irr_star (h1217 : R1217 D) (h : Hyp151 D V₀ V L)
    (hL : barSub V₀ V h.isElemAbelian L ≠ ⊥)
    (htr : ∃ φ ∈ Mbar D.M (v1Sub D.M V₀ V h.isElemAbelian L) V h.isElemAbelian,
      InducesTransvection φ (wStar D.M V₀ V h.isElemAbelian L)) :
    sSup {I : Subgroup (vStar D.M V₀ V h.isElemAbelian L) |
      IsIrrOn (lStar D.M V₀ V h.isElemAbelian L) I ⊥} = ⊤ := by
  rcases s15_semiBot_shape h with hsh | hmulti | ⟨hfit, hcomp⟩
  · exact s15_semiBot_sSup_irr_star_of_shape h1217 h hL hsh
  · obtain ⟨P, Q, hPL, hQL, hPQ, hQ, hWP, hWQ, hN⟩ :=
      s15_semiBot_exists_pair_of_multi h1217 h hmulti
    exact (s15_semiBot_false_of_pair h1217 h htr hPL hQL hPQ hQ hWP hWQ hN).elim
  · obtain ⟨P, Q, hPL, hQL, hPQ, hQ, hWP, hWQ, hN⟩ :=
      s15_semiBot_exists_pair_of_mixed h1217 h hfit hcomp
    exact (s15_semiBot_false_of_pair h1217 h htr hPL hQL hPQ hQ hWP hWQ hN).elim

end Concrete

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
