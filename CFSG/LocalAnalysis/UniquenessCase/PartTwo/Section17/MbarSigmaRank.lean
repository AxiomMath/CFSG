module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.FifteenThreeS
public import CFSG.LocalAnalysis.UniquenessCase.UC22P22qm
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.TwelveShort

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.S17

open Subgroup CFSG.Open CFSG.LocalAnalysis.UniquenessCase.UC22
open CFSG.LocalAnalysis.UniquenessCase.PartTwo

variable {G : Type} [Group G] [Finite G]

theorem two_le_pRank_mbar_of_mem_sig {D : Data G} {V₀ V : Subgroup G} (hV : Hyp125 D V₀ V)
    (hx : DataExt D) (h61 : CFSG.LocalAnalysis.UniquenessCase.UC6.R6_1 D) (h127 : R127 D)
    (hcard4 : Nat.card V₀ ≤ 4) {p : ℕ} (hp : p ∈ D.sig) :
    2 ≤ CFSG.Open.pRank p (Mbar D.M V₀ V hV.isElemAbelian) := by
  have hpair := hV.pairFacts
  have hMs : D.M ≤ stabTil V₀ V := le_stabTil hpair.le_normalizer hpair.le_normalizer₀
  have := s15_Three_cTilde_normal (D := D) hV.isElemAbelian hMs
  obtain ⟨-, hle, -⟩ := uc22p22q_r115_of D hx h61 V₀ V (Hyp125.hyp11 h127 hV) hcard4 p hp
  have hle' : CFSG.Open.pRank p D.M - 1 ≤
      CFSG.Open.pRank p (⊤ : Subgroup (F11.MBar11 D.M V₀ V)) := hle
  have hEq := s15_Three_pRank_MBar11 (D := D) (V₀ := V₀) (V := V) hV.isElemAbelian hMs (p := p)
  have h3 : 3 ≤ CFSG.Open.pRank p D.M := hx.three_le p hp
  rw [CFSG.SectionRank.pRank_eq_pRank_top_subgroup (Mbar D.M V₀ V hV.isElemAbelian), ← hEq]
  omega

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.S17
