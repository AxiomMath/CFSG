module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.DataThree
public import CFSG.LocalAnalysis.UniquenessCase.UC6R
import CFSG.LocalAnalysis.UniquenessCase.UC6Dict
public import CFSG.LocalAnalysis.SectionRank.PRank

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.Three

open Subgroup CFSG.Open CFSG.LocalAnalysis.RankThreeUC CFSG.LocalAnalysis.UniquenessCase.UC22

variable {G : Type} [Group G] [Finite G]

theorem r6_1_dataOfSetup (hS : Standing G) (S : Setup G) : UC6.R6_1 (dataOfSetup hS S) := by
  rintro p ⟨hpA, Q, hw⟩ X hXM hXp hnc
  have hp := prime_of_mem_rankThreeSigmaA hpA
  ext N
  constructor
  · rintro ⟨hN, hXN⟩
    have h2 : 2 ≤ CFSG.Open.pRank p (N ⊓ S.M) :=
      (UC6.two_le_pRank_of_not_isCyclic hp.1 hp.2 hXp hnc).trans
        (CFSG.SectionRank.pRank_mono hp.1.one_lt (le_inf hXN hXM))
    exact (hN.2 _ S.witness.maxLocal.1 (hw.u2 N hN.1 h2)).symm
  · intro hN
    have hNM : N = S.M := hN
    subst hNM
    exact ⟨S.witness.maxLocal, hXM⟩

theorem r6_3_dataOfSetup (hS : Standing G) (hUC : rankThreeUC G) (hC : AGL81TheoremC G)
    (S : Setup G) : UC6.R6_3 (dataOfSetup hS S) := by
  intro r hr hr2 E hEM hEel hEcard hΓ
  have hE2 : 2 ≤ CFSG.Open.pRank r E := UC6.le_pRank_of_elemAbelian hr le_rfl hEel hEcard
  ext N
  constructor
  · rintro ⟨hN, hEN⟩
    have hle := hC hUC S.p S.hp S.P S.M S.witness r hr hr2 E hEM hEel.isPGroup hE2 hΓ N hN.1 hEN
    exact (hN.2 _ S.witness.maxLocal.1 hle).symm
  · intro hN
    have hNM : N = S.M := hN
    subst hNM
    exact ⟨S.witness.maxLocal, hEM⟩

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.Three
