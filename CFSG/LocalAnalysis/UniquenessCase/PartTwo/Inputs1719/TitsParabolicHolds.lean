module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.ExceptionalParabolicsGen
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.X6TitsLattice
public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.K33ThreeCoverRanks
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.ExceptionalParabolics

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719

open CFSG.QuasithinUnique.Setup.X6 (titsSylowOvergroupLattice ne_top_of_card
  invariant_of_overgroup_lattice generation_of_overgroup_lattice)

theorem k_TitsParabolicGen_holds :
    K_TitsParabolicGen := by
  intro X _ _ h S hS
  obtain ⟨H, N, hS2048, hSH, hSN, hH, hN, hlat, -, -⟩ :=
    titsSylowOvergroupLattice X (h.reeTitsModel (by decide)).2 S hS
  refine ⟨N, H, hSN, hSH, by rw [hN, hS2048], by rw [hH, hS2048], ?_, fun α hα => ?_⟩
  · rw [sup_comm]
    exact generation_of_overgroup_lattice hH hN hSH hS2048 hlat
  · exact (invariant_of_overgroup_lattice hS2048 hH hN hSH hSN hlat hα).symm

theorem k_TitsParabolic_holds :
    K_TitsParabolic := by
  intro X _ _ h
  refine ⟨CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.pRank_three_eq_two_of_lieModel_Tits
    h, fun S hS => ?_⟩
  obtain ⟨H, N, -, hSH, hSN, hH, hN, -, hsolH, hsolN⟩ :=
    titsSylowOvergroupLattice X (h.reeTitsModel (by decide)).2 S hS
  obtain ⟨hHtop, hNtop⟩ := ne_top_of_card hH hN
  refine ⟨N, H, hSN, hSH, lt_top_iff_ne_top.2 hNtop, lt_top_iff_ne_top.2 hHtop, fun hNH => ?_,
    hN, hH, hsolN, hsolH⟩
  rw [hNH, hH] at hN
  omega

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719

end
