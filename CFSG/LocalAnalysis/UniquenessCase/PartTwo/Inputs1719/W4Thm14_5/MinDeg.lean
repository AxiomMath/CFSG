module

public import CFSG.LocalAnalysis.UniquenessCase.UC22Defs2
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.DefsModule
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.KMinDegLow.LeviSec
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.KMinDegLow.Rep
public import CFSG.LocalAnalysis.UniquenessCase.UC22S20

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.Thm14_5

open CFSG.LocalAnalysis.UniquenessCase.UC22 CFSG.LocalAnalysis.UniquenessCase.UC22.MinDegLow
open CFSG.RankThree.PartTwo.Sec4.Ronan148V

theorem lt_dMinDeg_of_nParam_of
    (hSz : ∀ (X : Type) [Group X] (f : ℕ), IsSz X f → Nat.card X = CFSG.Open.ordSuzuki (2 ^ f))
    {G : Type} [Group G] [Finite G] {L P : Subgroup G} (hL : CFSG.Open.IsQuasisimple ↥L)
    (hPL : P ≤ L) {n : ℕ} (hN : NParam (Hinf P) n) (hn : 2 < n) :
    n + 1 < PartTwo.dMinDeg ↥L := by
  obtain ⟨T, _, _, hTL, hT⟩ := exists_leviData_sec hSz hPL hN hn
  have := hT.simple
  have := nontrivial_of_isQuasisimple hL
  suffices h : n + 2 ≤ PartTwo.dMinDeg ↥L by omega
  apply le_dMinDeg
  intro d f hf
  have hnot : ¬ IsSolvable T := not_isSolvable_of_isSimpleGroup hT.nonab
  have hTL' : IsSec T ↥L :=
    isSec_trans hTL (isSec_of_surjective (QuotientGroup.mk' (CFSG.pCore 2 ↥L))
      (QuotientGroup.mk'_surjective (CFSG.pCore 2 ↥L)))
  have hTS : IsSec T (↥L ⧸ Subgroup.center ↥L) :=
    hTL'.quotient_of_isSolvable hnot
      (Group.isSolvable_of_comm fun a b => Subtype.ext (Subgroup.mem_center_iff.mp b.2 a))
  obtain ⟨m, hm2, -, ⟨t, ht⟩, -⟩ := hT.bound
  obtain ⟨s, hs⟩ := exists_orderOf_eq_of_isSec hTS t
  obtain ⟨g, hg⟩ := exists_orderOf_eq_of_quotient hL (QuotientGroup.mk' (Subgroup.center ↥L))
    (QuotientGroup.mk'_surjective _) (center_quotient_center_eq_bot hL) f hf s
  have hd := ht d g (hg.trans hs)
  nlinarith

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.Thm14_5
