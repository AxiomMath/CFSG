module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC11E3V1SixFinBT
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC11E3V1SixFinBV1
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC11E3V1SixFinBV2
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC11E3V1SixFinBV3

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Quasithin.G6 Equiv

theorem sixGhatOf_injective {c d : s1611e3_SixCode} (hc : s1611e3_sixCodeValid c)
    (hd : s1611e3_sixCodeValid d) (h : s1611e3_sixGhatOf c = s1611e3_sixGhatOf d) : c = d :=
  s1611e3_sixGhatOf_injective hc hd h

theorem sixVNat_act_tab {c : s1611e3_SixCode} (hc : s1611e3_sixCodeValid c)
    (u : SixE6 × SixE6) :
    s1611e3_sixVNat (s1611e3_sixGhatOf c u) = sixTabAct (sixCodeTab c) (s1611e3_sixVNat u) := by
  rw [s1611e3_sixVNat_act c u hc, sixCodeAct_eq_tab]

theorem exists_of_mem_sixVecs {m : Nat} (hm : m ∈ sixVecs) :
    ∃ u : SixE6 × SixE6, s1611e3_sixVNat u = m :=
  s1611e3_exists_of_mem_sixVecs hm

theorem testBit_sixProf (K : Bool) (t m : Nat) :
    (sixProf K t).testBit m = (decide (m ∈ sixVecs) && sixFixes K t m) :=
  s1611e3_testBit_sixProf K t m

theorem testBit_sixInvAdj {i k : Nat} (hi : i < 111) (hk : k < 111) :
    (sixInvAdj.getD i 0).testBit k =
      sixComm (sixInvTabs.getD i 0) (sixInvTabs.getD k 0) :=
  s1611e3_testBit_sixInvAdj hi hk

theorem sixKMem_iff {K : Subgroup (SixE6 × SixE6)} {Kb : Bool}
    (hK : (Kb = false ∧ K = ⊥) ∨ (Kb = true ∧ K = sixDiag)) (x : SixE6 × SixE6) :
    sixKMem Kb (s1611e3_sixVNat x) = true ↔ x ∈ K :=
  s1611e3_sixKMem_iff hK x

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
