module

public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Defs
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.MinimalCounterexample
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section3.FirstCaseCountData
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section3.FirstCaseCountDataOfFirstCase
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Suzuki.IndexSevenToA7
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Suzuki.OddGraphReconstruction
import Mathlib.Tactic

namespace CFSG
end CFSG
open CFSG

/-!
# Suzuki's recognition theorem for the first case

This module owns `firstCase_isASeven`, the last Section-3 theorem.  The
statement is pinned verbatim from `GorensteinWalter/Section3/Basic.lean`;
the intended proof is Suzuki's §8 (`refs/suzuki-1959.tex`, pp. 269--270):
the first-case count gives `|G| = 2520`; the commuting graph on the 35
conjugates of the order-three subgroup `U` reconstructs seven intrinsic
edge-star classes, and a class stabilizer has index 7.  Its coset action then
embeds `G` into `A₇`.

`books/miller-2520.pdf` (G. A. Miller, Bull. AMS 28 (1922), 98--102) is the
same recognition theorem by elementary permutation-group methods; it is used
as a cross-check for the Sylow counting, not transcribed wholesale.
-/

noncomputable section

namespace CFSG.GorensteinWalter

universe u

/-- Suzuki's recognition theorem identifies the first-case group with
`A₇`.

The statement is pinned from `GorensteinWalter/Section3/Basic.lean`.  The
count package is constructed internally from the first-case hypotheses.
 -/
public theorem firstCase_isASeven
    {G : Type u} [Group G] [Finite G]
    (hmin : IsMinimalCounterexample G)
    (c : CentralizerSetup G)
    (hfirst : FirstCase c) :
    Nonempty (G ≃* alternatingGroup (Fin 7)) := by
  classical
  obtain ⟨d⟩ := firstCase_count_data_nonempty hmin c hfirst
  rcases firstCase_exists_indexSeven_subgroup_oddGraph hmin c hfirst d with
    ⟨H, hHindex⟩
  have hGcard : Nat.card G = 2 ^ 3 * 3 ^ 2 * 5 * 7 :=
    (firstCase_index_card_of_countData c d).2
  have hsimple : IsSimpleGroup G := minimalCounterexample_isSimple hmin
  exact mulEquiv_alternatingGroup_seven_of_index_seven hGcard hsimple H hHindex

end CFSG.GorensteinWalter
