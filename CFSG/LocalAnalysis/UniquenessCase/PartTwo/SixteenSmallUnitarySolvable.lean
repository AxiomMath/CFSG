module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenDefs
public import CFSG.LocalAnalysis.StandardType.GGStdSubSmallUnitDvdSmall

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Open Subgroup
open CFSG.ClassicalGroups.UnitaryFlag
open CFSG.LocalAnalysis.ComponentInitial
open CFSG.StandardType.SmallU
open CFSG.StandardType.TableBU

theorem s16low_isSolvable_of_isSUn_le_three {X : Type} [Group X] {n : ℕ}
    (hn : n ≤ 3) (hSU : IsSUn X n 1) :
    Group.IsSolvable X := by
  obtain ⟨K, hKf, hKfin, hKcard, ⟨e⟩⟩ := hSU
  let := hKf
  let := hKfin
  by_cases hn0 : n = 0
  · subst hn0
    have : Subsingleton ↥(StatedSU 0 (2 ^ 1) K) :=
      ⟨fun a b => Subtype.ext (Units.ext (Matrix.ext fun i => isEmptyElim i))⟩
    have : Subsingleton X :=
      ⟨fun x y => e.injective (Subsingleton.elim _ _)⟩
    exact Group.isSolvable_of_comm fun a b => Subsingleton.elim _ _
  · have hn1 : 1 ≤ n := Nat.one_le_iff_ne_zero.mpr hn0
    have hFD : UnitaryFieldData 2 1 K := unitaryFieldData_of_card hKcard (by norm_num)
    have : Group.IsSolvable ↥(unitarySU 2 1 K n) :=
      isSolvable_unitarySU_small hFD hn1 hn
    exact Group.isSolvable_of_isSolvable_injective (f := e.toMonoidHom) e.injective

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
