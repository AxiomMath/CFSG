module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC23NeDefs
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.DefsWeakClosure
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenDefsB

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup

variable {G : Type} [Group G] [Finite G]

structure C23NeO2 (M V₀ V N₁ N₂ Y : Subgroup G) (g : G) : Prop where
  pair : C23NePair M V₀ V N₁ N₂ Y
  pair' : C23NePair (conjSubgroup M g) (conjSubgroup V₀ g) (conjSubgroup V g)
    (conjSubgroup N₁ g) (conjSubgroup N₂ g) (conjSubgroup Y g)
  notLe : ¬ conjSubgroup V g ≤ M
  notLe' : ¬ V ≤ conjSubgroup M g
  mU : E3.mQuot V (conjSubgroup M g) ≤ 2
  mB : E3.mQuot (conjSubgroup V g) M ≤ 2

theorem C23NeO2.swap {M V₀ V N₁ N₂ Y : Subgroup G} {g : G} (h : C23NeO2 M V₀ V N₁ N₂ Y g) :
    C23NeO2 (conjSubgroup M g) (conjSubgroup V₀ g) (conjSubgroup V g) (conjSubgroup N₁ g)
      (conjSubgroup N₂ g) (conjSubgroup Y g) g⁻¹ where
  pair := h.pair'
  pair' := by simpa only [conjSubgroup_conjSubgroup_inv] using h.pair
  notLe := by simpa only [conjSubgroup_conjSubgroup_inv] using h.notLe'
  notLe' := by simpa only [conjSubgroup_conjSubgroup_inv] using h.notLe
  mU := by simpa only [conjSubgroup_conjSubgroup_inv] using h.mB
  mB := by simpa only [conjSubgroup_conjSubgroup_inv] using h.mU

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
