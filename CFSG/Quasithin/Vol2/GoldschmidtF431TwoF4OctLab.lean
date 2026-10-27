module

public import CFSG.Quasithin.Vol2.GoldschmidtF431TwoF4OctDefs

public noncomputable section

namespace CFSG.Quasithin.H13.F431.TwoF4

open CFSG.LieType.Ree CFSG.LieType.Ree.ReeTag CFSG.LieType.Ree.LargeReeInvolution
  CFSG.LieType.Chevalley CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LocalAnalysis.EvenBN.TwoF4
  CFSG.LieType.Ree.LargeReeCover

set_option linter.unusedSectionVars false


variable {K : Type} [Field K] [Finite K] [CharP K F4.prime] {a : ℕ}

theorem fourCoordG_mem_rootV (hK : Nat.card K = 2 ^ (2 * a + 1)) {i : Idx} (hi : i.isSz = true)
    (b c : K) : fourCoordG a i.fourIdx b c ∈ rootV K a i := by
  have hx : ∀ n ∉ i.coords,
      (Function.update (Pi.single i.coord b) i.center.coord c : Fin 12 → K) n = 0 := by
    intro n hn
    have h1 : n ≠ i.coord := fun h => hn (by simp [Idx.coords, hi, h])
    have h2 : n ≠ i.center.coord := fun h => hn (by simp [Idx.coords, hi, h])
    rw [Function.update_of_ne h2, Pi.single_eq_of_ne h1]
  have hne : i.coord ≠ i.center.coord := by
    cases i <;> simp_all [Idx.isSz, Idx.coord, Idx.center]
  have hmem : sylowVec a K (Function.update (Pi.single i.coord b) i.center.coord c) ∈
      (rootV K a i : Set (ModGL F4.tag K)) := by
    rw [coe_rootV hK]
    exact ⟨_, hx, rfl⟩
  rwa [(sylowVec_eq_of_supp i hx).1 hi, Function.update_of_ne hne, Pi.single_eq_same,
    Function.update_self] at hmem

theorem rootV_eq_blockGroup_four (hK : Nat.card K = 2 ^ (2 * a + 1)) {i : Idx}
    (hi : i.isSz = true) : rootV K a i = largeReeBlockGroup K a (fourSet i.fourIdx) := by
  refine le_antisymm ?_ fun g hg => ?_
  · rw [rootV, Subgroup.closure_le]
    rintro _ ⟨u, rfl⟩
    rw [(rootElt_eq_coord i u).1 hi]
    exact fourCoordG_mem_block hK _ _ _
  · obtain ⟨b, c, rfl⟩ := exists_fourCoordG_eq hK _ hg
    exact fourCoordG_mem_rootV hK hi b c

theorem rootV_eq_blockGroup_two (hK : Nat.card K = 2 ^ (2 * a + 1)) {i : Idx}
    (hi : i.isLin = true) : rootV K a i = largeReeBlockGroup K a (twoSet i.twoIdx) := by
  refine le_antisymm ?_ fun g hg => ?_
  · rw [rootV, Subgroup.closure_le]
    rintro _ ⟨u, rfl⟩
    rw [(rootElt_eq_coord i u).2.2 hi]
    exact twoCoordG_mem_block hK _ _
  · obtain ⟨u, rfl⟩ := exists_twoCoordG_eq hK _ hg
    rw [← (rootElt_eq_coord i u).2.2 hi]
    exact Subgroup.subset_closure ⟨_, rfl⟩

theorem octRoot_eq_rootV (hK : Nat.card K = 2 ^ (2 * a + 1)) {k : ℤ} (h1 : 1 ≤ k) (h8 : k ≤ 8) :
    octRoot K a k = (rootV K a (octLab k)).subgroupOf (F4.reeGamma K a) := by
  unfold octRoot
  congr 1
  interval_cases k
  · exact (rootV_eq_blockGroup_four hK (i := .i1) rfl).symm
  · exact (rootV_eq_blockGroup_two hK (i := .i7) rfl).symm
  · exact (rootV_eq_blockGroup_four hK (i := .i6) rfl).symm
  · exact (rootV_eq_blockGroup_two hK (i := .i10) rfl).symm
  · exact (rootV_eq_blockGroup_four hK (i := .i5) rfl).symm
  · exact (rootV_eq_blockGroup_two hK (i := .i9) rfl).symm
  · exact (rootV_eq_blockGroup_four hK (i := .i4) rfl).symm
  · exact (rootV_eq_blockGroup_two hK (i := .i3) rfl).symm

end CFSG.Quasithin.H13.F431.TwoF4
