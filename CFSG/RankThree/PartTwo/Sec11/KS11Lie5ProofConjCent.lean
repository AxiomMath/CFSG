module

public import CFSG.RankThree.PartTwo.Sec11.KS11Lie5ProofConjTup
public import CFSG.RankThree.PartOne.KE.StabGeneral
public import CFSG.RankThree.PartOne.KGD.D4A2Frame
public import CFSG.LieType.AlgebraicGroups.E6GraphCentralizerLangCurves

public section

set_option linter.unusedSectionVars false

namespace CFSG.RankThree.PartTwo.Sec11.KS11Lie5Proof

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.RankThree.Chevalley
  CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  CFSG.RankThree.E6 CFSG.LieType.AlgebraicGroups CFSG.RankThree.PartOne.KE
  CFSG.RankThree.PartOne.KF4 CFSG.RankThree.PartOne.KGD
open scoped MatrixGroups

theorem pow_three_of_orderOf {G : Type*} [Monoid G] {ζ : G} (hζ : orderOf ζ = 3) : ζ ^ 3 = 1 := by
  rw [← hζ]
  exact pow_orderOf_eq_one ζ

theorem chainRoot_gA : ∀ i j : Fin 3,
    ∑ k : Fin TwistTag.D4.tag.rank, (((chainRoot d4ChainA2 i j : Fin Tag.D4.rank → ℤ) k : ℤ) :
      ZMod 3) * gA k = 0 := by
  decide +kernel

theorem sigmaB_gB : ∀ k : Fin 24, (k = 0 ∨ k = 4 ∨ k = 1 ∨ k = 6 ∨ k = 3 ∨ k = 10) →
    ∑ j : Fin TwistTag.D4.tag.rank, ((d4RootVec k j : ℤ) : ZMod 3) * gB j = 0 := by
  decide +kernel


theorem isRoot_of_mem_sigmaA {α : Fin TwistTag.D4.tag.rank → ℤ} (hα : α ∈ sigmaA) :
    IsRoot TwistTag.D4.tag α := by
  obtain ⟨i, j, hij, rfl⟩ := hα
  exact (chainRootA2_mem_parabolicRoots hij).1

theorem neg_mem_sigmaA {α : Fin TwistTag.D4.tag.rank → ℤ} (hα : α ∈ sigmaA) : -α ∈ sigmaA := by
  obtain ⟨i, j, hij, rfl⟩ := hα
  exact ⟨j, i, hij.symm, (chainRoot_swap d4ChainA2 i j).symm⟩

theorem isRoot_of_mem_sigmaB {α : Fin TwistTag.D4.tag.rank → ℤ} (hα : α ∈ sigmaB) :
    IsRoot TwistTag.D4.tag α := by
  obtain ⟨k, -, rfl⟩ := hα
  exact isRoot_d4RootVec k

theorem neg_mem_sigmaB {α : Fin TwistTag.D4.tag.rank → ℤ} (hα : α ∈ sigmaB) : -α ∈ sigmaB := by
  obtain ⟨k, hk, rfl⟩ := hα
  have hneg : ∀ k : Fin 24, (k = 0 ∨ k = 4 ∨ k = 1 ∨ k = 6 ∨ k = 3 ∨ k = 10) →
      ∃ k' : Fin 24, (k' = 0 ∨ k' = 4 ∨ k' = 1 ∨ k' = 6 ∨ k' = 3 ∨ k' = 10) ∧
        -d4RootVec k = d4RootVec k' := by decide +kernel
  obtain ⟨k', hk', h⟩ := hneg k hk
  exact ⟨k', hk', h⟩

variable {L : Type} [Field L] {ζ : Lˣ}

theorem rootChar_gA_of_mem_sigmaA (hζ : ζ ^ 3 = 1) {α : Fin TwistTag.D4.tag.rank → ℤ}
    (hα : α ∈ sigmaA) : rootChar (tup ζ gA) α = 1 := by
  obtain ⟨i, j, -, rfl⟩ := hα
  refine (rootChar_tup hζ gA _).trans ?_
  exact (congrArg (fun z : ZMod 3 => ζ ^ z.val) (chainRoot_gA i j)).trans (by simp)

theorem rootChar_gB_of_mem_sigmaB (hζ : ζ ^ 3 = 1) {α : Fin TwistTag.D4.tag.rank → ℤ}
    (hα : α ∈ sigmaB) : rootChar (tup ζ gB) α = 1 := by
  obtain ⟨k, hk, rfl⟩ := hα
  refine (rootChar_tup hζ gB _).trans ?_
  exact (congrArg (fun z : ZMod 3 => ζ ^ z.val) (sigmaB_gB k hk)).trans (by simp)

theorem rootSubgroup_le_centralizer {a : Fin TwistTag.D4.tag.rank → Lˣ}
    {α : Fin TwistTag.D4.tag.rank → ℤ} (hα : IsRoot TwistTag.D4.tag α) (h1 : rootChar a α = 1) :
    rootSubgroup TwistTag.D4.tag L α ≤
      Subgroup.centralizer {rootDiagUnit TwistTag.D4.tag a} := by
  refine (Subgroup.closure_le _).2 ?_
  rintro _ ⟨c, rfl⟩
  rw [SetLike.mem_coe, Subgroup.mem_centralizer_singleton_iff]
  have h := rootDiagUnit_conj_pinnedX a hα c
  rw [h1, Units.val_one, one_mul, mul_inv_eq_iff_eq_mul] at h
  exact h.symm

theorem torusGroup_le_centralizer (a : Fin TwistTag.D4.tag.rank → Lˣ) :
    torusGroup TwistTag.D4.tag L ≤ Subgroup.centralizer {rootDiagUnit TwistTag.D4.tag a} := by
  intro h hh
  rw [Subgroup.mem_centralizer_singleton_iff]
  exact (rootDiagUnit_mul_comm_of_mem_torusGroup a hh).symm

theorem torusGroup_le_adjointGroup_D4 :
    torusGroup TwistTag.D4.tag L ≤ adjointGroup TwistTag.D4.tag L :=
  (Subgroup.closure_le _).2 (by rintro _ ⟨⟨i, t⟩, rfl⟩; exact torusElt_mem_adjointGroup i t)

theorem graphCentralizer_gA (hζ : orderOf ζ = 3) :
    graphCentralizer TwistTag.D4.tag L (rootDiagUnit TwistTag.D4.tag (tup ζ gA)) =
      torusGroup TwistTag.D4.tag L ⊔ rootSpan TwistTag.D4.tag L sigmaA := by
  refine le_antisymm ?_ ?_
  · exact toralCentralizer_le_sup_rootSpan_of_stab (stab_subset_closure_A hζ)
      (fun α hα => isRoot_of_mem_sigmaA hα) (fun α hα => neg_mem_sigmaA hα)
      (rootCharKernel_tup_gA_subset hζ)
  · refine sup_le (le_inf torusGroup_le_adjointGroup_D4 (torusGroup_le_centralizer _))
      (le_inf (rootSpan_le_adjointGroup _ _) ?_)
    exact iSup₂_le fun α hα => rootSubgroup_le_centralizer (isRoot_of_mem_sigmaA hα)
      (rootChar_gA_of_mem_sigmaA (pow_three_of_orderOf hζ) hα)

theorem graphCentralizer_gB (hζ : orderOf ζ = 3) :
    graphCentralizer TwistTag.D4.tag L (rootDiagUnit TwistTag.D4.tag (tup ζ gB)) =
      torusGroup TwistTag.D4.tag L ⊔ rootSpan TwistTag.D4.tag L sigmaB := by
  refine le_antisymm ?_ ?_
  · exact toralCentralizer_le_sup_rootSpan_of_stab (stab_subset_closure_B hζ)
      (fun α hα => isRoot_of_mem_sigmaB hα) (fun α hα => neg_mem_sigmaB hα)
      (rootCharKernel_tup_gB_subset hζ)
  · refine sup_le (le_inf torusGroup_le_adjointGroup_D4 (torusGroup_le_centralizer _))
      (le_inf (rootSpan_le_adjointGroup _ _) ?_)
    exact iSup₂_le fun α hα => rootSubgroup_le_centralizer (isRoot_of_mem_sigmaB hα)
      (rootChar_gB_of_mem_sigmaB (pow_three_of_orderOf hζ) hα)

theorem isPointIrreducible_gA [IsAlgClosed L] (hζ : orderOf ζ = 3) :
    IsPointIrreducible L (transportPoints (modGLPoint TwistTag.D4.tag L)
      (graphCentralizer TwistTag.D4.tag L (rootDiagUnit TwistTag.D4.tag (tup ζ gA)))) := by
  rw [graphCentralizer_gA hζ]
  exact isPointIrreducible_torusGroup_sup_rootSpan fun α hα => isRoot_of_mem_sigmaA hα

theorem isPointIrreducible_gB [IsAlgClosed L] (hζ : orderOf ζ = 3) :
    IsPointIrreducible L (transportPoints (modGLPoint TwistTag.D4.tag L)
      (graphCentralizer TwistTag.D4.tag L (rootDiagUnit TwistTag.D4.tag (tup ζ gB)))) := by
  rw [graphCentralizer_gB hζ]
  exact isPointIrreducible_torusGroup_sup_rootSpan fun α hα => isRoot_of_mem_sigmaB hα

end CFSG.RankThree.PartTwo.Sec11.KS11Lie5Proof
