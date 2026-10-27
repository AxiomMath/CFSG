module

public import CFSG.RankThree.PartOne.KGD.D4T36Torus
public import CFSG.Assembly.ComponentTypeDefs
public import CFSG.Assembly.RankThreeEvenDefs

public section

namespace CFSG.RankThree.PartOne.TCX.Tri

open Subgroup CFSG CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
open CFSG.RankThree.Chevalley CFSG.RankThree.PartOne.KGD
open CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
open scoped Matrix

section Matrices

@[expose] def triU2 : Matrix (Fin TwistTag.D4.tag.rank) (Fin TwistTag.D4.tag.rank) ℤ :=
  Matrix.of fun i j => if TwistTag.D4.perm i = j then -1 else 0

@[expose] def triX2 : Matrix (Fin TwistTag.D4.tag.rank) (Fin TwistTag.D4.tag.rank) ℤ :=
  !![-2, 2, 0, -2; -2, -2, 0, 2; 0, 0, -2, 0; 2, -2, 0, -2]

theorem triU2_pow : triU2 ^ 6 = 1 := by decide +kernel

theorem triU2_adj : (triU2 - 1) * triX2 = (4 : ℤ) • 1 := by decide +kernel

@[expose] def triAinv : Matrix (Fin TwistTag.D4.tag.rank) (Fin TwistTag.D4.tag.rank) ℤ :=
  !![-1, 0, 0, 1; 0, 0, -1, 1; -1, 1, -1, 1; -1, 0, 0, 0]

@[expose] def triU36 (ε : ℤ) : Matrix (Fin TwistTag.D4.tag.rank) (Fin TwistTag.D4.tag.rank) ℤ :=
  ε • triAinv

@[expose] def triX3 : Matrix (Fin TwistTag.D4.tag.rank) (Fin TwistTag.D4.tag.rank) ℤ :=
  !![-3, 0, 0, -3; 0, -6, 3, -3; 3, -3, -3, -3; 3, 0, 0, -6]

theorem triU36_mul {ε : ℤ} (hε : ε = 1 ∨ ε = -1) : triU36 ε * d4T36M ε = 1 := by
  rcases hε with rfl | rfl <;> simp only [triU36, d4T36M] <;> decide +kernel

theorem triU36_pow {ε : ℤ} (hε : ε = 1 ∨ ε = -1) : triU36 ε ^ 6 = 1 := by
  rcases hε with rfl | rfl <;> simp only [triU36] <;> decide +kernel

theorem triU3_adj : (triU36 1 - 1) * triX3 = (9 : ℤ) • 1 := by
  simp only [triU36]
  decide +kernel

theorem triU6_adj : (triU36 (-1) - 1) * triAinv = (1 : ℤ) • 1 := by
  simp only [triU36]
  decide +kernel

end Matrices

section Hyp

theorem triU2_mulVec (v : Fin TwistTag.D4.tag.rank → ℤ) (i : Fin TwistTag.D4.tag.rank) :
    (triU2 *ᵥ v) i = -v (TwistTag.D4.perm i) := by
  simp [triU2, Matrix.mulVec, dotProduct, Finset.sum_ite_eq]

theorem triU2_hU (v : Fin TwistTag.D4.tag.rank → ℤ) :
    permLattice TwistTag.D4.perm.symm (trialityOppositionWeyl⁻¹ • v) = triU2 *ᵥ v := by
  have hneg : trialityOppositionWeyl⁻¹ • v = -v := by
    have h := trialityOppositionWeyl_smul (trialityOppositionWeyl⁻¹ • v)
    rw [smul_inv_smul] at h
    have h2 := congrArg (fun z => -z) h
    simpa using h2.symm
  rw [hneg]
  ext i
  rw [triU2_mulVec]
  simp [permLattice]

theorem triU36_hU {ε : ℤ} (hε : ε = 1 ∨ ε = -1) {w : WeylGroup TwistTag.D4.tag}
    (hw : ∀ x, w • x = d4T36M ε *ᵥ permLattice TwistTag.D4.perm.symm x)
    (v : Fin TwistTag.D4.tag.rank → ℤ) :
    permLattice TwistTag.D4.perm.symm (w⁻¹ • v) = triU36 ε *ᵥ v := by
  have h1 : w • (w⁻¹ • v) = v := smul_inv_smul w v
  rw [hw] at h1
  set y := permLattice TwistTag.D4.perm.symm (w⁻¹ • v) with hy
  calc y = (triU36 ε * d4T36M ε) *ᵥ y := by rw [triU36_mul hε, Matrix.one_mulVec]
    _ = triU36 ε *ᵥ (d4T36M ε *ᵥ y) := by rw [Matrix.mulVec_mulVec]
    _ = triU36 ε *ᵥ v := by rw [h1]

end Hyp

end CFSG.RankThree.PartOne.TCX.Tri
