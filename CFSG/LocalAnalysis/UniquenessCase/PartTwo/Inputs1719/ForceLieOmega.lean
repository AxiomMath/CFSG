module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.ForceLieTools
public import CFSG.Open.StatedDefs
public import CFSG.HardMathSupport.Foote.E27.Q2OrthMinus
public import CFSG.HardMathSupport.Foote.E27.Q2OrthModel
public import CFSG.HardMathSupport.Foote.E27.TableMat
public import Certificates.Data.E27Q2O

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719

open Subgroup Matrix CFSG.Open CFSG.Blueprint
open scoped commutatorElement

private abbrev om8Ix : Type := Fin (4 - 1) ⊕ Fin (4 - 1) ⊕ Fin 2

private def om8Idx : om8Ix → Fin 8
  | .inl i => ![0, 1, 2] i
  | .inr (.inl i) => ![3, 4, 5] i
  | .inr (.inr i) => ![6, 7] i

private def om8Mat (r : Matrix (Fin 8) (Fin 8) (ZMod 2)) : Matrix om8Ix om8Ix (ZMod 2) :=
  Matrix.of fun i j => r (om8Idx i) (om8Idx j)

private def om8A : Matrix om8Ix om8Ix (ZMod 2) :=
  om8Mat !![0,0,0,1,0,0,0,0; 0,0,0,1,1,0,0,0; 0,0,1,0,0,0,0,0; 1,1,0,1,1,0,0,0;
    0,1,0,1,0,0,0,0; 0,0,0,0,0,1,0,0; 0,0,0,0,0,0,1,0; 0,0,0,0,0,0,0,1]

private def om8T : Matrix om8Ix om8Ix (ZMod 2) :=
  om8Mat !![1,0,0,1,0,0,1,1; 1,1,0,0,1,0,0,1; 0,0,1,0,0,0,0,0; 1,0,0,1,0,0,1,0;
    0,1,0,1,1,0,0,1; 0,0,0,0,0,1,0,0; 1,0,0,1,1,0,0,0; 0,1,0,0,1,0,0,0]

private def om8GA : Matrix om8Ix om8Ix (ZMod 2) :=
  om8Mat !![1,0,0,0,0,0,0,0; 1,0,0,0,1,0,0,0; 0,0,1,0,0,0,0,0; 1,1,0,1,1,0,0,0;
    1,1,0,0,0,0,0,0; 0,0,0,0,0,1,0,0; 0,0,0,0,0,0,0,1; 0,0,0,0,0,0,1,0]

private def om8GT : Matrix om8Ix om8Ix (ZMod 2) :=
  om8Mat !![1,0,0,0,0,0,0,0; 0,1,0,0,0,0,0,0; 0,0,1,0,0,0,0,0; 1,0,0,1,0,0,1,0;
    0,1,0,0,1,0,1,0; 0,0,0,0,0,1,0,0; 0,0,0,0,0,0,1,0; 1,1,0,0,0,0,0,1]

private def om8R1 : Matrix om8Ix om8Ix (ZMod 2) :=
  om8Mat !![1,0,0,0,0,0,0,0; 1,0,0,0,1,0,0,0; 0,0,1,0,0,0,0,0; 1,1,0,1,1,0,0,0;
    1,1,0,0,0,0,0,0; 0,0,0,0,0,1,0,0; 0,0,0,0,0,0,1,0; 0,0,0,0,0,0,0,1]

private def om8R2 : Matrix om8Ix om8Ix (ZMod 2) :=
  om8Mat !![1,0,0,0,0,0,0,0; 0,1,0,0,0,0,0,0; 0,0,1,0,0,0,0,0; 0,0,0,1,0,0,0,0;
    0,1,0,0,1,0,1,0; 0,0,0,0,0,1,0,0; 0,0,0,0,0,0,1,0; 0,1,0,0,0,0,1,1]

private def om8H : Matrix om8Ix om8Ix (ZMod 2) :=
  om8Mat !![1,0,0,0,0,0,0,0; 0,1,0,0,0,0,0,0; 0,0,1,0,0,0,0,0; 1,1,0,1,0,0,0,1;
    1,1,0,0,1,0,0,1; 0,0,0,0,0,1,0,0; 1,1,0,0,0,0,1,0; 0,0,0,0,0,0,0,1]

private theorem om8_orders : om8A * (om8A * om8A) = 1 ∧ om8T * (om8T * om8T) = 1 ∧
    om8GA * om8GA = 1 ∧ om8GT * om8GT = 1 ∧ om8R1 * om8R1 = 1 ∧ om8R2 * om8R2 = 1 ∧
    om8H * om8H = 1 := by
  decide +kernel

private theorem om8_rels :
    om8A * (om8T * om8A * (om8T * om8T)) = om8T * om8A * (om8T * om8T) * om8A ∧
    om8A * om8T ≠ om8T * om8A ∧ om8GA * om8A * om8GA = om8A * om8A ∧
    om8GT * om8T * om8GT = om8T * om8T := by
  decide +kernel

private theorem om8_comms : om8GA * om8A * om8GA * (om8A * om8A) = om8A ∧
    om8GT * om8T * om8GT * (om8T * om8T) = om8T ∧
    om8R1 * (om8T * om8T) * om8R1 * om8T = om8GA ∧ om8R2 * om8H * om8R2 * om8H = om8GT := by
  decide +kernel

private theorem om8A_isometry : ∀ v : om8Ix → ZMod 2,
    StatedQuadMinus 4 (ZMod 2) 1 1 (om8A *ᵥ v) = StatedQuadMinus 4 (ZMod 2) 1 1 v := by
  decide +kernel
private theorem om8T_isometry : ∀ v : om8Ix → ZMod 2,
    StatedQuadMinus 4 (ZMod 2) 1 1 (om8T *ᵥ v) = StatedQuadMinus 4 (ZMod 2) 1 1 v := by
  decide +kernel
private theorem om8GA_isometry : ∀ v : om8Ix → ZMod 2,
    StatedQuadMinus 4 (ZMod 2) 1 1 (om8GA *ᵥ v) = StatedQuadMinus 4 (ZMod 2) 1 1 v := by
  decide +kernel
private theorem om8GT_isometry : ∀ v : om8Ix → ZMod 2,
    StatedQuadMinus 4 (ZMod 2) 1 1 (om8GT *ᵥ v) = StatedQuadMinus 4 (ZMod 2) 1 1 v := by
  decide +kernel
private theorem om8R1_isometry : ∀ v : om8Ix → ZMod 2,
    StatedQuadMinus 4 (ZMod 2) 1 1 (om8R1 *ᵥ v) = StatedQuadMinus 4 (ZMod 2) 1 1 v := by
  decide +kernel
private theorem om8R2_isometry : ∀ v : om8Ix → ZMod 2,
    StatedQuadMinus 4 (ZMod 2) 1 1 (om8R2 *ᵥ v) = StatedQuadMinus 4 (ZMod 2) 1 1 v := by
  decide +kernel
private theorem om8H_isometry : ∀ v : om8Ix → ZMod 2,
    StatedQuadMinus 4 (ZMod 2) 1 1 (om8H *ᵥ v) = StatedQuadMinus 4 (ZMod 2) 1 1 v := by
  decide +kernel

private def om8UA : GL om8Ix (ZMod 2) :=
  ⟨om8A, om8A * om8A, om8_orders.1, by rw [mul_assoc]; exact om8_orders.1⟩
private def om8UT : GL om8Ix (ZMod 2) :=
  ⟨om8T, om8T * om8T, om8_orders.2.1, by rw [mul_assoc]; exact om8_orders.2.1⟩
private def om8UT2 : GL om8Ix (ZMod 2) :=
  ⟨om8T * om8T, om8T, by rw [mul_assoc]; exact om8_orders.2.1, om8_orders.2.1⟩
private def om8UGA : GL om8Ix (ZMod 2) :=
  ⟨om8GA, om8GA, om8_orders.2.2.1, om8_orders.2.2.1⟩
private def om8UGT : GL om8Ix (ZMod 2) :=
  ⟨om8GT, om8GT, om8_orders.2.2.2.1, om8_orders.2.2.2.1⟩
private def om8UR1 : GL om8Ix (ZMod 2) :=
  ⟨om8R1, om8R1, om8_orders.2.2.2.2.1, om8_orders.2.2.2.2.1⟩
private def om8UR2 : GL om8Ix (ZMod 2) :=
  ⟨om8R2, om8R2, om8_orders.2.2.2.2.2.1, om8_orders.2.2.2.2.2.1⟩
private def om8UH : GL om8Ix (ZMod 2) :=
  ⟨om8H, om8H, om8_orders.2.2.2.2.2.2, om8_orders.2.2.2.2.2.2⟩

private abbrev om8I : Subgroup (GL om8Ix (ZMod 2)) :=
  CFSG.MatrixModel.isometryCore (StatedQuadMinus 4 (ZMod 2) 1 1)

private theorem om8_mem_I : om8UA ∈ om8I ∧ om8UT ∈ om8I ∧ om8UT2 ∈ om8I ∧ om8UGA ∈ om8I ∧
    om8UGT ∈ om8I ∧ om8UR1 ∈ om8I ∧ om8UR2 ∈ om8I ∧ om8UH ∈ om8I := by
  have hT : om8UT ∈ om8I := Subgroup.subset_closure om8T_isometry
  refine ⟨Subgroup.subset_closure om8A_isometry, hT, ?_, Subgroup.subset_closure om8GA_isometry,
    Subgroup.subset_closure om8GT_isometry, Subgroup.subset_closure om8R1_isometry,
    Subgroup.subset_closure om8R2_isometry, Subgroup.subset_closure om8H_isometry⟩
  have : om8UT2 = om8UT * om8UT := Units.ext rfl
  rw [this]
  exact om8I.mul_mem hT hT

private theorem om8_comm_eqs : om8UA = ⁅om8UGA, om8UA⁆ ∧ om8UT = ⁅om8UGT, om8UT⁆ ∧
    om8UGA = ⁅om8UR1, om8UT2⁆ ∧ om8UGT = ⁅om8UR2, om8UH⁆ := by
  obtain ⟨e1, e2, e3, e4⟩ := om8_comms
  refine ⟨Units.ext ?_, Units.ext ?_, Units.ext ?_, Units.ext ?_⟩
  · show om8A = om8GA * om8A * om8GA * (om8A * om8A); exact e1.symm
  · show om8T = om8GT * om8T * om8GT * (om8T * om8T); exact e2.symm
  · show om8GA = om8R1 * (om8T * om8T) * om8R1 * om8T; exact e3.symm
  · show om8GT = om8R2 * om8H * om8R2 * om8H; exact e4.symm

private theorem om8_mem_omega : om8UA ∈ StatedOmega (StatedQuadMinus 4 (ZMod 2) 1 1) ∧
    om8UT ∈ StatedOmega (StatedQuadMinus 4 (ZMod 2) 1 1) ∧
    om8UGA ∈ StatedOmega (StatedQuadMinus 4 (ZMod 2) 1 1) ∧
    om8UGT ∈ StatedOmega (StatedQuadMinus 4 (ZMod 2) 1 1) := by
  obtain ⟨hA, hT, hT2, hGA, hGT, hR1, hR2, hH⟩ := om8_mem_I
  obtain ⟨c1, c2, c3, c4⟩ := om8_comm_eqs
  unfold StatedOmega
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [c1]; exact Subgroup.commutator_mem_commutator hGA hA
  · rw [c2]; exact Subgroup.commutator_mem_commutator hGT hT
  · rw [c3]; exact Subgroup.commutator_mem_commutator hR1 hT2
  · rw [c4]; exact Subgroup.commutator_mem_commutator hR2 hH

theorem forceRealPair_om8 : ForceRealPair ↥(StatedOmega (StatedQuadMinus 4 (ZMod 2) 1 1)) := by
  obtain ⟨h1, h2, -⟩ := om8_orders
  obtain ⟨h5, h6, h7, h8⟩ := om8_rels
  obtain ⟨m1, m2, m3, m4⟩ := om8_mem_omega
  obtain ⟨ha, hb, hw, hab, hg, hk⟩ := forceRealPair_facts_of_matrix om8UA om8UT om8UGA om8UGT
    (by rw [mul_assoc]; exact h1) (by rw [mul_assoc]; exact h2) h5 h6 h7 h8
  exact ForceRealPair.of_mem _ m1 m2 m3 m4 ha hb hw hab hg hk

theorem nonempty_mulEquiv_omegaMinusEight_of_lieModel {Q : Type} [Group Q]
    (h : LieModel Q .POmegaMinus 4 2 1) :
    Nonempty (Q ≃* ↥(StatedOmega (StatedQuadMinus 4 (ZMod 2) 1 1))) := by
  obtain ⟨-, K, _, _, hK, b, c, hirr, ⟨e⟩⟩ := h.statedClassicalModel_of_ne_zero (by norm_num)
  rw [pow_one] at hK
  exact ⟨e.trans (CFSG.HardMathSupport.Foote.E27.Q2.statedProjOmegaEquiv
    (StatedQuadMinus 4 K b c) hK (StatedQuadMinus 4 (ZMod 2) 1 1)
    (fun v σ => CFSG.HardMathSupport.Foote.E27.Q2.quadMinus_comp 4 σ hirr v))⟩

theorem forceRealPair_of_lieModel_POmegaMinus_four {Q : Type} [Group Q]
    (h : LieModel Q .POmegaMinus 4 2 1) : ForceRealPair Q := by
  obtain ⟨e⟩ := nonempty_mulEquiv_omegaMinusEight_of_lieModel h
  exact forceRealPair_om8.of_mulEquiv e

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719
