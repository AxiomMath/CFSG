module

public import CFSG.LinearAlgebra.F2CubeMatrix
public import CFSG.HardMathSupport.Timmesfeld.SporadicBalance.BSevenLocalCore

public section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.W4Row

open CFSG.Blueprint CFSG.LinearAlgebra.F2Cube
  CFSG.HardMathSupport.Timmesfeld.SporadicBalance.BSevenLocal

theorem fixedCount_eq_two_pow_sub_rank {n : ℕ} (M : Matrix (Fin n) (Fin n) (ZMod 2)) :
    fixedCount M = 2 ^ (n - Matrix.rank (M - 1)) := by
  classical
  have hker : {y : Fin n → ZMod 2 // M.mulVec y = y} ≃
      LinearMap.ker (Matrix.mulVecLin (M - 1)) :=
    Equiv.subtypeEquivRight fun y => by
      simp [LinearMap.mem_ker, Matrix.sub_mulVec, sub_eq_zero]
  unfold fixedCount
  rw [Fintype.card_congr hker, Module.card_eq_pow_finrank (K := ZMod 2), ZMod.card 2]
  congr 1
  have hrn := LinearMap.finrank_range_add_finrank_ker (Matrix.mulVecLin (M - 1))
  rw [Module.finrank_fin_fun] at hrn
  unfold Matrix.rank
  omega

theorem fixedCount_B_eq (g : NativeSporadic.B) :
    fixedCount g.val.val = 2 ^ (4370 - rk g) := by
  rw [fixedCount_eq_two_pow_sub_rank]

theorem card_dvd_sum_fixedCount_B (H : Subgroup NativeSporadic.B) [Fintype H] :
    Fintype.card H ∣ ∑ h : H, fixedCount (h : NativeSporadic.B).val.val := by
  classical
  letI : MulAction H (Fin 4370 → ZMod 2) :=
    { smul := fun h v => ((h : NativeSporadic.B).val.val).mulVec v
      one_smul := fun v => by simp
      mul_smul := fun a b v => by
        change (((a * b : H) : NativeSporadic.B).val.val).mulVec v =
          (((a : H) : NativeSporadic.B).val.val).mulVec
            ((((b : H) : NativeSporadic.B).val.val).mulVec v)
        simp only [Subgroup.coe_mul, Units.val_mul, Submonoid.coe_mul, Matrix.mulVec_mulVec] }
  haveI : Fintype (Quotient (MulAction.orbitRel H (Fin 4370 → ZMod 2))) := Quotient.fintype _
  have hcard : ∀ h : H, Fintype.card (MulAction.fixedBy (Fin 4370 → ZMod 2) h) =
      fixedCount ((h : NativeSporadic.B).val.val) := by
    intro h
    apply Fintype.card_congr
    refine Equiv.subtypeEquivRight fun v => ?_
    exact Iff.rfl
  have hburnside := MulAction.sum_card_fixedBy_eq_card_orbits_mul_card_group H
    (Fin 4370 → ZMod 2)
  rw [Finset.sum_congr rfl (fun h _ => hcard h)] at hburnside
  refine ⟨Fintype.card (Quotient (MulAction.orbitRel H (Fin 4370 → ZMod 2))), ?_⟩
  rw [hburnside, mul_comm]

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.W4Row
