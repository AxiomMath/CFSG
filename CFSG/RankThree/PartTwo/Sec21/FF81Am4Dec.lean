module

public import CFSG.RankThree.PartTwo.Sec21.FF81Am4Model
public import CFSG.RankThree.PartTwo.Census.Carrier.Sp6Two

@[expose] public section

namespace CFSG.RankThree.PartTwo.Sec21.FF81.Am4

open CFSG.Assembly.LowTwoRank (StatedSp)
open CFSG.ClassicalInvolution.Models.SymplecticPairs CFSG.SeitzReduction.SymplecticPilot
open CFSG.LieType.Universal.Symplectic.SpExtras (mat)
open CFSG.LieType.Steinberg (sl2Upper sl2Lower)
open CFSG.RankThree.PartTwo.Census.Carrier.Sp6Two
open Matrix
open scoped MatrixGroups

theorem mat6_eq (x : K3) : mat6 x = (mat 3 (ZMod 2) x).submatrix ε6 ε6 := rfl

theorem nsElt_inv (k : Fin 3) : (nsElt (K := ZMod 2) (n := 3) k)⁻¹ = nsElt k * nsElt k :=
  inv_eq_of_mul_eq_one_right (by
    rw [← mul_assoc, ← pow_two, ← pow_succ]; exact nsElt_pow_three k)

theorem tM_mul_self : tM * tM = 1 := by
  rw [tM, ← map_mul]
  have : sl2Upper (1 : ZMod 2) * sl2Upper 1 = 1 := by decide
  rw [this, map_one]

theorem tM_conj_nsElt : tM * nsElt 2 * tM⁻¹ = (nsElt (K := ZMod 2) (n := 3) 2)⁻¹ := by
  rw [tM, nsElt, ← map_inv, ← map_mul, ← map_mul, ← map_inv]
  have : sl2Upper (1 : ZMod 2) * zThreeSL * (sl2Upper (1 : ZMod 2))⁻¹ = zThreeSL⁻¹ := by decide
  rw [this]

theorem ι₂_sl2Lower : ι₂ (sl2Lower 1) = nsElt 2 * tM * (nsElt (K := ZMod 2) (n := 3) 2)⁻¹ := by
  rw [ι₂, tM, nsElt, ← map_inv, ← map_mul, ← map_mul]
  have : sl2Lower (1 : ZMod 2) = zThreeSL * sl2Upper (1 : ZMod 2) * zThreeSL⁻¹ := by decide
  rw [this]

theorem ι₂_sl2Upper : ι₂ (sl2Upper 1) = tM := rfl

theorem commute_a_lower : Commute (ι₁ (sl2Lower 1)) tM := by
  show _ * _ = _ * _
  apply mat6_injective
  simp only [map_mul, mat6_eq]
  rw [ι₁, tM, mat_shortBlock, mat_longBlock]
  simp only [Matrix.SpecialLinearGroup.coe_inv, Matrix.adjugate_fin_two_of]
  decide +kernel

theorem commute_a_upper_conj :
    Commute ((nsElt (K := ZMod 2) (n := 3) 2)⁻¹ * ι₁ (sl2Upper 1) * nsElt 2) tM := by
  show _ * _ = _ * _
  rw [nsElt_inv]
  apply mat6_injective
  simp only [map_mul, mat6_eq]
  rw [ι₁, tM, nsElt, mat_shortBlock, mat_longBlock, mat_longBlock]
  simp only [Matrix.SpecialLinearGroup.coe_inv, Matrix.adjugate_fin_two_of]
  decide +kernel

end CFSG.RankThree.PartTwo.Sec21.FF81.Am4
