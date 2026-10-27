module

public import CFSG.LocalAnalysis.StandardType.GGSixTCWP4E6Lang
public import CFSG.LocalAnalysis.StandardType.GGSecFiveKGCentE6FixedFive

public section

namespace CFSG.StandardType.TableCRes

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Steinberg.Adjoint
open CFSG.StandardType.KGCentE6 (iform_comm_E6 iform_add_left_E6 iform_smul_left_E6
  iform_sub_left_E6 iform_right_neg_E6)

theorem iform_add_right_E6 (x y y' : Fin Tag.E6.rank → ℤ) :
    iform x (y + y') = iform x y + iform x y' := by
  simp only [iform, Pi.add_apply, mul_add, Finset.sum_add_distrib]

theorem iform_neg_left_E6 (x y : Fin Tag.E6.rank → ℤ) : iform (-x) y = -iform x y := by
  simp only [iform, Pi.neg_apply, neg_mul, Finset.sum_neg_distrib]

theorem iform_smul_right_E6 (k : ℤ) (x y : Fin Tag.E6.rank → ℤ) :
    iform x (k • y) = k * iform x y := by
  simp only [iform, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
  ring

theorem iform_sub_right_E6 (x y y' : Fin Tag.E6.rank → ℤ) :
    iform x (y - y') = iform x y - iform x y' := by
  rw [sub_eq_add_neg, iform_add_right_E6, iform_right_neg_E6, sub_eq_add_neg]

end CFSG.StandardType.TableCRes

end
