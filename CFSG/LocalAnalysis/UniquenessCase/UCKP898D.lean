module

public import CFSG.LocalAnalysis.UniquenessCase.UCKP898A
public import CFSG.LocalAnalysis.UniquenessCase.UCKP898B
public import CFSG.LocalAnalysis.UniquenessCase.UCKP898C
public import CFSG.LocalAnalysis.UniquenessCase.UCKP898E
public import CFSG.LocalAnalysis.UniquenessCase.UCKPCenter

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UCK

open Subgroup CFSG.Open
open CFSG.ComponentClassification.Burgoyne.U

theorem u3FixField_of_center (hCen : U3Center) : U3FixField := by
  intro X _ _ n hX s hs hsn r hr hrs α hα hni
  obtain ⟨hr2, hr3⟩ := prime_ne_two_three_of_dvd_pow_sub_one hs hrs
  obtain ⟨K, _, h, e, M, φ, hφord, hrn, hcard, hbar, hfix⟩ := u3_prime_descent hX hr hr2 hr3 hα hni
  obtain ⟨m, hm⟩ := hrn
  have hnr : n / r = m := by rw [hm]; exact Nat.mul_div_cancel_left m hr.pos
  rw [hnr] at hcard hbar
  refine ⟨m, hm, fun q hq hq3 hqm => ?_⟩
  obtain ⟨ζ, hζ0, hζq, hφζ, hζN⟩ := exists_fixed_norm_one_order h hcard hbar hqm
  obtain ⟨hord, hyfix⟩ := diag_fixed_order h hq hζ0 hζN hζq
  have hα1 := hfix _ (hyfix φ hφζ)
  refine lift_prime_fixed (hCen X n hX) hq hq3 α ?_ hα1
  rw [MulEquiv.orderOf_eq e.symm, MulEquiv.orderOf_eq (uConjAut h (by norm_num) M), hord]

theorem u3FixField_holds (hG : CFSG.Open.GriessAllModelsStatement) : U3FixField :=
  u3FixField_of_center (u3Center_of_griess hG)

end CFSG.LocalAnalysis.UniquenessCase.UCK
