module

public import CFSG.LocalAnalysis.StandardType.GGHdRo7DDefs
import CFSG.LocalAnalysis.StandardType.GGHdRo7SUClassLarge
import CFSG.LocalAnalysis.StandardType.GGRCArith

public section

namespace CFSG.StandardType.HdRo7D

open CFSG.StandardType.HdRo7C CFSG.StandardType.HdRo7SU

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

theorem d_classLarge_holds : DClassLargeLeaf := by
  intro hKG p _ hp d hd W _ _ hfin R hirr hgen hsmall
  refine su_linWeyl_of_card_lt hKG hp hd hfin R hirr hgen ?_
  subst hp
  have harith := ggRC_arith (p := 3) (n := d) (W := 2 ^ d * d.factorial)
    (by norm_num) (by norm_num) hd (Or.inl le_rfl)
  have h6 : (6 : ℕ) ^ d = 3 ^ d * 2 ^ d := by rw [← mul_pow]; norm_num
  have hle : 6 ^ d * d.factorial ≤ 3 ^ d * ((3 - 1) * 6 * (2 ^ d * d.factorial)) := by
    rw [h6]
    calc 3 ^ d * 2 ^ d * d.factorial ≤ 12 * (3 ^ d * 2 ^ d * d.factorial) :=
          Nat.le_mul_of_pos_left _ (by norm_num)
      _ = 3 ^ d * ((3 - 1) * 6 * (2 ^ d * d.factorial)) := by norm_num; ring
  exact lt_of_le_of_lt (Nat.mul_le_mul_left 8 (hsmall.trans hle)) harith

end CFSG.StandardType.HdRo7D
