module

public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.DihedralCore
import Mathlib.Tactic

namespace CFSG
end CFSG
open CFSG

/-! # The dihedral group of order six has no element of order six -/

namespace CFSG.GorensteinWalter

/-- Every element of `DihedralGroup 3` has order dividing either `3` or
`2`; in particular no element has order six. -/
public theorem dihedralGroup_three_orderOf_ne_six
    (z : DihedralGroup 3) : orderOf z ≠ 6 := by
  rcases dihedralGroup_cases z with ⟨i, rfl⟩ | ⟨i, rfl⟩
  · have hpow : (DihedralGroup.r i : DihedralGroup 3) ^ 3 = 1 := by
      rw [DihedralGroup.r_pow]
      have h3 : (3 : ZMod 3) = 0 := ZMod.natCast_self 3
      change DihedralGroup.r (i * (3 : ZMod 3)) = 1
      rw [h3, mul_zero, DihedralGroup.r_zero]
    have hdvd : orderOf (DihedralGroup.r i : DihedralGroup 3) ∣ 3 :=
      orderOf_dvd_of_pow_eq_one hpow
    intro h
    rw [h] at hdvd
    norm_num at hdvd
  · have hsq : (DihedralGroup.sr i : DihedralGroup 3) ^ 2 = 1 := by
      simpa [pow_two] using DihedralGroup.sr_mul_self i
    have hdvd : orderOf (DihedralGroup.sr i : DihedralGroup 3) ∣ 2 :=
      orderOf_dvd_of_pow_eq_one hsq
    intro h
    rw [h] at hdvd
    norm_num at hdvd

end CFSG.GorensteinWalter
