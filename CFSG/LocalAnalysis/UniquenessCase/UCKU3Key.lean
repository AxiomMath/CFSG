module

public import CFSG.SignalizerFunctorTheorem.McBride.Models.PSL2Even.Arithmetic
public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.LocalAnalysis.UniquenessCase.UC22Defs

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UCK

open CFSG.Open Subgroup
open CFSG.LocalAnalysis.UniquenessCase.UC22

variable {X : Type} [Group X] [Finite X]

theorem nine_dvd_two_pow_add_one (n : ℕ) (hn : Odd n) (h3 : 3 ∣ n) :
    9 ∣ 2 ^ n + 1 := by
  have h6 : n % 6 = 3 := by
    have h2 : n % 2 = 1 := Nat.odd_iff.mp hn
    omega
  have h9 := CFSG.SignalizerFunctorTheorem.McBride.PSL2Even.two_pow_mod_nine n
  rw [h6] at h9
  omega

theorem three_dvd_two_pow_add_one_of_odd (n : ℕ) (hn : Odd n) : 3 ∣ 2 ^ n + 1 := by
  have h := CFSG.SignalizerFunctorTheorem.McBride.PSL2Even.two_pow_mod_three hn
  omega

end CFSG.LocalAnalysis.UniquenessCase.UCK
