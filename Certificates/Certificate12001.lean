module

public import CFSG.Open.Defs

public section

namespace CFSG.GH74.GLS.TwoThin

open CFSG.Open (ordA ordSuzuki)

private theorem ordA_one_eight : ordA 1 8 = 504 := by decide +kernel

private theorem ordA_two_three : ordA 2 3 = 5616 := by decide +kernel

private theorem ordSuzuki_eight : ordSuzuki 8 = 29120 := by decide +kernel

private theorem three_dvd_29120_false : (3 : ℕ) ∣ 29120 → False := by
  decide +kernel

private theorem three_dvd_58240_false : (3 : ℕ) ∣ 58240 → False := by
  decide +kernel

end CFSG.GH74.GLS.TwoThin

namespace Certificates

theorem certificate12001 :
    CFSG.Open.ordA 1 8 = 504
    ∧ CFSG.Open.ordA 2 3 = 5616
    ∧ CFSG.Open.ordSuzuki 8 = 29120
    ∧ ((3 : ℕ) ∣ 29120 → False)
    ∧ ((3 : ℕ) ∣ 58240 → False) :=
  ⟨CFSG.GH74.GLS.TwoThin.ordA_one_eight, CFSG.GH74.GLS.TwoThin.ordA_two_three,
    CFSG.GH74.GLS.TwoThin.ordSuzuki_eight, CFSG.GH74.GLS.TwoThin.three_dvd_29120_false,
    CFSG.GH74.GLS.TwoThin.three_dvd_58240_false⟩

end Certificates
