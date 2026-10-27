module

public import CFSG.Quasithin.Vol2.F134HSTables

public section

namespace CFSG.Quasithin.F134

theorem hs_gOne_conj : ∀ l < 3, hsGOneU.getD l 0 < 512 ∧ hsGOneC.getD l 0 < 512 ∧
    mulX20 (hsTel (hsGOneU.getD l 0)) (hsD 1) = mulX20 (hsD 1) (hsTel (hsGOneC.getD l 0)) := by
  decide +kernel

theorem hs_gOne_tree : hsGOneEAt 0 = 0 ∧ ∀ p < 256, hsGOneEAt p < 512 ∧ (0 < p →
    hsGOnePAt p / 8 < p ∧ hsGOnePAt p % 8 < 3 ∧
    mulX20 (hsTel (hsGOneEAt (hsGOnePAt p / 8))) (hsTel (hsGOneU.getD (hsGOnePAt p % 8) 0)) =
      hsTel (hsGOneEAt p)) := by
  decide +kernel

theorem hs_gOne_trans : ∀ i < 512, hsGOneQAt i / 512 < 2 ∧ hsGOneQAt i % 512 < 256 ∧
    hsGOneR.getD (hsGOneQAt i / 512) 0 < 512 ∧
    hsTel i = mulX20 (hsTel (hsGOneR.getD (hsGOneQAt i / 512) 0))
      (hsTel (hsGOneEAt (hsGOneQAt i % 512))) := by
  decide +kernel

theorem hs_gOne_dec : ∀ j < 270, ∀ s < 2, hsGOneDecAt (2 * j + s) / 262144 < 270 ∧
    mulX20 (mulX20 (hsD j) (hsTel (hsGOneR.getD s 0))) (hsD 1) =
      mulX20 (mulX20 (hsTel (hsGOneDecAt (2 * j + s) / 512 % 512))
        (hsD (hsGOneDecAt (2 * j + s) / 262144))) (hsTel (hsGOneDecAt (2 * j + s) % 512)) := by
  decide +kernel

theorem hs_gTwo_conj : ∀ l < 4, hsGTwoU.getD l 0 < 512 ∧ hsGTwoC.getD l 0 < 512 ∧
    mulX20 (hsTel (hsGTwoU.getD l 0)) (hsD 251) =
      mulX20 (hsD 251) (hsTel (hsGTwoC.getD l 0)) := by
  decide +kernel

theorem hs_gTwo_tree : hsGTwoEAt 0 = 0 ∧ ∀ p < 128, hsGTwoEAt p < 512 ∧ (0 < p →
    hsGTwoPAt p / 8 < p ∧ hsGTwoPAt p % 8 < 4 ∧
    mulX20 (hsTel (hsGTwoEAt (hsGTwoPAt p / 8))) (hsTel (hsGTwoU.getD (hsGTwoPAt p % 8) 0)) =
      hsTel (hsGTwoEAt p)) := by
  decide +kernel

theorem hs_gTwo_trans : ∀ i < 512, hsGTwoQAt i / 512 < 4 ∧ hsGTwoQAt i % 512 < 128 ∧
    hsGTwoR.getD (hsGTwoQAt i / 512) 0 < 512 ∧
    hsTel i = mulX20 (hsTel (hsGTwoR.getD (hsGTwoQAt i / 512) 0))
      (hsTel (hsGTwoEAt (hsGTwoQAt i % 512))) := by
  decide +kernel

theorem hs_gTwo_dec : ∀ j < 270, ∀ s < 4, hsGTwoDecAt (4 * j + s) / 262144 < 270 ∧
    mulX20 (mulX20 (hsD j) (hsTel (hsGTwoR.getD s 0))) (hsD 251) =
      mulX20 (mulX20 (hsTel (hsGTwoDecAt (4 * j + s) / 512 % 512))
        (hsD (hsGTwoDecAt (4 * j + s) / 262144))) (hsTel (hsGTwoDecAt (4 * j + s) % 512)) := by
  decide +kernel

theorem hs_b_check : hsBC = mulX20 (hsTel 18) (hsBWC hsBW) := by decide +kernel

end CFSG.Quasithin.F134
