module

public import CFSG.RankThree.PartTwo.Sec15.Liebeck155R1T150Core
public import CFSG.HardMathSupport.Solomon.Coordinator.I14_20LieEnd
import CFSG.RankThree.PartTwo.Sec4.RonanK429RowVOrders
import CFSG.RankThree.PartTwo.Sec4.RonanK429RowVL39Lin
import CFSG.RankThree.PartTwo.Sec4.Item426A6U43
import CFSG.RankThree.PartTwo.Sec4.Item47Unitary
import CFSG.RankThree.PartTwo.Sec4.Item49Small
import CFSG.Models.PGLOrders
public import Certificates.Data.ExceptionalSL3

public section

namespace CFSG.RankThree.PartTwo.Sec15.Liebeck155R1T150

open CFSG CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec4
open CFSG.Assembly.RankThreeEven (projSL projSU)
open CFSG.HardMathSupport.Solomon.Coordinator (LieOrderBridge)
open CFSG.HardMathSupport.Solomon.Coordinator.I1420 (lieOrderFormula)

theorem k150_rowAll_of_prime_not_dvd {J : Type} [Group J] {X : Type} [Group X] {d : ℕ}
    (hd : d ∣ Nat.card J) (h : ¬ d ∣ Nat.card X) : RowAllOfK150 J X :=
  k150_rowAll_of_not_dvd fun h' => h (hd.trans h')

theorem k150_rowAll_of_lieOrder {J : Type} [Group J] (hb : LieOrderBridge) {X : Type} [Group X]
    (idx : TauCeti.ValidLieTypeIndex) (hX : Nonempty (X ≃* (TauCeti.CFSGIndex.lie idx).Group))
    {d : ℕ} (hd : d ∣ Nat.card J) (h : ¬ d ∣ lieOrderFormula idx.1) : RowAllOfK150 J X := by
  intro S _ _ hs hna ⟨eS⟩
  obtain ⟨eX⟩ := hX
  have hS : Nat.card S = lieOrderFormula idx.1 := hb idx S ⟨eS.trans eX⟩
  exact k150_rowAll_of_prime_not_dvd (X := S) hd (by rwa [hS]) S hs hna ⟨MulEquiv.refl S⟩

private theorem not_five_dvd_lieOrderFormula_reeG2_one :
    ¬ 5 ∣ lieOrderFormula (TauCeti.LieTypeIndex.reeG2 1) := by
  have h : lieOrderFormula (TauCeti.LieTypeIndex.reeG2 1) = 10073444472 := by
    simp only [lieOrderFormula, CFSG.Open.orderRee]
    norm_num
  rw [h]
  norm_num

private theorem not_five_dvd_lieOrderFormula_g2_three :
    ¬ 5 ∣ lieOrderFormula g2ThreeIndex.1 := by
  have h : lieOrderFormula g2ThreeIndex.1 = 4245696 := by
    simp only [g2ThreeIndex, lieOrderFormula, CFSG.Open.orderG2, TauCeti.PrimePower.card_def]
    norm_num
  rw [h]
  norm_num

theorem k150_three_of_bridge {J : Type} [Group J] (hb : LieOrderBridge) (h5 : 5 ∣ Nat.card J)
    (hr : (TauCeti.LieTypeIndex.reeG2 1).Valid) :
    RowAllOfK150 J (TauCeti.CFSGIndex.lie ⟨.reeG2 1, hr⟩).Group :=
  k150_rowAll_of_lieOrder hb ⟨.reeG2 1, hr⟩ ⟨MulEquiv.refl _⟩ h5
    not_five_dvd_lieOrderFormula_reeG2_one

theorem k150_nine_G2_of_bridge {J : Type} [Group J] (hb : LieOrderBridge)
    (h5 : 5 ∣ Nat.card J) : RowAllOfK150 J (TauCeti.CFSGIndex.lie g2ThreeIndex).Group :=
  k150_rowAll_of_lieOrder hb g2ThreeIndex ⟨MulEquiv.refl _⟩ h5
    not_five_dvd_lieOrderFormula_g2_three

section Classical

open CFSG.RankThree.PartTwo.Sec4.RonanK429

theorem k150_nine_SL3_ne_two {J : Type} [Group J] (h5 : 5 ∣ Nat.card J) (e : ℕ) (he : 1 ≤ e)
    (he3 : e ≤ 3) (he2 : e ≠ 2) : RowAllOfK150 J (projSL 3 (GaloisField 3 e)) := by
  refine k150_rowAll_of_prime_not_dvd h5 ?_
  rw [RowV.card_projSL_three_char_three he]
  obtain rfl | rfl : e = 1 ∨ e = 3 := by omega
  all_goals decide +kernel

theorem k150_nine_SL3_two_of_eleven {J : Type} [Group J] (h11 : 11 ∣ Nat.card J) :
    RowAllOfK150 J (projSL 3 (GaloisField 3 2)) := by
  refine k150_rowAll_of_prime_not_dvd h11 ?_
  rw [RowV.card_projSL_three_char_three (by norm_num)]
  decide +kernel

theorem k150_nine_SU3 {J : Type} [Group J] (h5 : 5 ∣ Nat.card J) (h7 : 7 ∣ Nat.card J)
    (e : ℕ) (he : 1 ≤ e) (he3 : e ≤ 3) : RowAllOfK150 J (projSU 3 3 e) := by
  obtain rfl | rfl | rfl : e = 1 ∨ e = 2 ∨ e = 3 := by omega
  · refine k150_rowAll_of_prime_not_dvd h5 ?_
    rw [RowV.card_projSU_three_char_three le_rfl]
    decide +kernel
  · refine k150_rowAll_of_prime_not_dvd h7 ?_
    rw [RowV.card_projSU_three_char_three (by norm_num)]
    decide +kernel
  · refine k150_rowAll_of_prime_not_dvd h5 ?_
    rw [RowV.card_projSU_three_char_three (by norm_num)]
    decide +kernel

theorem k150_nine_SL4 {J : Type} [Group J] (h7 : 7 ∣ Nat.card J) :
    RowAllOfK150 J (projSL 4 (GaloisField 3 1)) :=
  k150_rowAll_of_prime_not_dvd h7 fun h =>
    absurd (h.trans RowV.card_projSL_four_three_dvd) (by decide +kernel)

theorem k150_nine_SU4_of_eleven {J : Type} [Group J] (h11 : 11 ∣ Nat.card J) :
    RowAllOfK150 J (projSU 4 3 1) :=
  k150_rowAll_of_prime_not_dvd h11
    (by rw [CFSG.PGLModel.card_projSU_four_three]; decide +kernel)

end Classical

theorem k150_nine_SL3_two_of_seven {J : Type} [Group J] (h7 : 7 ∣ Nat.card J) :
    RowAllOfK150 J (projSL 3 (GaloisField 3 2)) :=
  k150_rowAll_of_inner_model
    (Item49Small.not_three_dvd_card_outer_projSL (by norm_num) (by norm_num) (by decide))
    fun x hx => k150_goodAll_of_not_dvd h7 (RonanK429.RowV.l39_not_seven_dvd_card_centralizer x hx)

theorem k150_nine_SU4_of_five {J : Type} [Group J] (h5 : 5 ∣ Nat.card J) :
    RowAllOfK150 J (projSU 4 3 1) :=
  k150_rowAll_of_inner_model outU43_holds
    fun x hx => k150_goodAll_of_not_dvd h5 (Item426.u43ThreeCentralizer x hx)

end CFSG.RankThree.PartTwo.Sec15.Liebeck155R1T150
