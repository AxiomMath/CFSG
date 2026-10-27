module

public import CFSG.RankThree.PartTwo.Sec15.Liebeck155R1T150LieRows
public import CFSG.RankThree.PartTwo.Sec15.Liebeck155R1T150LieThree
public import CFSG.RankThree.PartTwo.Sec15.Liebeck155R1T150LieL2
public import CFSG.RankThree.PartTwo.Sec15.Liebeck155R1T150Alt
import CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple.AssemblyAll
import CFSG.RankThree.PartTwo.Sec4.Ronan148LUSa

public section

namespace CFSG.RankThree.PartTwo.Sec15.Liebeck155R1T150

open CFSG CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec4
open CFSG.Assembly.RankThreeEven (projSL projSU)
open CFSG.HardMathSupport.Solomon.Coordinator

theorem k150Rows_of_families {J : Type} [Group J] (hF : K150Facts J) (hb : LieOrderBridge)
    (hLSC : LieSemisimpleCent) (hLC : LieComp.LieComp) (h5 : 5 ∣ Nat.card J)
    (h7 : 7 ∣ Nat.card J)
    (one3 : ∀ e : ℕ, 1 ≤ e → RowAllOfK150 J (projSL 2 (GaloisField 3 e)))
    (five : ∀ n : ℕ, 5 ≤ n → n ≤ 12 → n ≠ 10 → RowAllOfK150 J (alternatingGroup (Fin n)))
    (ten : Nonempty (J ≃* alternatingGroup (Fin 7)) ∨ RowOfK150 J (alternatingGroup (Fin 10)))
    (nineSL3Two : RowAllOfK150 J (projSL 3 (GaloisField 3 2)))
    (nineSU4 : RowAllOfK150 J (projSU 4 3 1))
    (six : ∀ s ∈ sporadics42, RowOfK150 J (Spor s)) : K150Rows J :=
  { one := by
      intro p e _ hp2 he
      by_cases hp3 : p = 3
      · subst hp3
        exact (one3 e he).rowOfK150
      · exact (k150_one_of_ne_three hF hLSC hLC p e hp2 he hp3).rowOfK150
    two_SL := fun p e _ hp he he2 => (k150_two_SL hF hLSC hLC p e hp he he2).rowOfK150
    two_SU := fun p e _ hp he he2 => (k150_two_SU hF hLSC hLC p e hp he he2).rowOfK150
    three := fun hr => (k150_three_of_bridge hb h5 hr).rowOfK150
    four_G2 := fun p _ hp q hqp hqe hq => (k150_four_G2 hF hLSC hLC p hp q hqp hqe hq).rowOfK150
    four_Sp := fun p _ hp => (k150_four_Sp hF hLSC hLC p hp).rowOfK150
    four_SL := fun p _ hp => (k150_four_SL hF hLSC hLC p hp).rowOfK150
    four_SU := fun p _ hp => (k150_four_SU hF hLSC hLC p hp).rowOfK150
    five := fun n hn5 hn12 hn10 => (five n hn5 hn12 hn10).rowOfK150
    ten := ten
    six := six
    seven_SL2 := fun n hn => (k150_seven_SL2 hF hLSC hLC n hn).rowOfK150
    seven_SL3 := fun n hn => (k150_seven_SL3 hF hLSC hLC n hn).rowOfK150
    seven_SU3 := fun n hn => (k150_seven_SU3 hF hLSC hLC n hn).rowOfK150
    seven_Sp4 := fun n hn => (k150_seven_Sp4 hF hLSC hLC n hn).rowOfK150
    seven_SU4 := fun n hn => (k150_seven_SU4 hF hLSC hLC n hn).rowOfK150
    seven_G2 := fun q hq2 hq => (k150_seven_G2 hF hLSC hLC q hq2 hq).rowOfK150
    seven_D4 := fun q hq hq2 => (k150_seven_D4 hF hLSC hLC q hq hq2).rowOfK150
    seven_Sz := fun m hm => (k150_seven_Sz hF hLSC hLC m hm).rowOfK150
    seven_F4 := fun m hm => (k150_seven_F4 hF hLSC hLC m hm).rowOfK150
    seven_Tits := fun ht => (k150_seven_Tits hF hLSC hLC ht).rowOfK150
    eight_SL5 := (k150_eight_SL5 hF hLSC hLC).rowOfK150
    eight_SU5 := (k150_eight_SU5 hF hLSC hLC).rowOfK150
    eight_SL6 := (k150_eight_SL6 hF hLSC hLC).rowOfK150
    eight_SU6 := (k150_eight_SU6 hF hLSC hLC).rowOfK150
    eight_SL7 := (k150_eight_SL7 hF hLSC hLC).rowOfK150
    eight_Sp6 := (k150_eight_Sp6 hF hLSC hLC).rowOfK150
    eight_Sp8 := (k150_eight_Sp8 hF hLSC hLC).rowOfK150
    eight_OmegaPlus := (k150_eight_OmegaPlus hF hLSC hLC).rowOfK150
    eight_OmegaMinus := fun b c hbc => (k150_eight_OmegaMinus hF hLSC hLC b c hbc).rowOfK150
    eight_SL4 := (k150_eight_SL4 hF hLSC hLC).rowOfK150
    eight_Sp6_4 := (k150_eight_Sp6_4 hF hLSC hLC).rowOfK150
    eight_SU5_4 := (k150_eight_SU5_4 hF hLSC hLC).rowOfK150
    eight_SU5_8 := (k150_eight_SU5_8 hF hLSC hLC).rowOfK150
    eight_F4 := (k150_eight_F4 hF hLSC hLC).rowOfK150
    nine_SL3 := by
      intro e he he3
      by_cases he2 : e = 2
      · subst he2
        exact nineSL3Two.rowOfK150
      · exact (k150_nine_SL3_ne_two h5 e he he3 he2).rowOfK150
    nine_SU3 := fun e he he3 => (k150_nine_SU3 h5 h7 e he he3).rowOfK150
    nine_G2 := (k150_nine_G2_of_bridge hb h5).rowOfK150
    nine_SL4 := (k150_nine_SL4 h7).rowOfK150
    nine_SU4 := nineSU4.rowOfK150 }

theorem k150_hJord_a7 :
    ∀ m : ℕ, m ≠ 0 → 2 * Nat.card (alternatingGroup (Fin 7)) ≠ 3 ^ m * ((3 ^ m) ^ 2 - 1) := by
  rw [k150_card_alternating_seven]
  refine k150_not_psl2_card 4 (by norm_num) fun m hm hm0 => ?_
  have : 1 ≤ m := Nat.one_le_iff_ne_zero.mpr hm0
  interval_cases m <;> norm_num

theorem k150_hJord_of_card_m22 {J : Type} [Group J] (hN : Nat.card J = 443520) :
    ∀ m : ℕ, m ≠ 0 → 2 * Nat.card J ≠ 3 ^ m * ((3 ^ m) ^ 2 - 1) := by
  rw [hN]
  refine k150_not_psl2_card 5 (by norm_num) fun m hm hm0 => ?_
  have : 1 ≤ m := Nat.one_le_iff_ne_zero.mpr hm0
  interval_cases m <;> norm_num

section Holds


theorem k150Rows_a7
    (six : ∀ s ∈ sporadics42, RowOfK150 (alternatingGroup (Fin 7)) (Spor s)) :
    K150Rows (alternatingGroup (Fin 7)) := by
  have hb : LieOrderBridge := HardMathSupport.Solomon.Coordinator.lieOrderBridge_holds
  have hLSC : LieSemisimpleCent :=
    HardMathSupport.Solomon.Coordinator.LieSemisimple.lieSemisimpleCent
  have hLC : LieComp.LieComp := Sec4.Ronan148L.lieComp_holds
  have hc := k150_card_alternating_seven
  have hF := k150Facts_a7 hb
  exact k150Rows_of_families hF hb hLSC hLC (by rw [hc]; norm_num) (by rw [hc]; norm_num)
    (fun e he => k150_rowAll_projSL_two_three hF.exists_noncomm (by rw [hc]; norm_num)
      k150_hJord_a7 e he)
    (fun _ hn5 hn12 hn10 => k150_rowAll_alternating_a7 hn5 hn12 hn10)
    (Or.inl ⟨MulEquiv.refl _⟩)
    (k150_nine_SL3_two_of_seven (by rw [hc]; norm_num))
    (k150_nine_SU4_of_five (by rw [hc]; norm_num)) six

section M22


theorem k150Rows_m22
    (six : ∀ s ∈ sporadics42, RowOfK150 Blueprint.NativeSporadic.M22 (Spor s)) :
    K150Rows Blueprint.NativeSporadic.M22 := by
  have hb : LieOrderBridge := HardMathSupport.Solomon.Coordinator.lieOrderBridge_holds
  have hLSC : LieSemisimpleCent :=
    HardMathSupport.Solomon.Coordinator.LieSemisimple.lieSemisimpleCent
  have hLC : LieComp.LieComp := Sec4.Ronan148L.lieComp_holds
  have hc : Nat.card Blueprint.NativeSporadic.M22 = 443520 := Sporadic.Mathieu.card_M22
  have hF := k150Facts_m22 hb
  have hgt : 362880 < Nat.card Blueprint.NativeSporadic.M22 := by rw [hc]; norm_num
  exact k150Rows_of_families hF hb hLSC hLC (by rw [hc]; norm_num) (by rw [hc]; norm_num)
    (fun e he => k150_rowAll_projSL_two_three hF.exists_noncomm
      (lt_trans (by norm_num : 60 < 720) hF.card_gt) (k150_hJord_of_card_m22 hc) e he)
    (fun _ hn5 hn12 _ => k150_rowAll_alternating_of_card_gt hgt hn5 hn12)
    (Or.inr (k150_rowAll_alternating_of_card_gt hgt (by norm_num) (by norm_num)).rowOfK150)
    (k150_nine_SL3_two_of_eleven (by rw [hc]; norm_num))
    (k150_nine_SU4_of_eleven (by rw [hc]; norm_num)) six

end M22

end Holds

end CFSG.RankThree.PartTwo.Sec15.Liebeck155R1T150
