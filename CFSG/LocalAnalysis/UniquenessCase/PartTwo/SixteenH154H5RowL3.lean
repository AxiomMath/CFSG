module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenH154H5Red
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenH154H5SumGlue
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenH154H5SumSL3
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Fourteen1
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenEightKSumConv
import CFSG.Monster.B.TwoA.Base.ElemAut

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22

variable {W : Type} [CommGroup W]

theorem s16h_H5_row_L3_rank [Finite W] {A L : Subgroup (MulAut W)} {t : MulAut W}
    (hc : s16h_H5Cfg A L t)
    (h : s16h_H5RowL3 L (commSub ⊤ L) (commSub ⊤ L ⊓ fixV L)) :
    ∀ q : ℕ, q.Prime → q ≠ 2 → ∀ E : Subgroup (MulAut W),
      E ≤ A ⊓ normalizer (L : Set (MulAut W)) → IsElemAbelian q E →
      Nat.card ↥(autSub E (commSub ⊤ L)) ≤ q ^ 2 := by
  obtain ⟨k, hk, hs, hsum⟩ := h
  have hq : CFSG.Open.IsQuasisimple ↥L := hc.comp.2.2
  have hLn : IsL3 ↥L 1 := s16k_isLn_of_isSLn (by norm_num) hs
  have hcenter : Subgroup.center ↥L = ⊥ := center_eq_bot_of_isL3 hLn
  have hM : Nat.card (MulAut ↥L) ∣ 336 := card_mulAut_dvd_of_isL3 hLn
  have hMq : ∀ q : ℕ, q.Prime → q ≠ 2 → ¬ q ^ 2 ∣ 336 := by
    intro q hqp hq2 hdvd
    have hq_dvd : q ∣ 336 := dvd_trans (dvd_pow_self q (by norm_num)) hdvd
    have h336 : 336 = 2 ^ 4 * (3 * 7) := by norm_num
    rw [h336] at hq_dvd
    rcases hqp.dvd_mul.mp hq_dvd with h2 | h37
    · have hq2dvd : q ∣ 2 := hqp.dvd_of_dvd_pow h2
      exact hq2 ((Nat.prime_dvd_prime_iff_eq hqp Nat.prime_two).mp hq2dvd)
    · rcases hqp.dvd_mul.mp h37 with h3 | h7
      · have hq3 : q = 3 := (Nat.prime_dvd_prime_iff_eq hqp Nat.prime_three).mp h3
        rw [hq3] at hdvd
        norm_num at hdvd
      · have hq7 : q = 7 := (Nat.prime_dvd_prime_iff_eq hqp Nat.prime_seven).mp h7
        rw [hq7] at hdvd
        norm_num at hdvd
  exact s16h_H5_sum_glue hc (N := fun H U Z => BinaryNaturalSL H U Z 3 1)
    (fun I hI => s16h_simpleScalar_binarySL3 hq hs hI) hk hsum hcenter hM hMq

theorem s16h_H5_row_L3 [Finite W] {A L : Subgroup (MulAut W)} {t : MulAut W}
    (hc : s16h_H5Cfg A L t)
    (h : s16h_H5RowL3 L (commSub ⊤ L) (commSub ⊤ L ⊓ fixV L)) :
    s16h_H5Block A L :=
  s16h_H5_block_of_autSub (s16h_H5_row_L3_rank hc h)

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
