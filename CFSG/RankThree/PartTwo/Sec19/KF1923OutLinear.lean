module

public import CFSG.RankThree.PartTwo.Sec19.KF1923OutGeneric
import CFSG.GH74.GLS.IVK.Proofs2.Ivk93WL3
import CFSG.GH74.Generic.S45.LOut
import CFSG.RankThree.PartTwo.Sec14.Ronan148KT1RowEight
import CFSG.Quasithin.Background.L34OutFacts
import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81TenThirteenAltTenOuter
import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81TenElevenOneSLThreeOdd

public section

namespace CFSG.RankThree.PartTwo.Late

open CFSG.Assembly.RankThreeEven (projSL)
open CFSG.ComponentClassification.OuterAutomorphisms (Outer)
open CFSG.LocalAnalysis.ComponentInitial

theorem odd_commutator_projSL_three (F : Type) [Field F] [Finite F] :
    Odd (Nat.card (commutator (Outer (projSL 3 F)))) :=
  CFSG.GH74.Generic.S45.odd_card_commutator_outer_of_equiv
    (CFSG.RankThree.PartTwo.Sec4.projSLEquivProjectiveSL 3 F)
    CFSG.GH74.GLS.IVK.Proofs2.ivk93w_odd_commutator_outer_three

theorem outTwoAbelian_projSL_three (F : Type) [Field F] [Finite F] :
    OutTwoAbelian (projSL 3 F) :=
  outTwoAbelian_of_odd_commutator (odd_commutator_projSL_three F)

theorem gcd_three_two_pow_sub_one {n : ℕ} (hn : Odd n) : Nat.gcd 3 (2 ^ n - 1) = 1 := by
  obtain ⟨j, rfl⟩ := hn
  have h4 : 4 ^ j % 3 = 1 := by
    rw [Nat.pow_mod]
    norm_num
  have h2 : 2 ^ (2 * j + 1) = 2 * 4 ^ j := by
    rw [show (4 : ℕ) = 2 ^ 2 by norm_num, ← pow_mul, pow_succ]
    ring
  have hnd : ¬ 3 ∣ 2 ^ (2 * j + 1) - 1 := by
    rw [h2]
    omega
  exact (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mpr hnd

theorem card_outer_projSL_three_odd {n : ℕ} (hn : Odd n) :
    Nat.card (Outer (projSL 3 (GaloisField 2 n))) ∣ 2 * n := by
  have hcard : Nat.card (GaloisField 2 n) = 2 ^ n := GaloisField.card 2 n hn.pos.ne'
  have h := UnitaryHigher.higher_linear_outer_order_divides_field_gcd_bound
    (k := GaloisField 2 n) (p := 2) (f := n) (n := 3) Nat.prime_two hn.pos (le_refl 3) hcard
  rw [gcd_three_two_pow_sub_one hn, mul_one] at h
  rw [natCard_outer_of_mulEquiv
    (CFSG.RankThree.PartTwo.Sec4.projSLEquivProjectiveSL 3 (GaloisField 2 n))]
  exact h

theorem outTwoExpTwo_projSL_three_odd {n : ℕ} (hn : Odd n) :
    OutTwoExpTwo (projSL 3 (GaloisField 2 n)) :=
  outTwoExpTwo_of_card_dvd hn (card_outer_projSL_three_odd hn)

theorem outTwoCyclic_projSL_three_odd {n : ℕ} (hn : Odd n) :
    CFSG.ClassicalInvolution.Nobq.OutTwoCyclic (projSL 3 (GaloisField 2 n)) :=
  outTwoCyclic_of_card_dvd hn (card_outer_projSL_three_odd hn)

noncomputable def sl3OddEquiv {n : ℕ} (hn : Odd n) :
    Matrix.SpecialLinearGroup (Fin 3) (GaloisField 2 n) ≃*
      CFSG.LocalAnalysis.ComponentInitial.LinearFlag.projectiveSL 3 (GaloisField 2 n) :=
  (((QuotientGroup.quotientMulEquivOfEq
      (CFSG.LocalAnalysis.RankThreeTheoremC.SL3E27.center_eq_bot_of_odd hn)).trans
    QuotientGroup.quotientBot).symm).trans
    (CFSG.LocalAnalysis.ComponentInitial.LinearCover.projectiveSpecialLinearEquivProjectiveSL 3
      (GaloisField 2 n))

noncomputable def projSLOfSL3Odd {X : Type} [Group X] {n : ℕ} (hn : Odd n)
    (e : X ≃* Matrix.SpecialLinearGroup (Fin 3) (GaloisField 2 n)) :
    X ≃* projSL 3 (GaloisField 2 n) :=
  (e.trans (sl3OddEquiv hn)).trans
    (CFSG.RankThree.PartTwo.Sec4.projSLEquivProjectiveSL 3 (GaloisField 2 n)).symm

theorem outTwoAbelian_of_sl_three {X : Type} [Group X] (F : Type) [Field F] [Finite F]
    (hX : Group.IsPerfect X) (e : X ≃* Matrix.SpecialLinearGroup (Fin 3) F) :
    OutTwoAbelian X :=
  outTwoAbelian_of_perfect_quotient hX
    ((centerQuotEquiv e).trans
      (CFSG.LocalAnalysis.ComponentInitial.LinearCover.projectiveSpecialLinearEquivProjectiveSL 3
        F))
    CFSG.GH74.GLS.IVK.Proofs2.ivk93w_odd_commutator_outer_three

theorem outTwoExpTwo_projectiveSL_three_four {k : Type} [Field k] (hk : Nat.card k = 4) :
    OutTwoExpTwo (CFSG.LocalAnalysis.ComponentInitial.LinearFlag.projectiveSL 3 k) := by
  intro P hP x hx
  obtain ⟨m, hm⟩ := hP ⟨x, hx⟩
  have hm' : x ^ 2 ^ m = 1 := by simpa using congrArg Subtype.val hm
  obtain ⟨α, rfl⟩ := QuotientGroup.mk_surjective x
  rw [← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff] at hm'
  rw [← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff]
  exact CFSG.Quasithin.L34Out.sq_mem_range_conj hk hm'

theorem outTwoExpTwo_of_sl_three_four {X : Type} [Group X] (hX : Group.IsPerfect X)
    (e : X ≃* Matrix.SpecialLinearGroup (Fin 3) (GaloisField 2 2)) : OutTwoExpTwo X :=
  outTwoExpTwo_of_perfect_quotient hX
    ((centerQuotEquiv e).trans
      (CFSG.LocalAnalysis.ComponentInitial.LinearCover.projectiveSpecialLinearEquivProjectiveSL 3
        (GaloisField 2 2)))
    (outTwoExpTwo_projectiveSL_three_four (by rw [GaloisField.card 2 2 (by norm_num)]; norm_num))

theorem outTwoCyclic_projSL_gf2 {n : ℕ} (hn : 3 ≤ n) :
    CFSG.ClassicalInvolution.Nobq.OutTwoCyclic (projSL n (GaloisField 2 1)) := by
  have h := CFSG.RankThree.PartTwo.Sec14.Ronan148K.card_outer_projSL_gf2_dvd_two hn
  exact outTwoCyclic_of_card_dvd (m := 1) odd_one (by rw [mul_one]; exact h)

theorem outTwoExpTwo_projSL_four_four : OutTwoExpTwo (projSL 4 (GaloisField 2 2)) := by
  have hk : Nat.card (GaloisField 2 2) = 4 := by
    rw [GaloisField.card 2 2 (by norm_num)]
    norm_num
  exact outTwoExpTwo_of_mulEquiv
    (CFSG.RankThree.PartTwo.Sec4.projSLEquivProjectiveSL 4 (GaloisField 2 2))
    (outTwoExpTwo_of_forall_sq (sq_eq_one_of_sq_inner
      (CFSG.LocalAnalysis.RankThreeTheoremC.TenThirteen.AltTen.sq_inner_projectiveSL_four hk)))

end CFSG.RankThree.PartTwo.Late
