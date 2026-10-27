module

public import CFSG.RankThree.PartTwo.Sec19.KF1923OutLinear
public import CFSG.RankThree.PartTwo.Sec19.KF1923OutClassical
public import CFSG.RankThree.PartTwo.Sec19.KF1923OutAlternating

public section

namespace CFSG.RankThree.PartTwo.Late

open CFSG.RankThree.PartTwo.Sec19 (IsList194 IsSmall194 IsTripleA6)
open CFSG.Assembly.RankThreeEven (projSL projSU projSp projOmegaMinus)
open CFSG.ComponentClassification.OuterAutomorphisms (Outer)

theorem kf1_pointwise
    (hGtwo : ∀ (K : Type) [Field K] [Finite K] (m : ℕ), Nat.card K = 2 ^ m →
      IsCyclic (Outer (CFSG.Blueprint.Chevalley.adjointGroup .G2 K)))
    (X : Type) [Group X] [Finite X] (hX : CFSG.IsQuasisimple X)
    (hlist : IsList194 X ∨ IsSmall194 X ∨ IsTripleA6 X) :
    OutTwoAbelian X ∧ (¬ IsNoncyclicOutType X → CFSG.ClassicalInvolution.Nobq.OutTwoCyclic X) := by
  obtain ⟨hperf, -, -⟩ := hX
  rcases hlist with hL | hS | hT
  · unfold IsList194 at hL
    rcases hL with ⟨n, hn, hSL | hL3 | hSp | hG2⟩ | hU42 | hU48 | hL42 | hL44 | hL52 | hL62 |
      hL72 | hSp6 | ⟨b, c, hirr, hOm⟩ | hA10
    ·
      obtain ⟨e⟩ := hSL
      rcases Nat.even_or_odd' n with ⟨k, rfl | rfl⟩
      · refine ⟨outTwoAbelian_of_sl_three _ hperf e, fun hnc => ?_⟩
        exact (hnc (Or.inl ⟨k, by omega, Or.inl ⟨e⟩⟩)).elim
      · have hodd : Odd (2 * k + 1) := odd_two_mul_add_one k
        have e' := projSLOfSL3Odd hodd e
        exact ⟨outTwoAbelian_of_mulEquiv e' (outTwoAbelian_projSL_three _),
          fun _ => CFSG.ClassicalInvolution.Nobq.OutTwoCyclic.of_mulEquiv e'
            (outTwoCyclic_projSL_three_odd hodd)⟩
    ·
      obtain ⟨e⟩ := hL3
      rcases Nat.even_or_odd' n with ⟨k, rfl | rfl⟩
      · refine ⟨outTwoAbelian_of_mulEquiv e (outTwoAbelian_projSL_three _), fun hnc => ?_⟩
        exact (hnc (Or.inl ⟨k, by omega, Or.inr ⟨e⟩⟩)).elim
      · have hodd : Odd (2 * k + 1) := odd_two_mul_add_one k
        exact ⟨outTwoAbelian_of_mulEquiv e (outTwoAbelian_projSL_three _),
          fun _ => CFSG.ClassicalInvolution.Nobq.OutTwoCyclic.of_mulEquiv e
            (outTwoCyclic_projSL_three_odd hodd)⟩
    ·
      obtain ⟨e⟩ := hSp
      have hc := CFSG.ClassicalInvolution.Nobq.OutTwoCyclic.of_mulEquiv e
        (outTwoCyclic_projSp_two (GaloisField 2 n))
      exact ⟨outTwoAbelian_of_outTwoCyclic hc, fun _ => hc⟩
    ·
      obtain ⟨K, hKf, hKfin, hK, ⟨e⟩⟩ := hG2
      have hcX : IsCyclic (Outer X) :=
        isCyclic_outer_of_mulEquiv e (hGtwo K n hK)
      exact ⟨outTwoAbelian_of_outTwoCyclic (outTwoCyclic_of_isCyclic_outer hcX),
        fun _ => outTwoCyclic_of_isCyclic_outer hcX⟩
    ·
      obtain ⟨e⟩ := hU42
      have hc := outTwoCyclic_projSU 4 2 1 (by norm_num) (by norm_num) le_rfl (by norm_num)
      exact ⟨outTwoAbelian_of_outTwoCyclic (CFSG.ClassicalInvolution.Nobq.OutTwoCyclic.of_mulEquiv
        e hc), fun _ => CFSG.ClassicalInvolution.Nobq.OutTwoCyclic.of_mulEquiv e hc⟩
    ·
      obtain ⟨e⟩ := hU48
      have hc := outTwoCyclic_projSU 4 2 3 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      exact ⟨outTwoAbelian_of_outTwoCyclic (CFSG.ClassicalInvolution.Nobq.OutTwoCyclic.of_mulEquiv
        e hc), fun _ => CFSG.ClassicalInvolution.Nobq.OutTwoCyclic.of_mulEquiv e hc⟩
    ·
      obtain ⟨e⟩ := hL42
      have hc := CFSG.ClassicalInvolution.Nobq.OutTwoCyclic.of_mulEquiv e
        (outTwoCyclic_projSL_gf2 (n := 4) (by norm_num))
      exact ⟨outTwoAbelian_of_outTwoCyclic hc, fun _ => hc⟩
    ·
      obtain ⟨e⟩ := hL44
      exact ⟨outTwoAbelian_of_mulEquiv e (outTwoAbelian_of_outTwoExpTwo
        outTwoExpTwo_projSL_four_four), fun hnc => (hnc (Or.inr (Or.inl ⟨e⟩))).elim⟩
    ·
      obtain ⟨e⟩ := hL52
      have hc := CFSG.ClassicalInvolution.Nobq.OutTwoCyclic.of_mulEquiv e
        (outTwoCyclic_projSL_gf2 (n := 5) (by norm_num))
      exact ⟨outTwoAbelian_of_outTwoCyclic hc, fun _ => hc⟩
    ·
      obtain ⟨e⟩ := hL62
      have hc := CFSG.ClassicalInvolution.Nobq.OutTwoCyclic.of_mulEquiv e
        (outTwoCyclic_projSL_gf2 (n := 6) (by norm_num))
      exact ⟨outTwoAbelian_of_outTwoCyclic hc, fun _ => hc⟩
    ·
      obtain ⟨e⟩ := hL72
      have hc := CFSG.ClassicalInvolution.Nobq.OutTwoCyclic.of_mulEquiv e
        (outTwoCyclic_projSL_gf2 (n := 7) (by norm_num))
      exact ⟨outTwoAbelian_of_outTwoCyclic hc, fun _ => hc⟩
    ·
      obtain ⟨e⟩ := hSp6
      have hd := card_outer_projSp_three_one X e
      have hc := outTwoCyclic_of_card_dvd (m := 1) odd_one (by rw [mul_one]; exact hd)
      exact ⟨outTwoAbelian_of_outTwoCyclic hc, fun _ => hc⟩
    ·
      obtain ⟨e⟩ := hOm
      have hc := CFSG.ClassicalInvolution.Nobq.OutTwoCyclic.of_mulEquiv e
        (outTwoCyclic_projOmegaMinus_three b c hirr)
      exact ⟨outTwoAbelian_of_outTwoCyclic hc, fun _ => hc⟩
    ·
      obtain ⟨e⟩ := hA10
      have hd := card_outer_dvd_two_of_alternating (n := 10) (Or.inr (by norm_num)) e
      have hc := outTwoCyclic_of_card_dvd (m := 1) odd_one (by rw [mul_one]; exact hd)
      exact ⟨outTwoAbelian_of_outTwoCyclic hc, fun _ => hc⟩
  ·
    obtain hA6 | hU33 := hS
    · obtain ⟨e⟩ := hA6
      exact ⟨outTwoAbelian_of_alternatingGroup_six e, fun hnc =>
        (hnc (Or.inr (Or.inr (Or.inl ⟨e⟩)))).elim⟩
    · obtain ⟨e⟩ := hU33
      have hc := outTwoCyclic_projSU 3 3 1 (by norm_num) (by norm_num) le_rfl (by norm_num)
      exact ⟨outTwoAbelian_of_outTwoCyclic (CFSG.ClassicalInvolution.Nobq.OutTwoCyclic.of_mulEquiv
        e hc), fun _ => CFSG.ClassicalInvolution.Nobq.OutTwoCyclic.of_mulEquiv e hc⟩
  ·
    obtain ⟨hcard, ⟨e⟩⟩ := hT
    have hE := outTwoExpTwo_of_tripleA6 hperf e
    exact ⟨outTwoAbelian_of_outTwoExpTwo hE, fun hnc =>
      (hnc (Or.inr (Or.inr (Or.inr ⟨hcard, ⟨e⟩⟩)))).elim⟩

theorem kf1_of_G2
    (hGtwo : ∀ (K : Type) [Field K] [Finite K] (m : ℕ), Nat.card K = 2 ^ m →
      IsCyclic (Outer (CFSG.Blueprint.Chevalley.adjointGroup .G2 K))) : KF1 := by
  unfold KF1
  refine ⟨?_, ?_, ?_⟩
  · intro X _ _ hX
    obtain ⟨hq, hlist⟩ := hX
    exact (kf1_pointwise hGtwo X hq hlist).1
  · intro X _ _ hX hb
    obtain ⟨hq, -⟩ := hX
    obtain ⟨hperf, -, -⟩ := hq
    obtain hL3 | hT | hSL := hb
    · obtain ⟨n, hodd, ⟨e⟩⟩ := hL3
      exact outTwoExpTwo_of_mulEquiv e (outTwoExpTwo_projSL_three_odd hodd)
    · obtain ⟨-, ⟨e'⟩⟩ := hT
      exact outTwoExpTwo_of_tripleA6 hperf e'
    · obtain ⟨e⟩ := hSL
      exact outTwoExpTwo_of_sl_three_four hperf e
  · intro X _ _ hX hnc
    obtain ⟨hq, hlist⟩ := hX
    exact (kf1_pointwise hGtwo X hq hlist).2 hnc

end CFSG.RankThree.PartTwo.Late
