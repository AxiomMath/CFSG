module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC1677ThreeDefs
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenH154E3Fix
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenThreeOrbitExclusion
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenSLThreeTripleRank
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenSLThreeTripleParabolic
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SteinbergConjugateBounds
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenNaturalThreeCases
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenH154H5Shapes
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenH154H5ZResTrans
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC165ExclDirect

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22

theorem s168e3_s15_ne_three_of_sl_three_sum_three
    {G : Type} [Group G] [Finite G]
    {D : UC22.Data G} {V₀ V L : Subgroup G} {hV : IsElemAbelian 2 V}
    (c : S168e3Ctx D V₀ V L hV)
    (h82 : F08.R82 D)
    (hcomp : IsComponentOf (lBar V₀ V hV L) (Mbar D.M V₀ V hV))
    (hthin : ∀ q : ℕ, q.Prime → q ≠ 2 →
      CFSG.Open.pRank q (lBar V₀ V hV L) ≤ 1)
    (hrow : s16h_H5L3Sum (lBar V₀ V hV L)
      (wTil V₀ V hV L)
      (wTil V₀ V hV L ⊓ fixV (lBar V₀ V hV L)) 3) :
    s15 D.M V₀ V hV L ≠ 3 := by
  intro hs
  have hL3 : IsL3 ↥(lBar V₀ V hV L) 1 :=
    s16k_isLn_of_isSLn (by norm_num) hrow.1
  have hsimple : IsSimpleGroup ↥(lBar V₀ V hV L) := isSimpleGroup_of_isL3 hL3
  have hcard : Nat.card (lBar V₀ V hV L) = 168 := card_eq_of_isL3 hL3
  have hthree : 3 ∣ Nat.card (lBar V₀ V hV L) := by
    rw [hcard]
    norm_num
  have hnine : ¬ 3 ^ 2 ∣ Nat.card (lBar V₀ V hV L) := by
    rw [hcard]
    norm_num
  have hm : MBarGT D.M V₀ V 2 :=
    s168e3_mBarGT_two_of_sl_three_sum_three c hcomp hthin hrow
  have hP : T3Parab
      (⨆ g : ↥(Mbar D.M V₀ V hV),
        (lBar V₀ V hV L).map
          (MulAut.conj (g : MulAut (Vtil V₀ V hV))).toMonoidHom)
      (barSub V₀ V hV D.T) 3 :=
    s168e3_sl_three_orbit_three_parabolic c hcomp hs hrow
  exact s168e3_false_of_three_orbit_parabolic c h82 hcomp hsimple hthin hs hthree hnine hm hP

theorem s168e3_concl163F_of_sl_three_sum_three
    {G : Type} [Group G] [Finite G]
    {D : UC22.Data G} {V₀ V L : Subgroup G} {hV : IsElemAbelian 2 V}
    (c : S168e3Ctx D V₀ V L hV)
    (h82 : F08.R82 D)
    (hcomp : IsComponentOf (lBar V₀ V hV L) (Mbar D.M V₀ V hV))
    (hrow : s16h_H5L3Sum (lBar V₀ V hV L)
      (wTil V₀ V hV L)
      (wTil V₀ V hV L ⊓ fixV (lBar V₀ V hV L)) 3) :
    Concl163F D V₀ V hV L := by
  let H := lBar V₀ V hV L
  let A := Mbar D.M V₀ V hV
  let U := wTil V₀ V hV L
  let Z := U ⊓ fixV H
  have hL3 : IsL3 ↥H 1 := s16k_isLn_of_isSLn (by norm_num) hrow.1
  obtain ⟨t, hc⟩ := s168e3_exists_H5Cfg c hcomp hL3
  have hs_le : s15 D.M V₀ V hV L ≤ 3 := s168e3_s_le_three c hcomp hL3
  have hs_ge : 1 ≤ s15 D.M V₀ V hV L := Om8Excl.one_le_s15 D.M V₀ V hV L
  have hs_cases : s15 D.M V₀ V hV L = 1 ∨ s15 D.M V₀ V hV L = 2 ∨ s15 D.M V₀ V hV L = 3 := by
    omega
  rcases hs_cases with hs1 | hs2 | hs3
  ·
    have hshape : SumOfNatShape H U Z 3 := ⟨3, Or.inl hrow⟩
    have htrans : ∀ I₁ ∈ irrSet H, ∀ I₂ ∈ irrSet H,
        ∃ g ∈ A ⊓ Subgroup.normalizer (H : Set (MulAut (Vtil V₀ V hV))),
        I₂ = I₁.map g.toMonoidHom := by
      rcases hc.conc.2.2 with h1 | h2 | h3 | h4
      · exact (s16h_H5_not_pgroup hc h1).elim
      · exact (s16h_H5_not_tensor hc h2).elim
      · exact h3.2.2
      · exact s16h_trans_of_commSub_mem_irrSet hc.comp.2.2 h4.1
    exact s168e3_concl163F_of_sum_three_l3_of_s15_eq_one c hcomp hshape htrans hs1 hL3
  ·
    have hcase5 : Case163_5 D V₀ V hV L := s168e3_case163_5_of_sum_three_l3 c hs2 hL3 hrow.2
    exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hcase5)))))
  ·
    exact (s168e3_s15_ne_three_of_sl_three_sum_three c h82 hcomp hc.thin hrow hs3).elim

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
