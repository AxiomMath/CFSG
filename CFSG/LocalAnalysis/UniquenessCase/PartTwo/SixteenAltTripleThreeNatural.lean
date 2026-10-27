module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC1677ThreeNatThree
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenNaturalThreeAltCoverHyp81
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.TwelveThirteen
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.InP11OfStrongly

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22

theorem s168e3_false_of_sum_three_alt_ten_eleven
    {G : Type} [Group G] [Finite G]
    {D : Data G} {V₀ V L : Subgroup G} {hV : IsElemAbelian 2 V}
    (c : S168e3Ctx D V₀ V L hV)
    (hcomp : IsComponentOf (lBar V₀ V hV L) (Mbar D.M V₀ V hV))
    (hsum : SumOfNatShape (lBar V₀ V hV L) (wTil V₀ V hV L)
      (wTil V₀ V hV L ⊓ fixV (lBar V₀ V hV L)) 3)
    (htrans : ∀ I₁ ∈ irrSet (lBar V₀ V hV L),
      ∀ I₂ ∈ irrSet (lBar V₀ V hV L),
      ∃ g ∈ Mbar D.M V₀ V hV ⊓ Subgroup.normalizer
        (lBar V₀ V hV L : Set (MulAut (Vtil V₀ V hV))),
        I₂ = I₁.map g.toMonoidHom)
    (hs : s15 D.M V₀ V hV L = 1)
    {n : ℕ} (hn : n = 10 ∨ n = 11)
    (hAlt : UC22.IsAlt ↥(lBar V₀ V hV L) n)
    (h82 : UC22.F08.R82 D) : False := by
  obtain ⟨Y, hYM, -, hYnorm, -, -, -, -, -, -, hYAlt, -, -, hHyp, -, -⟩ :=
    s168e3_exists_alt_ten_eleven_cover_hyp81 c hcomp hs hn hAlt
  have hstr : CFSG.RankThree.PartOne.IsStronglyPEmbedded 3 D.M := h82 Y hHyp
  have hk : D.k = 1 := Data.k_eq_one_of_isStronglyPEmbedded D hstr
  have hm : MBarGT D.M V₀ V 2 :=
    mBarGT_two_of_threeNat c.setting (s168e3_threeNat_of_s15_eq_one c hcomp hsum htrans hs)
  have hXM : Y ⊔ D.T ≤ D.M := sup_le hYM D.sylowM.le
  have hXsn : CFSG.Open.IsSubnormal Y (Y ⊔ D.T) := by
    refine CFSG.Open.IsSubnormal.step le_sup_left ?_ (CFSG.Open.IsSubnormal.refl _)
    exact (Subgroup.normal_subgroupOf_iff_le_normalizer le_sup_left).2
      (hXM.trans ((Subgroup.normal_subgroupOf_iff_le_normalizer hYM).1 hYnorm))
  have h9 : n ≤ 9 :=
    twelve_thirteen_two D c.std.h63 c.std.h126 c.std.h127 c.std.h1211 c.std.h111
      c.std.h6161ii c.setting.hyp16.hyp125 (fun _ => by rw [hk]; exact hm) hXsn hXM hYAlt
      (fun P hP hP3 hnc hexp _ hperm =>
        inP11_of_strongly Nat.prime_three (by norm_num) hstr (hP.trans hXM) hP3 hexp hnc hperm)
  rcases hn with rfl | rfl <;> omega

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
