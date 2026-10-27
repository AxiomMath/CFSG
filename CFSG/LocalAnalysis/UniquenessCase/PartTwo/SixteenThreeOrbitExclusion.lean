module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC1677ThreeDefs
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenEightS1T3Par
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenThreeConjugateCover
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenH154AssemblyCTA
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.InP11OfStrongly
import CFSG.LocalAnalysis.AGLEmbeddingD2.McLaughlin.OrdinaryProofs.CentreTransfer

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22

variable {G : Type} [Group G] [Finite G]

theorem s168e3_false_of_three_orbit_parabolic
    {D : UC22.Data G} {V₀ V L : Subgroup G} {hV : IsElemAbelian 2 V}
    (c : S168e3Ctx D V₀ V L hV)
    (h82 : F08.R82 D)
    (hcomp : IsComponentOf (lBar V₀ V hV L) (Mbar D.M V₀ V hV))
    (hsimple : IsSimpleGroup (lBar V₀ V hV L))
    (hthin : ∀ q : ℕ, q.Prime → q ≠ 2 → CFSG.Open.pRank q (lBar V₀ V hV L) ≤ 1)
    (hs : s15 D.M V₀ V hV L = 3)
    (hthree : 3 ∣ Nat.card (lBar V₀ V hV L))
    (hnine : ¬ 3 ^ 2 ∣ Nat.card (lBar V₀ V hV L))
    (hm : UC22.MBarGT D.M V₀ V 2)
    (hP : T3Parab
      (⨆ g : ↥(Mbar D.M V₀ V hV),
        (lBar V₀ V hV L).map
          (MulAut.conj (g : MulAut (Vtil V₀ V hV))).toMonoidHom)
      (barSub V₀ V hV D.T) 3) :
    False := by
  classical
  have hcover : ∀ (Q : Type) [Group Q] [Finite Q],
      CFSG.Open.IsQuasisimple Q →
      Nonempty ((Q ⧸ Subgroup.center Q) ≃* ↥(lBar V₀ V hV L)) →
      ¬ 3 ∣ Nat.card (Subgroup.center Q) := by
    intro Q _ _ hQ hquot
    obtain ⟨e⟩ := hquot
    refine @CFSG.AGLEmbeddingD2.McLaughlin.not_dvd_card_center_of_perfect Q _ _ hQ.1 3
      ⟨Nat.prime_three⟩ ?_
    rw [Nat.card_congr e.toEquiv]
    exact hnine
  obtain ⟨K, hK, -, hKbar, -⟩ :=
    s168e3_exists_cover_prime_free c hcomp hsimple Nat.prime_three (by norm_num) hcover
  have hKrank : CFSG.Open.pRank 3 K = 1 := by
    obtain ⟨t, -, -, -, -, hW⟩ := c.conc
    exact s16h_pRank_three_eq_one_of_thin_cover D c.setting hcomp hW hthin hthree hK hKbar
  have hstr : CFSG.RankThree.PartOne.IsStronglyPEmbedded 3 D.M :=
    s16h_stronglyEmbedded_of_pRank_one_cover D h82 c.setting (by simp [hs]) hK hKbar hKrank
  obtain ⟨C, hCM, hCnorm, hCbar, hC3⟩ :=
    s168e3_exists_normal_orbit_cover_three_free c hcomp hsimple hs hcover
  obtain ⟨J, hTJ, hJB, hJcard, hJexp⟩ := hP
  obtain ⟨Y, hYM, hY3, hYcard, hYexp, hYnc, hperm⟩ :=
    s168e3_exists_permuting_of_normal_subgroup_three_free c hCM hCnorm hC3
      hTJ (by simpa only [hCbar] using hJB) hJcard (by norm_num : 2 ≤ 3) hJexp
  have hk : D.k = 1 := Data.k_eq_one_of_isStronglyPEmbedded D hstr
  have hmK : MBarGT D.M V₀ V (D.k + 1) := by
    rw [hk]
    exact hm
  have hP11 : F11.InP11 D Y :=
    inP11_of_strongly Nat.prime_three (by norm_num) hstr hYM hY3 hYexp hYnc hperm
  have hPstar : InPStar D V₀ Y :=
    ⟨hP11, fun _ =>
      ⟨3, Nat.prime_three, hY3, Or.inl (by rw [hYcard]; norm_num)⟩⟩
  exact twelve_twelve D c.std.h63 c.std.h126 c.std.h1211
    c.std.h111 c.std.h6161ii c.setting.hyp16.hyp125 hmK Y hPstar

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
