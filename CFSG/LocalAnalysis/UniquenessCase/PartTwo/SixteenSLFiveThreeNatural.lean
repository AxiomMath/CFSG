module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenSpOmegaThreeNatural
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenAltSixSevenNaturalR880
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenThreeL5Conjugates
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenNaturalThreeCentralizerRank
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC1677ThreeNatThree

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22

theorem s168e3_false_of_sum_three_sl_five
    {G : Type} [Group G] [Finite G]
    {D : Data G} {V₀ V L : Subgroup G} {hV : IsElemAbelian 2 V}
    (c : S168e3Ctx D V₀ V L hV)
    (h880 : CFSG.LocalAnalysis.UniquenessCase.UC22.F08.R880 D)
    (hcomp : IsComponentOf (lBar V₀ V hV L) (Mbar D.M V₀ V hV))
    (hsum : SumOfNatShape (lBar V₀ V hV L) (wTil V₀ V hV L)
      (wTil V₀ V hV L ⊓ fixV (lBar V₀ V hV L)) 3)
    (htrans : ∀ I₁ ∈ irrSet (lBar V₀ V hV L),
      ∀ I₂ ∈ irrSet (lBar V₀ V hV L),
      ∃ g ∈ Mbar D.M V₀ V hV ⊓ Subgroup.normalizer
        (lBar V₀ V hV L : Set (MulAut (Vtil V₀ V hV))),
        I₂ = I₁.map g.toMonoidHom)
    (hSL : IsSLn ↥(lBar V₀ V hV L) 5 1) :
    False := by
  have hLn : IsLn ↥(lBar V₀ V hV L) 5 1 := s16k_isLn_of_isSLn (by norm_num) hSL
  have hs : s15 D.M V₀ V hV L = 1 := s15_eq_one_of_l5_component_at_three c hcomp hLn
  have hT := s168e3_threeNat_of_s15_eq_one c hcomp hsum htrans hs
  have hsp : CFSG.RankThree.PartOne.IsStronglyPEmbedded 3 D.M :=
    isStronglyPEmbedded_three_of_r880 c.setting.hyp16.hyp125 c.std.h127 c.std.h119 h880 hcomp
      (Or.inr (Or.inr (Or.inr hLn)))
  have hsimple : IsSimpleGroup ↥(lBar V₀ V hV L) := s16c167_cfg2_simple_ln hLn
  have hcover := cover_center_three_free_of_isSLn (by norm_num) hSL
  have hcard : Nat.card ↥(lBar V₀ V hV L) = 9999360 := by
    obtain ⟨K, hKf, hKfin, hKcard, ⟨e⟩⟩ := hSL
    let : Field K := hKf
    let : Finite K := hKfin
    have hK2 : Nat.card K = 2 := by simpa using hKcard
    rw [Nat.card_congr e.toEquiv,
      CFSG.Open.StatedAPI.card_statedSL_eq_prod (K := K) (d := 5) (by norm_num), hK2]
    decide +kernel
  have hE := hT.t3EngineBranch_of_card (by rw [hcard]; decide +kernel)
  exact s168e3_false_of_t3EngineBranch_of_stronglyEmbedded c hcomp hT hsp hsimple hcover hE

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
