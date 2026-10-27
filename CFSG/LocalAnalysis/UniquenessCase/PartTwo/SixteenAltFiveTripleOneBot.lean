module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC1677ThreeDefs
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenH154E3AltBridge
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenH154E3Engine
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenNaturalThreeAltFiveContext
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenNaturalThreeAltFiveCentralizer
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenNaturalThreeAltFiveLift
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenNaturalThreeAltFiveOne
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenSmallComponentBounds

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22

variable {G : Type} [Group G] [Finite G]

theorem s168e3_false_of_sum_three_alt_five_of_v0_eq_bot
    {D : UC22.Data G} {V₀ V L : Subgroup G} {hV : IsElemAbelian 2 V}
    (c : S168e3Ctx D V₀ V L hV)
    (hcomp : IsComponentOf (lBar V₀ V hV L) (Mbar D.M V₀ V hV))
    (hrow : s16h_H5A5Sum (lBar V₀ V hV L)
      (wTil V₀ V hV L)
      (wTil V₀ V hV L ⊓ fixV (lBar V₀ V hV L)) 3)
    (hs : s15 D.M V₀ V hV L = 1)
    (hV₀ : V₀ = ⊥) : False := by
  classical
  let H : Subgroup (MulAut (Vtil V₀ V hV)) := lBar V₀ V hV L
  let U : Subgroup (Vtil V₀ V hV) := wTil V₀ V hV L
  let Z : Subgroup (Vtil V₀ V hV) := U ⊓ fixV H
  have hrow' : s16h_H5A5Sum H U Z 3 := by
    simpa only [H, U, Z] using hrow
  obtain ⟨hA5, hsum⟩ := s16h_a5Sum_alt hrow'
  have hcardH : Nat.card ↥H = 60 := by
    rw [s15k_six_alt_card hA5 (by norm_num : 2 ≤ 5)]
    norm_num [Nat.factorial]
  have hthin : ∀ q : ℕ, q.Prime → q ≠ 2 → CFSG.Open.pRank q H ≤ 1 :=
    fun q hq hq2 => pRank_le_one_of_card_eq_sixty hcardH hq hq2
  obtain ⟨hT, h7, hsig, hm⟩ :=
    s168e3_threeNat_data_of_sum_three_alt_five_of_s15_eq_one c hcomp hthin hA5 hsum hs
  have h3 : 3 ∈ D.sig := by
    rw [hsig]
    exact Set.mem_singleton 3
  obtain ⟨hK, -⟩ := s168e3_kBar_card_and_simple_of_threeNat_alt_five c hT h7 hA5 h3
  obtain ⟨Y, hYM, hY3, -, hYexp, hYnc, hperm⟩ :=
    s168e3_exists_permuting_nine_of_threeNat_isAlt_five c hT hA5 h7 hK
  obtain ⟨v, hvV, -, hvT, hvC⟩ :=
    s168e3_exists_good_vector_of_threeNat_alt_five c hT hA5 hsum h7 hK h3 hV₀
  have hσ : D.sig = D.sig1 := c.std.h1219 V₀ V c.setting.hyp16.hyp125
  exact false_of_permuting_three_of_weakClosure D c.std.hx c.std.hSg c.std.h61 c.std.h63
    c.std.h126 c.std.h1211 c.std.h111 c.std.h6161ii hσ c.setting h3 hm hYM hY3 hYexp hYnc
    hperm (Or.inr (Or.inr ⟨v, hvV, hvT, hvC⟩))

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
