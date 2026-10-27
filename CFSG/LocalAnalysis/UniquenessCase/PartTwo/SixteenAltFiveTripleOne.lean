module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC1677ThreeDefs
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenH154E3AltBridge
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenNaturalThreeAltFiveContext
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenNaturalThreeAltFiveCentralizer
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenNaturalThreeAltFiveLift
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.InP11OfStrongly
import CFSG.GroupTheory.PRankBound

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22

variable {G : Type} [Group G] [Finite G]

theorem s168e3_false_of_sum_three_alt_five_of_v0_ne_bot
    {D : UC22.Data G} {V₀ V L : Subgroup G} {hV : IsElemAbelian 2 V}
    (c : S168e3Ctx D V₀ V L hV)
    (hcomp : IsComponentOf (lBar V₀ V hV L) (Mbar D.M V₀ V hV))
    (hrow : s16h_H5A5Sum (lBar V₀ V hV L)
      (wTil V₀ V hV L)
      (wTil V₀ V hV L ⊓ fixV (lBar V₀ V hV L)) 3)
    (hs : s15 D.M V₀ V hV L = 1)
    (hV₀ : V₀ ≠ ⊥) : False := by
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
  have hthin : ∀ q : ℕ, q.Prime → q ≠ 2 → CFSG.Open.pRank q H ≤ 1 := by
    intro q hq hq2
    refine CFSG.GroupTheory.pRank_le_of_not_dvd_pow_succ (H := H) (p := q) (k := 1) hq ?_
    have h60 : 2 ^ 2 * ([3, 5] : List ℕ).prod = 60 := by norm_num
    have hl : ∀ p ∈ ([3, 5] : List ℕ), p.Prime := by
      intro p hp
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
      rcases hp with rfl | rfl
      · exact Nat.prime_three
      · exact Nat.prime_five
    have hnd : ([3, 5] : List ℕ).Nodup := by decide
    have hcop : Nat.Coprime q (2 ^ 2) :=
      CFSG.SectionRank.coprime_pow_of_ne hq Nat.prime_two hq2 2
    have hnot : ¬ q ^ 2 ∣ 2 ^ 2 * ([3, 5] : List ℕ).prod :=
      CFSG.SectionRank.not_sq_dvd_of_factorization hq hcop [3, 5] hl hnd
    rw [h60] at hnot
    rw [hcardH]
    simpa using hnot
  obtain ⟨hT, h7, hsig, hm⟩ :=
    s168e3_threeNat_data_of_sum_three_alt_five_of_s15_eq_one c hcomp hthin hA5 hsum hs
  have h3 : 3 ∈ D.sig := by
    rw [hsig]
    exact Set.mem_singleton 3
  obtain ⟨hK, -⟩ := s168e3_kBar_card_and_simple_of_threeNat_alt_five c hT h7 hA5 h3
  obtain ⟨Y, hYM, hY3, -, hYexp, hYnc, hperm⟩ :=
    s168e3_exists_permuting_nine_of_threeNat_isAlt_five c hT hA5 h7 hK
  have hσ : D.sig = D.sig1 := c.std.h1219 V₀ V c.setting.hyp16.hyp125
  have hstr : CFSG.RankThree.PartOne.IsStronglyPEmbedded 3 D.M :=
    c.std.hSg.sig1_sp 3 (hσ ▸ h3)
  have hk : D.k = 1 := Data.k_eq_one_of_three_mem D c.std.hSg hσ h3
  have hP11 : F11.InP11 D Y :=
    inP11_of_strongly Nat.prime_three (by norm_num) hstr hYM hY3 hYexp hYnc hperm
  have hPStar : InPStar D V₀ Y := (inPStar_iff_of_ne_bot hV₀ Y).2 hP11
  have hmK : MBarGT D.M V₀ V (D.k + 1) := by
    rw [hk]
    exact hm
  exact twelve_twelve D c.std.h63 c.std.h126 c.std.h1211 c.std.h111 c.std.h6161ii
    c.setting.hyp16.hyp125 hmK Y hPStar

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
