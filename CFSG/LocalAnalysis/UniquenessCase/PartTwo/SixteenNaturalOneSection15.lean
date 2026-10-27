module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC1677ThreeTools
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.FifteenThreeC2
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.FifteenKTable
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.FifteenKRank3List
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.FifteenKAbsIrr
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.FifteenThreeSimple
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenNaturalComponentShape

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22
open scoped commutatorElement Pointwise

theorem s168e3_shape_self_of_s15_eq_one
    {G : Type} [Group G] [Finite G]
    {D : Data G} {V₀ V L : Subgroup G} {hV : IsElemAbelian 2 V}
    (c : S168e3Ctx D V₀ V L hV)
    (hcomp : IsComponentOf (lBar V₀ V hV L) (Mbar D.M V₀ V hV))
    (hs : s15 D.M V₀ V hV L = 1)
    (hperf : s15KNatPerf ↥(lBar V₀ V hV L)
      (lStar D.M V₀ V hV L) (wStar D.M V₀ V hV L)) :
    s15Shape D V₀ V hV L L := by
  exact s168e3_shape_self_of_natPerf c hcomp hperf

theorem s168e3_three_mem_sig_of_natural_aut_rank
    {G : Type} [Group G] [Finite G]
    {D : Data G} {V₀ V L : Subgroup G} {hV : IsElemAbelian 2 V}
    (c : S168e3Ctx D V₀ V L hV)
    (hs : s15 D.M V₀ V hV L = 1)
    (hperf : s15KNatPerf ↥(lBar V₀ V hV L)
      (lStar D.M V₀ V hV L) (wStar D.M V₀ V hV L))
    (hAut : ∀ p : ℕ, p.Prime → p ≠ 2 → p ≠ 3 →
      CFSG.Open.pRank p (⊤ : Subgroup (MulAut ↥(lBar V₀ V hV L))) ≤ 1) :
    3 ∈ D.sig := by
  have hCent : Mbar D.M V₀ V hV ⊓
      Subgroup.centralizer (lBar V₀ V hV L : Set (MulAut (Vtil V₀ V hV))) = ⊥ := by
    rw [Subgroup.eq_bot_iff_forall]
    intro x hx
    exact s15_Three_Mbar_centralizer rAbsIrr153_holds D c.std.h1217 c.setting.hyp151 hV
      c.ne hs hperf x hx.1
      (fun y hy => (Subgroup.mem_centralizer_iff.mp hx.2 y hy).symm)
  obtain ⟨p, hpSig⟩ := c.std.hx.sig_nonempty
  by_contra h3
  have hp3 : p ≠ 3 := fun hp => h3 (hp ▸ hpSig)
  obtain ⟨hpPrime, hp2⟩ := D.sig_prime p hpSig
  have hRank := CFSG.AGLEmbedding.pRank_le_pRank_inf_centralizer_add_pRank_mulAut
    (X := MulAut (Vtil V₀ V hV)) (K := lBar V₀ V hV L) (R := Mbar D.M V₀ V hV)
    hpPrime (s15_Three_le_normalizer hs)
  rw [hCent, CFSG.AGLEmbedding.pRank_bot_eq_zero (X := MulAut (Vtil V₀ V hV)) hpPrime,
    zero_add] at hRank
  have hle := hAut p hpPrime hp2 hp3
  have h2 := c.two_le_pRank_mbar hpSig
  omega

theorem s15ExcList_card_le
    {X : Type} [Group X] [Finite X]
    (h : s15ExcList X) : Nat.card X ≤ 25920 := by
  rcases h with h | h | h | h | h | h
  · rw [CFSG.Blueprint.LieModel.card_psl_three_two h]
    norm_num
  · rw [s16c167_card_isLn_four h]
    norm_num
  · have h2 := s16c167_two_mul_card_isAlt (n := 5) (by norm_num) h
    rw [show Nat.factorial 5 = 120 by decide] at h2
    omega
  · rw [s16c167_card_isAlt_six h]
    norm_num
  · rw [s16c167_card_isAlt_seven h]
    norm_num
  · rw [s16c167_card_isOmegaMinus_six h]

theorem s168e3_concl163F_of_natural_perfect
    {G : Type} [Group G] [Finite G]
    {D : Data G} {V₀ V L : Subgroup G} {hV : IsElemAbelian 2 V}
    (c : S168e3Ctx D V₀ V L hV)
    (hcomp : IsComponentOf (lBar V₀ V hV L) (Mbar D.M V₀ V hV))
    (hs : s15 D.M V₀ V hV L = 1)
    (hperf : s15KNatPerf ↥(lBar V₀ V hV L)
      (lStar D.M V₀ V hV L) (wStar D.M V₀ V hV L))
    (hnot : ¬ s15ExcList ↥(lBar V₀ V hV L))
    (h3 : 3 ∈ D.sig) :
    Concl163F D V₀ V hV L := by
  have hshape : s15Shape D V₀ V hV L L :=
    s168e3_shape_self_of_s15_eq_one c hcomp hs hperf
  have hperfComm : s15KNatPerf ↥(barSub V₀ V hV L)
      (barSub (v1Sub D.M V₀ V hV L) V hV L)
      (commSub ⊤ (barSub (v1Sub D.M V₀ V hV L) V hV L)) := by
    change s15KNatPerf ↥(lBar V₀ V hV L) (lStar D.M V₀ V hV L)
      (commSub ⊤ (lStar D.M V₀ V hV L))
    rw [s15_Three_commSub_top_lStar c.setting.hyp151 hV]
    exact hperf
  have hO1 := s15_Three_O1a rTable137_holds rRank3List153_holds rAbsIrr153_holds
    rSimple153_holds c.std.h127 c.std.h119 c.std.h1217 c.setting.hyp151 hV c.ne hshape
    hperfComm (fun h => hnot h.2)
  exact False.elim ((s15_Three_not_O1a_of_unique
    c.std.h61 c.std.h63 c.std.h127 c.setting.hyp151.hyp125 (Or.inl h3)) hO1)

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
