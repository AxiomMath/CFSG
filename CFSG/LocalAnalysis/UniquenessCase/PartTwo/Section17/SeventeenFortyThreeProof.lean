module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section17.SeventeenFortyThree
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section17.SeventeenFortyTwoChev
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section17.SeventeenNineTransfer
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.GF2ThreeRankHolds
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.ShapeDisjoint
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section17.StatementsB
public import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.L2_5_19IdRank
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section17.SeventeenEight
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section17.TenFiveBridge
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.InP11OfStrongly
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.DataKParam
public import CFSG.Adapters.StatedPSLTwoSeven
public import CFSG.LocalAnalysis.SectionRank.QTK.J4InspA3
public import CFSG.CGT.PushingUpLit.CGT6.SixFourA8
public import CFSG.Quasithin.EmptyFaithful.R3cBase
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.GF2Perm.FamPSL
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.GF2Perm.FamPSp
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.GF2Perm.FamOmegaPlus
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.GF2Perm.FamExc
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.GF2Perm.FamPSU
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.GF2Perm.FamOmegaMinus
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.GF2Perm.FamTwistedE6
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.GF2Perm.OfTypeBridge

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.S17

open Subgroup CFSG.Open CFSG.LocalAnalysis.UniquenessCase.UC22
open CFSG.Blueprint (LieModel)
open scoped Pointwise commutatorElement

variable {G : Type} [Group G] [Finite G]

theorem list880_of_psl_five {X : Type} [Group X] (h : LieModel X .PSL 5 2 1) : F08.List880 X := by
  unfold F08.List880
  exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
    (Or.inr (Or.inl h)))))))))))

theorem not_isSpor_J2_of_psl_five {X : Type} [Group X] (h : LieModel X .PSL 5 2 1) :
    ¬ IsSpor X .J2 := by
  intro hJ2
  obtain ⟨e⟩ := hJ2
  have h1 : Nat.card X = 604800 := by
    rw [Nat.card_congr e.toEquiv]
    change Nat.card CFSG.Blueprint.NativeSporadic.J2 = 604800
    exact CFSG.RankThree.PartTwo.KFacts.KS14.card_nativeJ2
  have h2 : Nat.card X = 9999360 :=
    CFSG.SectionRank.QTK.card_psl_five_two
      (CFSG.Blueprint.LieModel.statedClassicalModel h (by decide))
  omega


theorem exists_permutes_noncyclic_three_of_calC (hKp : Inputs1719.K_GF2_permutability)
    {D : Data G} {L : Subgroup G} (hL : L ∈ calC D.M) (hchev : CIsChevOver (BarInf L) 1)
    (hpos : 2 < CFSG.Open.pRank 3 (⊤ : Subgroup (Bar2 L)) ∨
      LieModel (Bar2 L ⧸ Subgroup.center (Bar2 L)) .PSL 5 2 1) :
    ∃ X : Subgroup G, X ≤ D.M ∧ X ≠ ⊥ ∧ IsPGroup 3 ↥X ∧ (∀ x ∈ X, x ^ 3 = 1) ∧
      ¬ IsCyclic ↥X ∧ Permutes X D.T := by
  obtain ⟨t, m, hadm, hlie⟩ := hchev
  obtain ⟨e1⟩ := uc22p21k_barInf_equiv_of_calC hL
  refine exists_permutes_three_of_calC hL fun Y _ _ K hKn hKq hKodd ⟨e⟩ hcent hidx S hS => ?_
  let eZ : (↥K ⧸ Subgroup.center ↥K) ≃* (Bar2 L ⧸ Subgroup.center (Bar2 L)) :=
    QuotientGroup.congr _ _ e (Subgroup.map_center_eq e)
  refine hKp Y K hKn hKq hKodd ⟨t, m, hadm, LieModel.of_mulEquiv (e1.trans eZ.symm) hlie⟩
    (hpos.imp (fun h => ?_) (LieModel.of_mulEquiv eZ.symm)) hcent hidx S hS
  rwa [CFSG.SectionRank.pRank_top_eq_of_mulEquiv (by norm_num) e]


theorem false_of_k_one_of_permutes {D : Data G} {V₀ V L : Subgroup G} {hV : Hyp125 D V₀ V}
    (h17_1 : R17_1At D V₀ V hV) (hKp : Inputs1719.K_GF2_permutability)
    (hL : L ∈ calC D.M) (hchev : CIsChevOver (BarInf L) 1) (hk : D.k = 1)
    (hpos : 2 < CFSG.Open.pRank 3 (⊤ : Subgroup (Bar2 L)) ∨
      LieModel (Bar2 L ⧸ Subgroup.center (Bar2 L)) .PSL 5 2 1) : False := by
  have hstr : CFSG.RankThree.PartOne.IsStronglyPEmbedded 3 D.M := by
    by_contra h
    have h2 : D.k = 2 := (Data.k_eq_two_iff D).2 h
    omega
  obtain ⟨X, hXM, hXne, hXp, hXexp, hXnc, hperm⟩ :=
    exists_permutes_noncyclic_three_of_calC hKp hL hchev hpos
  exact false_of_k_eq_one_of_inP11 h17_1 hk
    (inP11_of_strongly Nat.prime_three (by norm_num) hstr hXM hXp hXexp hXnc hperm)

theorem seventeen_fortythree
    (D : Data G) (V₀ V : Subgroup G) (hV : Hyp125 D V₀ V)
    (h17_1 : R17_1At D V₀ V hV) (h5 : R17_5At D V₀ V) (h61 : R17_6_1At D V₀ V)
    (h63 : R17_6_3At D V₀ V) (h31 : R17_31At D V₀ V) (h32 : R17_32At D V₀ V)
    (h82 : F08.R82 D) (h880 : F08.R880 D) (hN : uc22p20rNativeGriess) :
    R17_43At D V₀ V := by
  have hKp : Inputs1719.K_GF2_permutability :=
    GF2Perm.k_GF2_permutability_of_ofType hN (GF2Perm.k_GF2_permutabilityOfType_of_families
        GF2Perm.permWitnessPSL_holds GF2Perm.permWitnessPSU_holds GF2Perm.permWitnessPSp_holds
        GF2Perm.permWitnessOmegaPlus_holds GF2Perm.permWitnessOmegaMinus_holds
        GF2Perm.permWitnessExcUntwisted_holds GF2Perm.permWitnessTwistedE6_holds)
  intro L X p n l C Dc Gamma hC
  by_contra hle
  push Not at hle
  have hn1 : n = 1 := (Nat.pow_eq_self_iff (by norm_num)).1
    (le_antisymm hle (Nat.le_self_pow (by have := hC.one_le_exponent; omega) 2))
  have hcv1 : CIsChevOver (BarInf L) 1 := hn1 ▸ hC.chev
  have hodd : Odd (Nat.card (Subgroup.center (Bar2 L))) := uc22p22l_odd_center_quotient
  obtain ⟨t, m, hadm, hmodel⟩ := id hcv1
  have hmodelBar2 : LieModel (Bar2 L ⧸ Subgroup.center (Bar2 L)) t m 2 1 :=
    LieModel.of_mulEquiv (uc22p21k_barInf_equiv_of_calC hC.mem_calC).some hmodel
  by_cases hm3 : 2 < CFSG.Open.pRank 3 (⊤ : Subgroup (Bar2 L))
  ·
    have hm3L : 2 < CFSG.Open.pRank 3 L := by
      rwa [CFSG.Quasithin.R3c.pRank_three_eq_pCore_quotient L]
    have hstr : CFSG.RankThree.PartOne.IsStronglyPEmbedded 3 D.M :=
      h82 L ⟨hC.mem_calC.1, hC.mem_calC.2.1, hm3L, Or.inl (s15_Three_qs_of_open hC.mem_calC.2.2)⟩
    have hk : D.k = 1 := Data.k_eq_one_of_isStronglyPEmbedded D hstr
    exact false_of_k_one_of_permutes h17_1 hKp hC.mem_calC hcv1 hk (Or.inl hm3)
  · push Not at hm3
    have hlist := Inputs1719.k_GF2_threeRank_of_native hN (Bar2 L) t m hadm hC.mem_calC.2.2
      hmodelBar2 hodd hm3
    rcases hlist with ⟨rfl, hm⟩ | rfl | rfl
    ·
      rcases hm with rfl | rfl | rfl
      ·
        have hSC : CFSG.Open.StatedClassicalModel (BarInf L) .PSL 3 2 1 :=
          CFSG.Blueprint.LieModel.statedClassicalModel hmodel (by decide)
        have h27 : CFSG.Open.StatedClassicalModel (BarInf L) .PSL 2 7 1 :=
          CFSG.Open.StatedAPI.statedClassicalModel_psl_two_seven_of_psl_three_two hSC
        have hadm27 : CFSG.Open.StatedLieAdmissible .PSL 2 7 1 :=
          ⟨Nat.prime_seven, le_rfl, by norm_num, by decide, by decide⟩
        have hchev7 : IsChev (BarInf L) 7 :=
          ⟨.PSL, 2, 1, hadm27, Or.inl ⟨by decide, h27⟩⟩
        have hL2 : IsL2Over17 (Bar2 L) 7 := h61 L hC.mem_calC 7 (by norm_num) hchev7
        have hL2odd : IsL2Odd (Bar2 L) 7 := by
          obtain ⟨r, f, hr, hr2, hq, hf, hm⟩ := hL2
          obtain ⟨rfl, rfl⟩ := Nat.prime_seven.pow_eq_iff.1 hq.symm
          exact hm
        have hthinL : F08.Thin8 L := fun q hq hq2 => by
          rw [← s13_pRank_bar_top hq hq2 L]
          exact CFSG.QuasithinUnique.Id2519.pRank_le_one_psl_two_prime Nat.prime_seven
            (by norm_num) (LieModel.statedClassicalModel_of_ne_zero (by norm_num) hL2odd) hq hq2
        have hm3one : CFSG.Open.pRank 3 L = 1 :=
          le_antisymm (hthinL 3 Nat.prime_three (by norm_num))
            (s13_one_le_pRank_of_dvd L Nat.prime_three
              ((UC22.three_dvd_card_of_isL2Odd (by norm_num) hL2odd).trans
                (Subgroup.card_quotient_dvd_card _)))
        obtain ⟨⟨K₀, hK₀, huniq₀⟩, -⟩ :=
          h63 L hC.mem_calC 7 (by norm_num) hchev7 (by norm_num)
        have huniq : ∀ K ∈ calC D.M, F08.Thin8 K → CFSG.Open.pRank 3 K = 1 → K = L := by
          intro K hK hthinK hm3K
          exact (huniq₀ K ⟨hK, hthinK, hm3K⟩).trans
            (huniq₀ L ⟨hC.mem_calC, hthinL, hm3one⟩).symm
        exact false_of_concl_of_unique_thin hC.mem_calC hC.X_eq hthinL hm3one huniq
          hC.counter
      ·
        have hSC : CFSG.Open.StatedClassicalModel (BarInf L) .PSL 4 2 1 :=
          CFSG.Blueprint.LieModel.statedClassicalModel hmodel (by decide)
        obtain ⟨e1⟩ := barO2Z17_equiv_barInf hC.mem_calC
        obtain ⟨e2⟩ :=
          CFSG.CGT.PushingUpLit.CGT6.nonempty_mulEquiv_alt_eight_of_psl_four_two hSC
        exact h5 L hC.mem_calC 8 (by norm_num) ⟨e1.trans e2⟩
      ·
        have hZbot : Subgroup.center (Bar2 L) = ⊥ :=
          uc22p20v_center_eq_bot hN hC.mem_calC.2.2 hodd hmodelBar2
            (by simp [CFSG.Blueprint.Multiplier.genericOrders])
        have hmodelBar : LieModel (Bar2 L) .PSL 5 2 1 :=
          LieModel.of_mulEquiv
            ((QuotientGroup.quotientMulEquivOfEq hZbot).trans QuotientGroup.quotientBot)
            hmodelBar2
        have hk : D.k = 1 := k_eq_one_of_list880 h880 hC.mem_calC
          (list880_of_psl_five hmodelBar) (not_isSpor_J2_of_psl_five hmodelBar)
        exact false_of_k_one_of_permutes h17_1 hKp hC.mem_calC hcv1 hk (Or.inr hmodelBar2)
    ·
      have hm0 : m = 0 := by simpa using hadm.2.2
      subst hm0
      have hZbot : Subgroup.center (Bar2 L) = ⊥ :=
        uc22p20v_center_eq_bot hN hC.mem_calC.2.2 hodd hmodelBar2
          (by simp [CFSG.Blueprint.Multiplier.genericOrders])
      have h3d : Is3D4 (Bar2 L) 1 :=
        LieModel.of_mulEquiv
          ((QuotientGroup.quotientMulEquivOfEq hZbot).trans QuotientGroup.quotientBot)
          hmodelBar2
      exact h32 L hC.mem_calC 1 h3d
    ·
      have hm0 : m = 0 := by simpa using hadm.2.2
      subst hm0
      have hZbot : Subgroup.center (Bar2 L) = ⊥ :=
        uc22p20v_center_eq_bot hN hC.mem_calC.2.2 hodd hmodelBar2
          (by simp [CFSG.Blueprint.Multiplier.genericOrders])
      have htits : LieModel (Bar2 L) .Tits 0 2 1 :=
        LieModel.of_mulEquiv
          ((QuotientGroup.quotientMulEquivOfEq hZbot).trans QuotientGroup.quotientBot)
          hmodelBar2
      exact (h31 L hC.mem_calC).2 htits

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.S17
