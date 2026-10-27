module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenSeven2EighteenCfg2Simple
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenSimpleComponentRank
public import CFSG.RankThree.PartOne.KF.ClsPOmegaMinus
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.CenterHopf

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22

theorem s16nt_s15_eq_one_of_alt_nine_eleven
    {G : Type} [Group G] [Finite G]
    {D : Data G} {V₀ V L : Subgroup G} {hV : IsElemAbelian 2 V}
    (c : S168e3Ctx D V₀ V L hV)
    (hcomp : IsComponentOf (lBar V₀ V hV L) (Mbar D.M V₀ V hV))
    {n : ℕ} (hn9 : 9 ≤ n) (hn11 : n ≤ 11)
    (hA : UC22.IsAlt ↥(lBar V₀ V hV L) n) :
    s15 D.M V₀ V hV L = 1 := by
  have hsimple : IsSimpleGroup ↥(lBar V₀ V hV L) :=
    s16c167_cfg2_simple_alt (by omega) hA
  have hA' := hA
  obtain ⟨eA⟩ := hA'
  have hrank : 3 ≤ CFSG.Open.pRank 3 (⊤ : Subgroup ↥(lBar V₀ V hV L)) :=
    calc 3 ≤ CFSG.Open.pRank 3 (⊤ : Subgroup (alternatingGroup (Fin n))) :=
          CFSG.SectionRank.three_le_pRank_alternating (by omega)
      _ = CFSG.Open.pRank 3 (⊤ : Subgroup ↥(lBar V₀ V hV L)) :=
          (CFSG.SectionRank.pRank_top_eq_of_mulEquiv (p := 3) (by norm_num) eA).symm
  have hcover : ∀ (Q : Type) [Group Q] [Finite Q], CFSG.Open.IsQuasisimple Q →
      Nonempty ((Q ⧸ Subgroup.center Q) ≃* ↥(lBar V₀ V hV L)) →
      IsPGroup 2 ↥(Subgroup.center Q) := by
    intro Q _ _ hQ ⟨eQ⟩
    have hperf : Group.IsPerfect Q := Group.isPerfect_def.mpr hQ.1
    have hcardA : Nat.card (CFSG.Open.griessHopfMultiplier (alternatingGroup (Fin n))) = 2 := by
      rw [Nat.card_congr (CFSG.RankThree.PerfectCover.hopfMultiplierEquivGriess
        (alternatingGroup (Fin n))).toEquiv,
        CFSG.Alternating.Multipliers.card_hopfMultiplier_alternatingGroup (n := n) (by omega)]
    have hdvdM : Nat.card (CFSG.Open.griessHopfMultiplier (alternatingGroup (Fin n))) ∣ 2 := by
      simp [hcardA]
    have hdvd := (CFSG.AGLEmbedding.card_center_dvd_card_griessHopfMultiplier
      (Q := Q) (S := alternatingGroup (Fin n)) hperf (eQ.trans eA)).trans hdvdM
    exact IsPGroup.of_card_dvd_pow (n := 1) (by simpa using hdvd)
  have hs : s15 D.M V₀ V hV L = 1 :=
    s15_eq_one_of_simple_component_of_three_rank c hcomp hsimple (r := 3) (by norm_num)
      hrank hcover
  exact hs

theorem s16nt_s15_eq_one_of_omega_minus_eight
    {G : Type} [Group G] [Finite G]
    {D : Data G} {V₀ V L : Subgroup G} {hV : IsElemAbelian 2 V}
    (c : S168e3Ctx D V₀ V L hV)
    (hcomp : IsComponentOf (lBar V₀ V hV L) (Mbar D.M V₀ V hV))
    (hOm8 : IsOmegaMinus ↥(lBar V₀ V hV L) 8 1) :
    s15 D.M V₀ V hV L = 1 := by
  have hsimple : IsSimpleGroup ↥(lBar V₀ V hV L) :=
    s16c167_cfg2_simple_omegaMinus_eight hOm8
  have hOm8' := hOm8
  obtain ⟨-, K, hKf, hKfin, b₀, c₀, hKcard, hirr, ⟨e⟩⟩ := hOm8'
  have : Fintype K := Fintype.ofFinite K
  have hK2 : Nat.card K = 2 := by simpa using hKcard
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : CharP K 2 := charP_of_card_eq_prime (p := 2)
    (by rw [Fintype.card_eq_nat_card, hK2])
  have hrank : 3 ≤ CFSG.Open.pRank 3 (⊤ : Subgroup ↥(lBar V₀ V hV L)) :=
    calc 3 ≤ CFSG.Open.pRank 3
          (⊤ : Subgroup (StatedProj (StatedOmega (StatedQuadMinus 4 K b₀ c₀)))) :=
          CFSG.SectionRank.ClassicalEven.omegaMinus_three_le_pRank_three
            (K := K) (n := 4) (by norm_num) b₀ c₀
      _ = CFSG.Open.pRank 3 (⊤ : Subgroup ↥(lBar V₀ V hV L)) :=
          (CFSG.SectionRank.pRank_top_eq_of_mulEquiv (p := 3) (by norm_num) e).symm
  have hclass : StatedClassicalModel ↥(lBar V₀ V hV L) .POmegaMinus 4 2 1 :=
    ⟨⟨Nat.prime_two, by norm_num, by norm_num⟩, K, hKf, hKfin, by simpa using hKcard,
      b₀, c₀, hirr, ⟨e⟩⟩
  have hcover : ∀ (Q : Type) [Group Q] [Finite Q], CFSG.Open.IsQuasisimple Q →
      Nonempty ((Q ⧸ Subgroup.center Q) ≃* ↥(lBar V₀ V hV L)) →
      IsPGroup 2 ↥(Subgroup.center Q) := by
    intro Q _ _ hQ ⟨eQ⟩
    have hperf : Group.IsPerfect Q := Group.isPerfect_def.mpr hQ.1
    obtain ⟨-, ⟨eM⟩⟩ := CFSG.LieType.Steinberg.CentralExt.GriessClassical.pomegaMinus_row
      (X := ↥(lBar V₀ V hV L)) hclass
    have hcardM : Nat.card (CFSG.Open.griessHopfMultiplier ↥(lBar V₀ V hV L)) = 1 := by
      rw [Nat.card_congr eM.toEquiv]
      exact CFSG.RankThree.PartOne.KFU.card_multiplier_pOmegaMinus (n := 4) (f := 1)
        (by norm_num) (by norm_num)
    have hdvd : Nat.card (Subgroup.center Q) ∣ 1 := by
      simpa [hcardM] using
        (CFSG.AGLEmbedding.card_center_dvd_card_griessHopfMultiplier
          (Q := Q) (S := ↥(lBar V₀ V hV L)) hperf eQ)
    exact IsPGroup.of_card_dvd_pow (n := 0) (by simpa using hdvd)
  have hs : s15 D.M V₀ V hV L = 1 :=
    s15_eq_one_of_simple_component_of_three_rank c hcomp hsimple (r := 3) (by norm_num)
      hrank hcover
  exact hs

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
