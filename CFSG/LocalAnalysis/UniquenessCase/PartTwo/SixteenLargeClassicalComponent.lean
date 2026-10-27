module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC1677ThreeDefs
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenClassicalCoverThreePart
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenEightS1T3Sig
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.ExceptionalComponentCover
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.FifteenKJPrimeLie
import CFSG.LieType.Steinberg.CentralExt.PSLCoverCenter

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22

private theorem s168e3_false_of_simple_component_four_rank
    {G : Type} [Group G] [Finite G] {D : Data G} {V₀ V L : Subgroup G}
    {hV : IsElemAbelian 2 V}
    (c : S168e3Ctx D V₀ V L hV)
    (hcomp : IsComponentOf (lBar V₀ V hV L) (Mbar D.M V₀ V hV))
    (hsimple : IsSimpleGroup ↥(lBar V₀ V hV L))
    (hrank : 4 ≤ CFSG.Open.pRank 3 (lBar V₀ V hV L))
    (hcover : ∀ (Q : Type) [Group Q] [Finite Q] [Group.IsPerfect Q],
      (Q ⧸ Subgroup.center Q) ≃* ↥(lBar V₀ V hV L) →
        ¬ 3 ∣ Nat.card (Subgroup.center Q)) : False := by
  obtain ⟨K, hK, -, ⟨eK⟩⟩ := exists_calC_cover_of_simple_component
    c.setting.hyp16.hyp125 c.std.h127 c.std.h119 hcomp hsimple
  haveI : Group.IsPerfect (Bar2 K) := ⟨hK.2.2.1⟩
  have hZ3 : ¬ 3 ∣ Nat.card (Subgroup.center (Bar2 K)) := hcover (Bar2 K) eK
  have h4K : 4 ≤ CFSG.Open.pRank 3 K := by
    rw [CFSG.Quasithin.R3c.pRank_three_eq_pCore_quotient K]
    rw [← CFSG.SectionRank.pRank_quotient_eq (Subgroup.center (Bar2 K)) hZ3]
    rw [CFSG.SectionRank.pRank_top_eq_of_mulEquiv (p := 3) (by norm_num) eK]
    rw [← CFSG.SectionRank.pRank_eq_pRank_top_subgroup (p := 3) (lBar V₀ V hV L)]
    exact hrank
  have hleM : CFSG.Open.pRank 3 K ≤ CFSG.Open.evenRank G :=
    (CFSG.SectionRank.pRank_mono (p := 3) (by norm_num) (A3.subnormal_le hK.1)).trans
      (CFSG.RankThreeCoreUniqueness.Helpers.local_pRank_le_evenRank 3 Nat.prime_three
        (by norm_num) D.M D.maxLocal.1)
  have hle3 : CFSG.Open.pRank 3 K ≤ 3 := by
    simpa only [c.std.h3] using hleM
  omega

theorem s168e3_false_of_sl_component_ge_eight
    {G : Type} [Group G] [Finite G] {D : Data G} {V₀ V L : Subgroup G}
    {hV : IsElemAbelian 2 V}
    (c : S168e3Ctx D V₀ V L hV)
    (hcomp : IsComponentOf (lBar V₀ V hV L) (Mbar D.M V₀ V hV))
    {n : ℕ} (hn : 8 ≤ n)
    (hSL : IsSLn ↥(lBar V₀ V hV L) n 1) : False := by
  have hsimple : IsSimpleGroup ↥(lBar V₀ V hV L) :=
    s16t3_isSimpleGroup_of_shape (Or.inl ⟨hSL, by omega⟩)
  have hrank : 4 ≤ CFSG.Open.pRank 3 (lBar V₀ V hV L) :=
    ThreeRankShape.four_le_pRank ⟨n, Or.inl ⟨hSL, hn⟩⟩
  refine s168e3_false_of_simple_component_four_rank c hcomp hsimple hrank ?_
  intro Q _ _ _ eQ
  obtain ⟨K, hKf, hKfin, hKcard, ⟨eH⟩⟩ := hSL
  letI : Field K := hKf
  letI : Finite K := hKfin
  haveI : Fintype K := Fintype.ofFinite K
  have hK2 : Nat.card K = 2 := by simpa using hKcard
  haveI : CharP K 2 :=
    charP_of_card_eq_prime (p := 2) (by rwa [← Nat.card_eq_fintype_card])
  have hf : StatedProj (StatedSL n K) ≃* ↥(StatedSL n K) :=
    (s15k_jp_projEquiv hK2 (StatedSL n K)).some
  have hQK : (Q ⧸ Subgroup.center Q) ≃* Matrix.ProjectiveSpecialLinearGroup (Fin n) K :=
    (eQ.trans (eH.trans hf.symm)).trans
      (CFSG.Assembly.LowTwoRank.projectiveSpecialLinearGroupEquivStatedProj n K).symm
  have hdvd := CFSG.LieType.Steinberg.CentralExt.SLClosed.card_center_dvd_gcd_of_psl_of_five_le
    (inferInstance : Group.IsPerfect Q) (by omega) hQK
  have hgcd : Nat.gcd n (Nat.card K - 1) = 1 := by
    rw [hK2]
    simp
  have hdiv1 : Nat.card (Subgroup.center Q) ∣ 1 := by
    simpa only [hgcd] using hdvd
  rw [Nat.dvd_one.mp hdiv1]
  norm_num

theorem s168e3_false_of_sp_component_ge_eight
    {G : Type} [Group G] [Finite G] {D : Data G} {V₀ V L : Subgroup G}
    {hV : IsElemAbelian 2 V}
    (c : S168e3Ctx D V₀ V L hV)
    (hcomp : IsComponentOf (lBar V₀ V hV L) (Mbar D.M V₀ V hV))
    {n : ℕ} (hn : 8 ≤ n)
    (hSp : IsSpn ↥(lBar V₀ V hV L) n 1) : False := by
  have hsimple : IsSimpleGroup ↥(lBar V₀ V hV L) :=
    s16t3_isSimpleGroup_of_shape (Or.inr (Or.inl ⟨hSp, by omega⟩))
  have hrank : 4 ≤ CFSG.Open.pRank 3 (lBar V₀ V hV L) :=
    ThreeRankShape.four_le_pRank ⟨n, Or.inr (Or.inl ⟨hSp, hn⟩)⟩
  refine s168e3_false_of_simple_component_four_rank c hcomp hsimple hrank ?_
  intro Q _ _ _ eQ
  obtain ⟨-, K, hKf, hKfin, hKcard, ⟨eH⟩⟩ := hSp
  letI : Field K := hKf
  letI : Finite K := hKfin
  haveI : Fintype K := Fintype.ofFinite K
  have hK2 : Nat.card K = 2 := by simpa using hKcard
  haveI : CharP K 2 :=
    charP_of_card_eq_prime (p := 2) (by rwa [← Nat.card_eq_fintype_card])
  exact s16lc_sp_center_three_free (m := n / 2) (F := K) (by omega) (eQ.trans eH)

theorem s168e3_false_of_omegaPlus_component_ge_eight
    {G : Type} [Group G] [Finite G] {D : Data G} {V₀ V L : Subgroup G}
    {hV : IsElemAbelian 2 V}
    (c : S168e3Ctx D V₀ V L hV)
    (hcomp : IsComponentOf (lBar V₀ V hV L) (Mbar D.M V₀ V hV))
    {n : ℕ} (hn : 8 ≤ n)
    (hOmega : IsOmegaPlus ↥(lBar V₀ V hV L) n 1) : False := by
  have hsimple : IsSimpleGroup ↥(lBar V₀ V hV L) :=
    s16t3_isSimpleGroup_of_shape (Or.inr (Or.inr (Or.inl ⟨hOmega, by omega⟩)))
  have hrank : 4 ≤ CFSG.Open.pRank 3 (lBar V₀ V hV L) :=
    ThreeRankShape.four_le_pRank ⟨n, Or.inr (Or.inr (Or.inl ⟨hOmega, hn⟩))⟩
  refine s168e3_false_of_simple_component_four_rank c hcomp hsimple hrank ?_
  intro Q _ _ _ eQ
  obtain ⟨-, K, hKf, hKfin, hKcard, ⟨eH⟩⟩ := hOmega
  letI : Field K := hKf
  letI : Finite K := hKfin
  haveI : Fintype K := Fintype.ofFinite K
  have hK2 : Nat.card K = 2 := by simpa using hKcard
  haveI : CharP K 2 :=
    charP_of_card_eq_prime (p := 2) (by rwa [← Nat.card_eq_fintype_card])
  exact s16lc_omegaPlus_center_three_free (m := n / 2) (F := K) (by omega) (eQ.trans eH)

theorem s168e3_false_of_omegaMinus_component_ge_ten
    {G : Type} [Group G] [Finite G] {D : Data G} {V₀ V L : Subgroup G}
    {hV : IsElemAbelian 2 V}
    (c : S168e3Ctx D V₀ V L hV)
    (hcomp : IsComponentOf (lBar V₀ V hV L) (Mbar D.M V₀ V hV))
    {n : ℕ} (hn : 10 ≤ n)
    (hOmega : IsOmegaMinus ↥(lBar V₀ V hV L) n 1) : False := by
  have hsimple : IsSimpleGroup ↥(lBar V₀ V hV L) :=
    s16t3_isSimpleGroup_of_shape
      (Or.inr (Or.inr (Or.inr (Or.inl ⟨hOmega, by omega⟩))))
  have hrank : 4 ≤ CFSG.Open.pRank 3 (lBar V₀ V hV L) :=
    ThreeRankShape.four_le_pRank ⟨n, Or.inr (Or.inr (Or.inr (Or.inl ⟨hOmega, hn⟩)))⟩
  refine s168e3_false_of_simple_component_four_rank c hcomp hsimple hrank ?_
  intro Q _ _ _ eQ
  obtain ⟨-, K, hKf, hKfin, b, d, hKcard, hirr, ⟨eH⟩⟩ := hOmega
  letI : Field K := hKf
  letI : Finite K := hKfin
  haveI : Fintype K := Fintype.ofFinite K
  have hK2 : Nat.card K = 2 := by simpa using hKcard
  haveI : CharP K 2 :=
    charP_of_card_eq_prime (p := 2) (by rwa [← Nat.card_eq_fintype_card])
  exact s16lc_omegaMinus_center_three_free (m := n / 2) (F := K) (by omega) hirr (eQ.trans eH)

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
