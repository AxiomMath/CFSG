module

public import CFSG.LocalAnalysis.UniquenessCase.UC22S215KF7Use
public import CFSG.LocalAnalysis.UniquenessCase.UCFront08
public import CFSG.LocalAnalysis.UniquenessCase.UC6Inst
import CFSG.LocalAnalysis.UniquenessCase.UCFront07Use
import CFSG.LocalAnalysis.UniquenessCase.UC6S846h
import CFSG.LocalAnalysis.UniquenessCase.UC6R869NS
import CFSG.LocalAnalysis.UniquenessCase.UC22OddPRank
import CFSG.LocalAnalysis.AGLEmbedding.CaseTwoEscapeK
import CFSG.LocalAnalysis.GLTheoremB.NormalPlane
import CFSG.GroupTheory.SurjectiveRangeFactor
import CFSG.GroupTheory.PerfectSylowCenter
import CFSG.Quasithin.EmptyFaithful.GoldschmidtKFIdSyl
public import CFSG.LocalAnalysis.ComponentClassification.SimpleEvenOrder
public import CFSG.LocalAnalysis.PreuniquenessRankFour.SamePrimeAction
public import CFSG.Quasithin.Background.B6Sections

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

open CFSG.Open Subgroup
open CFSG.Yardstones.Mf4cdcdf2e013 (Standing4 Setup4)
open CFSG.RankThree.PartOne (IsStronglyPEmbedded)
open CFSG.LocalAnalysis.UniquenessCase.PartOne.Section7 (Sec7Core4)

variable {G : Type} [Group G] [Finite G]

theorem uc22s213_exists_surj_center_quotient {M L A : Subgroup G} (hL : L ∈ calC M)
    (hY : (L ⊓ centralizer (A : Set G)) ⊔ pCoreOf 2 L = L) :
    ∃ f : ↥(CFSG.Quasithin.perfectCore (L ⊓ centralizer (A : Set G))) →*
      (Bar2 L ⧸ center (Bar2 L)), Function.Surjective f := by
  have hYL : L ⊓ centralizer (A : Set G) ≤ L := inf_le_left
  have hDL : CFSG.Quasithin.perfectCore (L ⊓ centralizer (A : Set G)) ≤ L :=
    (CFSG.Quasithin.perfectCore_le _).trans hYL
  have hin : (CFSG.Quasithin.perfectCore (L ⊓ centralizer (A : Set G))).subgroupOf L =
      CFSG.Quasithin.perfectCore ((L ⊓ centralizer (A : Set G)).subgroupOf L) := by
    have h := CFSG.Quasithin.map_perfectCore L.subtype ((L ⊓ centralizer (A : Set G)).subgroupOf L)
    rw [Subgroup.map_subgroupOf_eq_of_le hYL] at h
    rw [← h]
    exact Subgroup.comap_map_eq_self_of_injective L.subtype_injective _
  have honto : (CFSG.Quasithin.perfectCore ((L ⊓ centralizer (A : Set G)).subgroupOf L)).map
      (QuotientGroup.mk' (CFSG.pCore 2 ↥L)) = ⊤ := by
    rw [CFSG.Quasithin.map_perfectCore, UC6.R869S.map_subgroupOf_eq_top hYL hY,
      CFSG.Quasithin.perfectCore_eq_self_of_perfect (UC6.R869S.bar2_perfect hL.2.1)]
  let g := (QuotientGroup.mk' (CFSG.pCore 2 ↥L)).comp (Subgroup.inclusion hDL)
  have hg : Function.Surjective g := by
    rw [← MonoidHom.range_eq_top, MonoidHom.range_comp, Subgroup.inclusion_range, hin, honto]
  exact ⟨(QuotientGroup.mk' (center (Bar2 L))).comp g,
    (QuotientGroup.mk'_surjective _).comp hg⟩

theorem uc22s213_thin8_of_isAlt_five {L : Subgroup G} (hL : ⁅L, L⁆ = L)
    (h : IsAlt (Bar2 L ⧸ center (Bar2 L)) 5) : F08.Thin8 L := by
  intro q hq hq2
  by_contra hlt
  haveI : Fact q.Prime := ⟨hq⟩
  have h2 : 2 ≤ CFSG.Open.pRank q (⊤ : Subgroup (Bar2 L)) := by
    rw [pRank_bar2_eq_of_odd hq hq2]
    omega
  haveI : Group.IsPerfect (Bar2 L) := Group.isPerfect_def.mpr (UC6.R869S.bar2_perfect hL)
  obtain ⟨P⟩ : Nonempty (Sylow q (Bar2 L)) := inferInstance
  have hPnc : ¬ IsCyclic ↥(P : Subgroup (Bar2 L)) :=
    CFSG.LocalAnalysis.GLTheoremB.not_isCyclic_of_two_le_pRank
      ((CFSG.PreuniquenessRankFour.Helpers.pRank_sylow_eq_globalRank q hq P).symm ▸ h2)
  obtain ⟨Q⟩ : Nonempty (Sylow q (Bar2 L ⧸ center (Bar2 L))) := inferInstance
  have hdvd : q ^ 2 ∣ Nat.card (Bar2 L ⧸ center (Bar2 L)) :=
    CFSG.Quasithin.SBd19F.sq_dvd_card_of_noncyclic
      (CFSG.GroupTheory.not_isCyclic_sylow_quotient_of_center P hPnc (center (Bar2 L)) le_rfl Q)
  obtain ⟨e⟩ := h
  rw [Nat.card_congr e.toEquiv, nat_card_alternatingGroup] at hdvd
  norm_num at hdvd
  have hq7 : q ≤ 7 := by
    have := Nat.le_of_dvd (by norm_num) hdvd
    nlinarith
  interval_cases q <;>
    first
    | exact absurd rfl hq2
    | (norm_num at hdvd; done)
    | (norm_num at hq; done)

theorem uc22s213_normalizer_le_of_sig (hS : Standing4 G) (hU : uniqueFourUnique G)
    (S : Setup4 G) (hKF : KF7Use (UC6.dataOfSetup4 hS hU S)) {L : Subgroup G}
    (hL : L ∈ calC S.M) (hthin : ¬ F08.Thin8 L) {p : ℕ} (hp : p ∈ uniqueFourSigma S.M)
    {A : Subgroup G} (hAM : A ≤ S.M) {r : ℕ} (hr : r.Prime) (hAr : Nat.card A = r)
    (hY : (L ⊓ centralizer (A : Set G)) ⊔ pCoreOf 2 L = L)
    (h2 : 2 ≤ CFSG.Open.pRank p (normalizer (A : Set G) ⊓ S.M)) :
    normalizer (A : Set G) ≤ S.M := by
  classical
  by_contra hHM
  haveI : IsSimpleGroup G := hS.simple
  have htop : normalizer (A : Set G) ≠ ⊤ := by
    intro htop
    haveI : A.Normal := Subgroup.normalizer_eq_top_iff.1 htop
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal A with hbot | hAtop
    · subst hbot
      rw [Subgroup.card_bot] at hAr
      exact hr.ne_one hAr.symm
    · exact hHM fun x _ => hAM (hAtop ▸ Subgroup.mem_top x)
  have hpr := (UC6.dataOfSetup4 hS hU S).sig_prime p hp
  have hsp : IsStronglyPEmbedded p S.M :=
    UC6S846.sp_of_mem_sig (UC6S846.sigmaStd_dataOfSetup4 hS hU S)
      (UC6S846.not_solvable_of_mem_calC hL) hp
  have hsec : F07.Sec7Hyp (UC6.dataOfSetup4 hS hU S) p (normalizer (A : Set G)) :=
    ⟨hpr.1, hpr.2, hsp, htop, hHM, h2⟩
  have hodd : Odd (Nat.card (CFSG.pPrimeCore p ↥(normalizer (A : Set G)))) :=
    (Sec7Core4.ofSetup4Any hS hU S hp hsp).odd_card_pPrimeCore_of_not_le hHM h2
  obtain ⟨f, hf⟩ := uc22s213_exists_surj_center_quotient hL hY
  haveI hsimple : IsSimpleGroup (Bar2 L ⧸ center (Bar2 L)) := hL.2.2.2
  haveI : Group.IsPerfect (Bar2 L) := Group.isPerfect_def.mpr hL.2.2.1
  have hnab : ∃ x y : Bar2 L ⧸ center (Bar2 L), x * y ≠ y * x := by
    by_contra hcomm
    push Not at hcomm
    exact Group.IsPerfect.not_isSolvable _ (isSolvable_of_comm hcomm)
  obtain ⟨-, x, hx⟩ :=
    CFSG.ComponentClassification.SimpleEvenOrder.nonabelian_simple_even hnab
  have hx1 : x ≠ 1 := by
    rintro rfl
    rw [orderOf_one] at hx
    omega
  have hx2 : x ^ 2 ^ 1 = 1 := by
    have h := pow_orderOf_eq_one x
    rw [hx] at h
    simpa using h
  have hD0Y := CFSG.Quasithin.perfectCore_le (L ⊓ centralizer (A : Set G))
  have hD0H : CFSG.Quasithin.perfectCore (L ⊓ centralizer (A : Set G)) ≤
      normalizer (A : Set G) :=
    hD0Y.trans (inf_le_right.trans (Subgroup.centralizer_le_normalizer _))
  have hD0M : CFSG.Quasithin.perfectCore (L ⊓ centralizer (A : Set G)) ≤ S.M :=
    hD0Y.trans (inf_le_left.trans hL.1.le)
  let g := (QuotientGroup.mk' (CFSG.pPrimeCore p ↥(normalizer (A : Set G)))).comp
    (Subgroup.inclusion hD0H)
  have hker : g.ker ≤ f.ker := by
    refine CFSG.AGLEmbedding.le_ker_of_isSimpleGroup f hf g.ker (p := 2) (fun n hn => ?_) hx1 hx2
    have hnK : Subgroup.inclusion hD0H n ∈ CFSG.pPrimeCore p ↥(normalizer (A : Set G)) :=
      (QuotientGroup.eq_one_iff _).mp hn
    have hord : orderOf n = orderOf (⟨_, hnK⟩ : ↥(CFSG.pPrimeCore p ↥(normalizer (A : Set G)))) :=
      (orderOf_injective _ (Subgroup.inclusion_injective hD0H) n).symm.trans
        (Subgroup.orderOf_mk _ hnK).symm
    rw [hord, Nat.coprime_two_left]
    exact hodd.of_dvd_nat (orderOf_dvd_natCard _)
  obtain ⟨ψ, hψ⟩ := CFSG.exists_surjective_range_of_ker_le g f hf hker
  have hle : g.range ≤ ((normalizer (A : Set G) ⊓ S.M).subgroupOf (normalizer (A : Set G))).map
      (QuotientGroup.mk' (CFSG.pPrimeCore p ↥(normalizer (A : Set G)))) := by
    rintro _ ⟨d, rfl⟩
    exact Subgroup.mem_map_of_mem _ (Subgroup.mem_subgroupOf.mpr ⟨hD0H d.2, hD0M d.2⟩)
  have hperf : ⁅g.range, g.range⁆ = g.range := by
    haveI : Group.IsPerfect ↥(CFSG.Quasithin.perfectCore (L ⊓ centralizer (A : Set G))) :=
      Subgroup.isPerfect_iff.mpr (CFSG.Quasithin.perfectCore_perfect _)
    exact Subgroup.isPerfect_iff.mp (Group.IsPerfect.ofSurjective g.rangeRestrict_surjective)
  rcases hKF p hp (normalizer (A : Set G)) hsec with hsol | ⟨-, hA5⟩
  ·
    haveI : Group.IsSolvable ↥(((normalizer (A : Set G) ⊓ S.M).subgroupOf
        (normalizer (A : Set G))).map
          (QuotientGroup.mk' (CFSG.pPrimeCore p ↥(normalizer (A : Set G))))) := hsol
    haveI : Group.IsSolvable ↥g.range :=
      Group.isSolvable_of_isSolvable_injective (Subgroup.inclusion_injective hle)
    have hbot : g.range = ⊥ := by
      rw [← CFSG.Quasithin.perfectCore_eq_self_of_perfect hperf]
      exact (CFSG.Quasithin.isSolvable_iff_perfectCore_eq_bot _).mp inferInstance
    obtain ⟨y, rfl⟩ := hψ x
    have hy : y = 1 := Subtype.ext (by simpa [hbot] using y.2)
    exact hx1 (by rw [hy, map_one])
  ·
    exact hthin (uc22s213_thin8_of_isAlt_five hL.2.1 (hA5 g.range hle hperf _ hsimple ψ hψ))

end CFSG.LocalAnalysis.UniquenessCase.UC22
