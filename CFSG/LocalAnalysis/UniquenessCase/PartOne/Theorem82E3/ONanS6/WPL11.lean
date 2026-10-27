module

public import CFSG.GroupTheory.PLayer.Transfer
public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82E3.ONanS6.WPH2
public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82E3.ONanS6.WPL6
public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82E3.ONanS6.WPZ
import CFSG.RankThree.GroupTheory.CentralLineComponentAction
public import CFSG.GroupTheory.PGroup.CardCoprime
public import CFSG.LocalAnalysis.RankThreeUC.OddRankOneQuotient.OddRankOneQuotient

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82E3.ONan
section
open CFSG
open CFSG.RankThree.LocalRank
open CFSG.Open
open CFSG.RankThree CFSG.RankThree.PartTwo.Sec4 CFSG.RankThree.PartTwo.Sec13
open CFSG.LocalAnalysis.UniquenessCase.UC22 (Data IsSpor)
open CFSG.LocalAnalysis.UniquenessCase.UCK (ThreeCover)
variable {G : Type} [Group G] [Finite G] {D : Data G}

theorem component_normal_of_seven_of_pRank {X : Type} [Group X] [Finite X]
    {J : Subgroup X} (hrank : CFSG.Open.pRank 7 (⊤ : Subgroup X) ≤ 1)
    (hJ : CFSG.IsComponent J)
    (h7J : 7 ∣ Nat.card (J ⧸ Subgroup.center J))
    (hZ7 : ¬ 7 ∣ Nat.card (Subgroup.center J)) :
    J.Normal := by
  classical
  haveI : Fact (Nat.Prime 7) := ⟨Nat.prime_seven⟩
  have hrank' : CFSG.pRank 7 X ≤ 1 := by
    rwa [CFSG.SectionRank.pRank_eq_open_pRank_top]
  have h7Jcard : 7 ∣ Nat.card J := by
    rw [Subgroup.card_eq_card_quotient_mul_card_subgroup (Subgroup.center J)]
    exact dvd_mul_of_dvd_left h7J _
  refine ⟨fun n hn x => ?_⟩
  let φ : X ≃* X := MulAut.conj x
  let Jx : Subgroup X := J.map φ.toMonoidHom
  have hJx : CFSG.IsComponent Jx := CFSG.LocalCores.isComponent_map_mulEquiv φ hJ
  have hcardJx : Nat.card Jx = Nat.card J := Subgroup.card_map_of_injective φ.injective
  have h7Jx : 7 ∣ Nat.card Jx := hcardJx ▸ h7Jcard
  by_contra hmem
  have hne : Jx ≠ J := by
    intro h
    apply hmem
    have h1 : φ n ∈ Jx := Subgroup.mem_map_of_mem φ.toMonoidHom hn
    rw [h] at h1
    simpa [φ, MulAut.conj_apply] using h1
  have hcomm : ⁅J, Jx⁆ = ⊥ := by
    rcases CFSG.LocalCores.distinct_components_commute hJ hJx with h | h
    · exact absurd h.symm hne
    · exact h
  have hJle : J ≤ Subgroup.centralizer (Jx : Set X) :=
    Subgroup.commutator_eq_bot_iff_le_centralizer.mp hcomm
  obtain ⟨a, haord⟩ := exists_prime_orderOf_dvd_card' (G := ↥J) 7 h7Jcard
  obtain ⟨b, hbord⟩ := exists_prime_orderOf_dvd_card' (G := ↥Jx) 7 h7Jx
  have haordX : orderOf ((a : ↥J) : X) = 7 := by
    rw [Subgroup.orderOf_coe]; exact haord
  have hbordX : orderOf ((b : ↥Jx) : X) = 7 := by
    rw [Subgroup.orderOf_coe]; exact hbord
  have ha1 : ((a : ↥J) : X) ≠ 1 := by
    intro h
    rw [h, orderOf_one] at haordX
    omega
  have ha_not_b : ((a : ↥J) : X) ∉ Subgroup.zpowers ((b : ↥Jx) : X) := by
    intro hab
    have haJx : ((a : ↥J) : X) ∈ Jx := Subgroup.zpowers_le.mpr b.2 hab
    have hainf : ((a : ↥J) : X) ∈ J ⊓ Jx := ⟨a.2, haJx⟩
    have hcenter : a ∈ Subgroup.center J := by
      rw [Subgroup.mem_center_iff]
      intro j
      exact Subtype.ext (Subgroup.mem_centralizer_iff.mp (hJle j.2) ((a : ↥J) : X) haJx).symm
    have hle : Subgroup.zpowers a ≤ Subgroup.center J :=
      Subgroup.zpowers_le.mpr hcenter
    have h7c : 7 ∣ Nat.card (Subgroup.center J) := by
      have h := Subgroup.card_dvd_of_le hle
      rwa [Nat.card_zpowers, haord] at h
    exact hZ7 h7c
  have hcommab : ((a : ↥J) : X) * ((b : ↥Jx) : X) =
      ((b : ↥Jx) : X) * ((a : ↥J) : X) :=
    (Subgroup.mem_centralizer_iff.mp (hJle a.2) ((b : ↥Jx) : X) b.2).symm
  let E : Subgroup X :=
    Subgroup.closure ({((a : ↥J) : X), ((b : ↥Jx) : X)} : Set X)
  have hEabel : CFSG.Open.IsElemAbelian 7 E := by
    refine CFSG.SectionRank.isElemAbelian_closure_pair ?_ ?_ ?_
    · rw [← haordX]; exact pow_orderOf_eq_one _
    · rw [← hbordX]; exact pow_orderOf_eq_one _
    · exact hcommab
  have hclosure : E = Subgroup.zpowers ((a : ↥J) : X) ⊔
      Subgroup.zpowers ((b : ↥Jx) : X) := by
    simp only [E]
    rw [show ({((a : ↥J) : X), ((b : ↥Jx) : X)} : Set X) =
      ({((a : ↥J) : X)} : Set X) ∪ {((b : ↥Jx) : X)} by
        ext y
        simp only [Set.mem_insert_iff, Set.mem_singleton_iff, Set.mem_union]]
    rw [Subgroup.closure_union, Subgroup.zpowers_eq_closure, Subgroup.zpowers_eq_closure]
  have hinf : Subgroup.zpowers ((a : ↥J) : X) ⊓
      Subgroup.zpowers ((b : ↥Jx) : X) = ⊥ :=
    CFSG.zpowers_inf_eq_bot_of_not_mem Nat.prime_seven
      (by rw [← haordX]; exact pow_orderOf_eq_one _) ha1 ha_not_b
  have hcard := CFSG.CGT.PushingUpLit.SYMB.card_sup_mul_card_inf_of_commute
    (C := Subgroup.zpowers ((a : ↥J) : X))
    (D := Subgroup.zpowers ((b : ↥Jx) : X))
    (fun c hc d hd => by
      obtain ⟨m, rfl⟩ := Subgroup.mem_zpowers_iff.mp hc
      obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hd
      exact (show Commute ((a : ↥J) : X) ((b : ↥Jx) : X) from hcommab).zpow_zpow m k)
  rw [hinf, Subgroup.card_bot, mul_one, Nat.card_zpowers, Nat.card_zpowers, haordX,
    hbordX] at hcard
  have hEcard : Nat.card E = 7 ^ 2 := by
    rw [hclosure, hcard]
    norm_num
  have h2 : 2 ≤ CFSG.Open.pRank 7 (⊤ : Subgroup X) :=
    CFSG.SectionRank.le_pRank (p := 7) (H := ⊤) (E := E) (by norm_num) le_top hEabel
      (by rw [hEcard])
  omega

theorem theta_quotient_core_eq_bot_wPL11 (e : G) :
    CFSG.RankThree.LocalRank.aschbacherSolvableCore 3 (componentsQuot e) = ⊥ := by
  let H : Subgroup G := Subgroup.centralizer ({e} : Set G)
  have h := (CFSG.RankThree.theta_quotient_core_and_ranks (G := H)).1
  simpa [componentsQuot, H] using h

theorem seven_not_dvd_center_of_component_wPL11 (e : G)
    {J : Subgroup (componentsQuot e)} (hJ : CFSG.IsComponent J) :
    ¬ 7 ∣ Nat.card (Subgroup.center J) := by
  intro h7
  have hcenter : (Subgroup.center J).map J.subtype ≤ CFSG.pCore 3 (componentsQuot e) :=
    CFSG.RankThree.center_component_le_pCore Nat.prime_three (theta_quotient_core_eq_bot_wPL11 e) hJ
  have hdvd : Nat.card (Subgroup.center J) ∣ Nat.card (CFSG.pCore 3 (componentsQuot e)) := by
    rw [← Subgroup.card_map_of_injective (K := Subgroup.center J) J.subtype_injective]
    exact Subgroup.card_dvd_of_le hcenter
  have hp3 : ¬ 7 ∣ Nat.card (CFSG.pCore 3 (componentsQuot e)) :=
    CFSG.GroupTheory.not_dvd_card_of_isPGroup
      (CFSG.pCore_isPGroup (p := 3) (G := componentsQuot e)) Nat.prime_seven (by norm_num)
  exact hp3 (h7.trans hdvd)

theorem exists_thetaComponent_map_eq_wPL11 (e : G) {J : Subgroup (componentsQuot e)}
    (hJ : CFSG.IsComponent J) :
    ∃ L ∈ thetaComponentsAt 3 e,
      (L.subgroupOf (Subgroup.centralizer ({e} : Set G))).map
        (QuotientGroup.mk' (CFSG.RankThree.LocalRank.aschbacherSolvableCore 3
          ↥(Subgroup.centralizer ({e} : Set G)))) = J := by
  classical
  let H : Subgroup G := Subgroup.centralizer ({e} : Set G)
  let π : H →* componentsQuot e :=
    QuotientGroup.mk' (CFSG.RankThree.LocalRank.aschbacherSolvableCore 3 H)
  let P : Subgroup H := inSubgroup perfectResidual (Subgroup.comap π J)
  obtain ⟨hPtheta, hPmap⟩ :=
    perfectResidual_comap_mem_thetaComponents (p := 3) Nat.prime_three hJ
  refine ⟨P.map H.subtype, ⟨P, hPtheta, rfl⟩, ?_⟩
  have hLsub : (P.map H.subtype).subgroupOf H = P := by
    rw [Subgroup.subgroupOf, Subgroup.comap_map_eq_self_of_injective H.subtype_injective]
  rw [hLsub]
  exact hPmap

theorem componentsImage_eq_bot_of_mem_theta_wPL11
    (c : Ctx82E3 D) (h7 : D.sig = {7}) (e : G) {y : G}
    (hyM : y ∈ D.M) (hy7 : orderOf y = 7)
    (hyθ : y ∈ theta3 (Subgroup.centralizer ({e} : Set G))) :
    componentsImage (D := D) e = ⊥ := by
  classical
  let H : Subgroup G := Subgroup.centralizer ({e} : Set G)
  let θH : Subgroup H := CFSG.RankThree.LocalRank.aschbacherSolvableCore 3 H
  let π : H →* componentsQuot e := QuotientGroup.mk' θH
  let W : Subgroup H := (H ⊓ CFSG.Open.pCoreOf 2 D.M).subgroupOf H
  have hyθ' : y ∈ theta3 H := by simpa [H] using hyθ
  have hyC : y ∈ thetaQuotCentralizer H :=
    CFSG.RankThree.PartTwo.Sec6.theta_le_thetaQuotCentralizer H hyθ'
  have hH : H = (H ⊓ D.M) ⊔ theta3 H := eq_inf_sup_theta_of_seven c h7 hyM hy7 hyC
  have hWmap : componentsImage (D := D) e = W.map π := rfl
  have hWnormal : (W.map π).Normal := by
    refine ⟨fun w hw g => ?_⟩
    obtain ⟨h, rfl⟩ := QuotientGroup.mk'_surjective θH g
    obtain ⟨wH, hwW, rfl⟩ := Subgroup.mem_map.mp hw
    let K : Subgroup H := (H ⊓ D.M).subgroupOf H
    have hKsup : K ⊔ θH = ⊤ := by
      apply Subgroup.map_injective H.subtype_injective
      rw [Subgroup.map_sup,
        Subgroup.map_subgroupOf_eq_of_le (H := H ⊓ D.M) (K := H) inf_le_left,
        Subgroup.map_top, Subgroup.range_subtype]
      exact hH.symm
    have hmem : h ∈ K ⊔ θH := by rw [hKsup]; exact Subgroup.mem_top h
    obtain ⟨mH, hmK, tH, htH, hmul⟩ :=
      (Subgroup.mem_sup_of_normal_right (s := K) (t := θH) (x := h)).1 hmem
    have hmM : (mH : G) ∈ D.M := (Subgroup.mem_subgroupOf.mp hmK).2
    have hπt : π tH = 1 := by
      rw [← MonoidHom.mem_ker, QuotientGroup.ker_mk']
      exact htH
    have hh_eq : h = mH * tH := hmul.symm
    have hπh : π h = π mH := by
      rw [hh_eq, map_mul, hπt, mul_one]
    change π h * π wH * (π h)⁻¹ ∈ W.map π
    rw [hπh, ← map_inv, ← map_mul, ← map_mul]
    refine Subgroup.mem_map_of_mem π ?_
    simp only [W]
    rw [Subgroup.mem_subgroupOf]
    constructor
    · show ((mH : G) * (wH : G) * (mH : G)⁻¹) ∈ H
      exact H.mul_mem (H.mul_mem mH.2 (Subgroup.mem_subgroupOf.mp hwW).1) (H.inv_mem mH.2)
    · have h1 : (wH : G) ∈ CFSG.Open.pCoreOf 2 D.M := (Subgroup.mem_subgroupOf.mp hwW).2
      have hnorm : (mH : G) ∈
          Subgroup.normalizer ((CFSG.Open.pCoreOf 2 D.M : Subgroup G) : Set G) :=
        CFSG.LieType.BorelTits.le_normalizer_pCoreOf (r := 2) D.M hmM
      exact (Subgroup.mem_normalizer_iff.mp hnorm (wH : G)).mp h1
  have hWbot : W.map π = ⊥ := by
    have hθX : CFSG.RankThree.LocalRank.aschbacherSolvableCore 3 (componentsQuot e) = ⊥ :=
      theta_quotient_core_eq_bot_wPL11 e
    have hsol : Group.IsSolvable ↥(W.map π) := by
      haveI : Group.IsNilpotent ↥(W.map π) := (componentsImage_isPGroup (D := D) e).isNilpotent
      infer_instance
    have hmax := (solvable_prime_complement_core_characterization (H := componentsQuot e)
      Nat.prime_three).2.2.2.1
    have hle : W.map π ≤
        CFSG.RankThree.LocalRank.aschbacherSolvableCore 3 (componentsQuot e) :=
      hmax (W.map π) hWnormal hsol (by
        simpa [hWmap] using CFSG.GroupTheory.not_dvd_card_of_isPGroup
          (componentsImage_isPGroup (D := D) e) Nat.prime_three (by norm_num))
    rw [hθX] at hle
    exact le_bot_iff.mp hle
  rw [hWmap]
  exact hWbot

theorem false_of_not_mem_theta_of_suzuki_f_three_wPL11
    (c : Ctx82E3 D) (h7 : D.sig = {7})
    (P : Subgroup G) (hP : CFSG.ABGLocalTools.IsSylowOf 3 P D.M)
    (e : G) (hP3 : CFSG.Open.pRank 7 (Subgroup.centralizer ({e} : Set G)) = 1)
    (he : e ∈ P ⊓ c.L) (heZ : e ∉ zSub P c.L)
    {J : Subgroup (componentsQuot e)} (hJ : CFSG.IsComponent J)
    (hntriv : ¬ TrivialZComponentAction (D := D) c P e J)
    {f : ℕ} (hSz : CFSG.Blueprint.SuzukiModel (J ⧸ Subgroup.center J) 2 f) (hf : f = 3)
    {y : G} (hy7 : orderOf y = 7)
    (hyC : y ∈ Subgroup.centralizer ((P ⊓ c.L : Subgroup G) : Set G))
    (hyθ : y ∉ theta3 (Subgroup.centralizer ({e} : Set G))) :
    False := by
  classical
  haveI : Fact (Nat.Prime 7) := ⟨Nat.prime_seven⟩
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  let H : Subgroup G := Subgroup.centralizer ({e} : Set G)
  let θH : Subgroup H := CFSG.RankThree.LocalRank.aschbacherSolvableCore 3 H
  let π : H →* componentsQuot e := QuotientGroup.mk' θH
  have hyθ' : y ∉ theta3 H := by simpa [H] using hyθ
  have hyH : y ∈ H := by
    change y ∈ Subgroup.centralizer ({e} : Set G)
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact (Subgroup.mem_centralizer_iff.mp hyC e he).symm
  let yH : H := ⟨y, hyH⟩
  have hyHord : orderOf yH = 7 := by
    rw [← Subgroup.orderOf_coe yH]; exact hy7
  let ystar : componentsQuot e := π yH
  have hystar7 : orderOf ystar = 7 := by
    refine orderOf_eq_prime ?_ ?_
    · rw [← map_pow, ← hyHord, pow_orderOf_eq_one, map_one]
    · intro h1
      apply hyθ'
      have hmem : yH ∈ (QuotientGroup.mk' θH).ker := by
        rw [MonoidHom.mem_ker]; exact h1
      rw [QuotientGroup.ker_mk'] at hmem
      exact Subgroup.mem_map_of_mem H.subtype hmem
  have hP3' : CFSG.Open.pRank 7 H = 1 := by simpa [H] using hP3
  have hrankH : CFSG.pRank 7 ↥H ≤ 1 := by
    rw [CFSG.SectionRank.pRank_coe_eq_openPRank]
    omega
  have hrankX : CFSG.pRank 7 (componentsQuot e) ≤ 1 :=
    CFSG.LocalAnalysis.RankThreeUC.OddRankOneQuotient.pRank_le_one_of_surjective
      Nat.prime_seven (by norm_num) hrankH π (QuotientGroup.mk'_surjective θH)
  have hrankXtop : CFSG.Open.pRank 7 (⊤ : Subgroup (componentsQuot e)) ≤ 1 := by
    rw [← CFSG.SectionRank.pRank_eq_open_pRank_top]
    exact hrankX
  have hcycS : ∀ S : Sylow 7 (componentsQuot e),
      IsCyclic ↥(S : Subgroup (componentsQuot e)) := fun S =>
    CFSG.LocalAnalysis.RankThreeUC.OddRankOneQuotient.isCyclic_sylow_of_pRank_le_one
      Nat.prime_seven (by norm_num) hrankX S
  have h7Jquot : 7 ∣ Nat.card (J ⧸ Subgroup.center J) := by
    obtain ⟨-, a, ha, K, hKf, hKfin, hf', hKcard, ⟨eSZ⟩⟩ := hSz
    letI : Field K := hKf
    letI : Finite K := hKfin
    have ha1 : a = 1 := by omega
    subst ha1
    have hKcard' : Nat.card K = 2 ^ (2 * 1 + 1) := by
      rw [hf] at hKcard
      simpa using hKcard
    have horder := CFSG.LieType.Ree.suzuki_order (a := 1) (K := K) hKcard'
    have h7sz : 7 ∣ Nat.card (CFSG.Blueprint.suzukiGroup 1 K) := by
      rw [horder]
      norm_num
    rw [Nat.card_congr eSZ.toEquiv]
    exact h7sz
  have h7J : 7 ∣ Nat.card J := by
    rw [Subgroup.card_eq_card_quotient_mul_card_subgroup (Subgroup.center J)]
    exact dvd_mul_of_dvd_left h7Jquot _
  have hZ7 : ¬ 7 ∣ Nat.card (Subgroup.center J) := seven_not_dvd_center_of_component_wPL11 e hJ
  have hJnormal : J.Normal := component_normal_of_seven_of_pRank hrankXtop hJ h7Jquot hZ7
  have hystarP : IsPGroup 7 (Subgroup.zpowers ystar) := by
    refine IsPGroup.of_card (p := 7) (n := 1) ?_
    rw [Nat.card_zpowers, hystar7]
    norm_num
  obtain ⟨S, hyS⟩ := hystarP.exists_le_sylow
  have hSyl : CFSG.ABGLocalTools.IsSylowOf 7 (S : Subgroup (componentsQuot e)) ⊤ := by
    rw [CFSG.ABGLocalTools.isSylowOf_iff]
    exact ⟨le_top, S.isPGroup',
      by rw [Subgroup.relIndex_top_right]; exact S.not_dvd_index⟩
  have hJS : CFSG.ABGLocalTools.IsSylowOf 7
      ((S : Subgroup (componentsQuot e)) ⊓ J) J := by
    simpa [inf_comm] using CFSG.ABGLocalTools.IsSylowOf.inf_of_isSubnormal (p := 7) hSyl
      (CFSG.ComponentClassification.Components.chain_of_mathlib_subnormal hJ.2)
  have hJpos : 0 < Nat.card J := Nat.card_pos
  have hfact : 0 < (Nat.card J).factorization 7 :=
    Nat.prime_seven.factorization_pos_of_dvd hJpos.ne' h7J
  have h7JS : 7 ∣ Nat.card ↥((S : Subgroup (componentsQuot e)) ⊓ J) := by
    rw [hJS.card_eq]
    exact dvd_pow_self 7 hfact.ne'
  obtain ⟨u, huord⟩ := exists_prime_orderOf_dvd_card'
    (G := ↥((S : Subgroup (componentsQuot e)) ⊓ J)) 7 h7JS
  let uX : componentsQuot e := (u : ↥((S : Subgroup (componentsQuot e)) ⊓ J))
  have huXord : orderOf uX = 7 := by
    rw [Subgroup.orderOf_coe]; exact huord
  have huS : uX ∈ (S : Subgroup (componentsQuot e)) := u.2.1
  let uS : ↥(S : Subgroup (componentsQuot e)) := ⟨uX, huS⟩
  have huSord : orderOf uS = 7 := by
    rw [← Subgroup.orderOf_coe uS]; exact huXord
  let yS : ↥(S : Subgroup (componentsQuot e)) :=
    ⟨ystar, hyS (Subgroup.mem_zpowers ystar)⟩
  have hySord : orderOf yS = 7 := by
    rw [← Subgroup.orderOf_coe yS]; exact hystar7
  haveI : IsCyclic ↥(S : Subgroup (componentsQuot e)) := hcycS S
  have hEq : Subgroup.zpowers uS = Subgroup.zpowers yS :=
    (IsCyclic.subgroup_eq_iff_card_eq (H := Subgroup.zpowers uS)
      (K := Subgroup.zpowers yS)).mpr (by
        rw [Nat.card_zpowers, Nat.card_zpowers, huSord, hySord])
  have hyJ : ystar ∈ J := by
    have hmem : yS ∈ Subgroup.zpowers uS := hEq.symm ▸ Subgroup.mem_zpowers yS
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hmem
    have hkX : uX ^ k = ystar := by
      have h := congrArg (fun z : ↥(S : Subgroup (componentsQuot e)) =>
        (z : componentsQuot e)) hk
      simpa [uS, yS, uX] using h
    have hmemX : ystar ∈ Subgroup.zpowers uX := Subgroup.mem_zpowers_iff.mpr ⟨k, hkX⟩
    exact Subgroup.zpowers_le.mpr u.2.2 hmemX
  obtain ⟨L, hLmem, hLmap⟩ := exists_thetaComponent_map_eq_wPL11 e hJ
  have hntrivL : Nat.card (autThetaQuot (zSub P c.L) L) ≠ 1 := by
    intro h1
    exact hntriv ⟨L, hLmem, hLmap, h1⟩
  obtain ⟨L0, hL0mem, hL0eq⟩ := hLmem
  have hLH : L ≤ H := hL0eq ▸ Subgroup.map_subtype_le L0
  let Lh : Subgroup H := L.subgroupOf H
  have hLh_eq : Lh = L0 := by
    apply Subgroup.map_injective H.subtype_injective
    rw [Subgroup.map_subgroupOf_eq_of_le hLH]
    exact hL0eq.symm
  have hLh_sub : Lh.IsSubnormal := hLh_eq ▸ hL0mem.2.1
  have hLhmap : Lh.map π = J := by
    simpa [Lh, π, θH, H] using hLmap
  have hL0map : L0.map π = J := hLh_eq ▸ hLhmap
  have hLhmapG : Lh.map H.subtype = L := by
    rw [hLh_eq]
    exact hL0eq
  have hzSubH : zSub P c.L ≤ H := by
    intro z hz
    change z ∈ Subgroup.centralizer ({e} : Set G)
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact (Subgroup.mem_centralizer_iff.mp hz.2 e he).symm
  let Zh : Subgroup H := (zSub P c.L).subgroupOf H
  have hZhmap : Zh.map H.subtype = zSub P c.L :=
    Subgroup.map_subgroupOf_eq_of_le hzSubH
  have hntrivL' : Nat.card ↥(autThetaQuot (zSub P c.L) (Lh.map H.subtype)) ≠ 1 := by
    rw [hLhmapG]
    exact hntrivL
  have hEqAut := map_autThetaQuot_sub (C := H) (X' := Zh) (L' := Lh)
  have hcardAut : Nat.card ↥(autThetaQuot Zh Lh) =
      Nat.card ↥(autThetaQuot (zSub P c.L) (Lh.map H.subtype)) := by
    have hmap := Subgroup.card_map_of_injective (K := autThetaQuot Zh Lh)
      (f := (MulAut.congr (thetaQuotEquivSub H Lh)).toMonoidHom)
      (MulAut.congr (thetaQuotEquivSub H Lh)).injective
    rw [← hmap]
    rw [show (autThetaQuot Zh Lh).map
        (MulAut.congr (thetaQuotEquivSub H Lh)).toMonoidHom =
        autThetaQuot (zSub P c.L) (Lh.map H.subtype) by simpa [hZhmap] using hEqAut]
  have hntrivZh : Nat.card ↥(autThetaQuot Zh Lh) ≠ 1 :=
    fun h => hntrivL' (hcardAut ▸ h)
  have hnebotZh : autThetaQuot Zh Lh ≠ ⊥ := by
    intro h
    exact hntrivZh (by rw [h, Subgroup.card_bot])
  haveI : Nontrivial ↥(autThetaQuot Zh Lh) :=
    (Subgroup.nontrivial_iff_ne_bot _).mpr hnebotZh
  obtain ⟨τh, hτhne⟩ := exists_ne (1 : ↥(autThetaQuot Zh Lh))
  obtain ⟨z0, hz0Nh, hz0Zh, hτheq⟩ := mem_autThetaQuot_iff.mp τh.2
  let z0star : componentsQuot e := π z0
  have hz0starN : z0star ∈ Subgroup.normalizer (J : Set (componentsQuot e)) := by
    rw [Subgroup.normalizer_eq_top_iff.mpr hJnormal]
    exact Subgroup.mem_top _
  obtain ⟨η, hη⟩ := CFSG.RankThree.exists_thetaQuotient_mulEquiv_map
    (H := ↥H) (p := 3) Nat.prime_three (L := Lh) hLh_sub
  have hητ : ∀ x : Lh ⧸ aschbacherSolvableCore 3 Lh,
      ((η ((τh : MulAut (Lh ⧸ aschbacherSolvableCore 3 Lh)) x) : Lh.map π) :
          componentsQuot e) =
        z0star * ((η x : Lh.map π) : componentsQuot e) * z0star⁻¹ := by
    intro x
    induction x using QuotientGroup.induction_on with
    | H l =>
      have hτh_apply : (τh : MulAut (Lh ⧸ aschbacherSolvableCore 3 Lh))
          (QuotientGroup.mk' (aschbacherSolvableCore 3 Lh) l) =
          QuotientGroup.mk' (aschbacherSolvableCore 3 Lh)
            (Lh.normalizerMonoidHom ⟨z0, hz0Nh⟩ l) := by
        rw [← hτheq]
        exact thetaQuotMulAut_mk (Lh.normalizerMonoidHom ⟨z0, hz0Nh⟩) l
      change ((η ((τh : MulAut (Lh ⧸ aschbacherSolvableCore 3 Lh))
        (QuotientGroup.mk' (aschbacherSolvableCore 3 Lh) l)) : Lh.map π) :
          componentsQuot e) =
        z0star * ((η (QuotientGroup.mk' (aschbacherSolvableCore 3 Lh) l) :
          Lh.map π) : componentsQuot e) * z0star⁻¹
      rw [hτh_apply]
      change ((η (↑(Lh.normalizerMonoidHom ⟨z0, hz0Nh⟩ l)) : Lh.map π) :
          componentsQuot e) =
        z0star * ((η (↑l) : Lh.map π) : componentsQuot e) * z0star⁻¹
      rw [hη (Lh.normalizerMonoidHom ⟨z0, hz0Nh⟩ l), hη l]
      rw [Subgroup.normalizerMonoidHom_apply_apply_coe]
      simp only [map_mul, map_inv]
      rfl
  have hz0_not_central : ¬ (∀ j ∈ J,
      z0star * j * z0star⁻¹ = j) := by
    intro hcent
    apply hτhne
    apply Subtype.ext
    ext x
    apply η.injective
    apply Subtype.ext
    change ((η ((τh : MulAut (Lh ⧸ aschbacherSolvableCore 3 Lh)) x) : Lh.map π) :
      componentsQuot e) = ((η x : Lh.map π) : componentsQuot e)
    rw [hητ x]
    exact hcent ((η x : Lh.map π) : componentsQuot e) (hLhmap ▸ (η x).2)
  let yJ : J := ⟨ystar, hyJ⟩
  let αJ : MulAut J := J.normalizerMonoidHom ⟨z0star, hz0starN⟩
  let σJ : MulAut (J ⧸ Subgroup.center J) :=
    CFSG.ComponentClassification.PerfectAutomorphisms.centerQuotientHom J αJ
  haveI : Group.IsPerfect ↥J := hJ.1.1
  have hσJne : σJ ≠ 1 := by
    intro hσ
    apply hz0_not_central
    intro j hj
    have hσ' : CFSG.ComponentClassification.PerfectAutomorphisms.onCenterQuotient αJ = 1 := by
      simpa [σJ, CFSG.ComponentClassification.PerfectAutomorphisms.centerQuotientHom] using hσ
    have hα1 : αJ = 1 :=
      CFSG.ComponentClassification.PerfectAutomorphisms.onCenterQuotient_eq_one_imp αJ hσ'
    have h := congrArg (fun φ : MulAut J => ((φ ⟨j, hj⟩ : J) : componentsQuot e)) hα1
    rw [Subgroup.normalizerMonoidHom_apply_apply_coe] at h
    simpa using h
  have hz0_3 : ∃ n, orderOf z0 = 3 ^ n := by
    have hz0P : ((z0 : H) : G) ∈ P := by
      have h1 : ((z0 : H) : G) ∈ zSub P c.L := Subgroup.mem_subgroupOf.mp hz0Zh
      exact h1.1.1
    let z0P : P := ⟨((z0 : H) : G), hz0P⟩
    obtain ⟨n, hn⟩ := (IsPGroup.iff_orderOf.mp hP.isPGroup) z0P
    refine ⟨n, ?_⟩
    have hco := (Subgroup.orderOf_coe z0P).trans hn
    simpa [z0P] using hco
  have hσJord_pow : ∃ k, orderOf σJ = 3 ^ k := by
    obtain ⟨n, hn⟩ := hz0_3
    have h1 : orderOf z0star ∣ orderOf z0 := orderOf_map_dvd π z0
    have h2 : orderOf αJ ∣ orderOf z0star := by
      have h := orderOf_map_dvd (J.normalizerMonoidHom) ⟨z0star, hz0starN⟩
      have hc : orderOf (⟨z0star, hz0starN⟩ : Subgroup.normalizer (J : Set _)) =
          orderOf z0star :=
        (Subgroup.orderOf_coe (⟨z0star, hz0starN⟩ : Subgroup.normalizer (J : Set _))).symm
      rwa [hc] at h
    have h3 : orderOf σJ ∣ orderOf αJ :=
      orderOf_map_dvd (CFSG.ComponentClassification.PerfectAutomorphisms.centerQuotientHom J) αJ
    have hdvd : orderOf σJ ∣ 3 ^ n := hn ▸ (h3.trans (h2.trans h1))
    obtain ⟨k, -, hk⟩ := (Nat.dvd_prime_pow Nat.prime_three).mp hdvd
    exact ⟨k, hk⟩
  obtain ⟨k, hk⟩ := hσJord_pow
  have hk0 : k ≠ 0 := by
    intro h0
    apply hσJne
    apply orderOf_eq_one_iff.mp
    rw [hk, h0, pow_zero]
  have h3dvd : 3 ∣ orderOf σJ := by
    rw [hk]
    exact dvd_pow_self 3 hk0
  let σ' : MulAut (J ⧸ Subgroup.center J) := σJ ^ (orderOf σJ / 3)
  have hσ'ord : orderOf σ' = 3 :=
    orderOf_pow_orderOf_div (orderOf_pos σJ).ne' h3dvd
  let yJZ : J ⧸ Subgroup.center J := QuotientGroup.mk' (Subgroup.center J) yJ
  have hyJord : orderOf yJ = 7 := by
    rw [← Subgroup.orderOf_coe yJ]; exact hystar7
  have hyJZ7 : orderOf yJZ = 7 := by
    refine orderOf_eq_prime ?_ ?_
    · rw [← map_pow, ← hyJord, pow_orderOf_eq_one, map_one]
    · intro h1
      have hmem : yJ ∈ Subgroup.center J :=
        (QuotientGroup.eq_one_iff (N := Subgroup.center J) yJ).mp h1
      have hle : Subgroup.zpowers yJ ≤ Subgroup.center J := Subgroup.zpowers_le.mpr hmem
      have h7c : 7 ∣ Nat.card (Subgroup.center J) := by
        have h := Subgroup.card_dvd_of_le hle
        rwa [Nat.card_zpowers, hyJord] at h
      exact hZ7 h7c
  have hcommX : ystar * z0star = z0star * ystar := by
    have hz0PL : ((z0 : H) : G) ∈ P ⊓ c.L :=
      (Subgroup.mem_subgroupOf.mp hz0Zh).1
    have hcommG : y * ((z0 : H) : G) = ((z0 : H) : G) * y :=
      (Subgroup.mem_centralizer_iff.mp hyC ((z0 : H) : G) hz0PL).symm
    have hcommH : yH * z0 = z0 * yH := Subtype.ext hcommG
    have := congrArg π hcommH
    simpa [ystar, z0star, map_mul] using this
  have hαJ_y : αJ yJ = yJ := by
    apply Subtype.ext
    rw [Subgroup.normalizerMonoidHom_apply_apply_coe]
    change z0star * ystar * z0star⁻¹ = ystar
    rw [← hcommX]
    group
  have hσJfix : σJ yJZ = yJZ := by
    change CFSG.ComponentClassification.PerfectAutomorphisms.centerQuotientHom J αJ
      (QuotientGroup.mk' (Subgroup.center J) yJ) =
      QuotientGroup.mk' (Subgroup.center J) yJ
    rw [show CFSG.ComponentClassification.PerfectAutomorphisms.centerQuotientHom J αJ =
        CFSG.ComponentClassification.PerfectAutomorphisms.onCenterQuotient αJ from rfl,
      CFSG.ComponentClassification.PerfectAutomorphisms.onCenterQuotient_apply_mk, hαJ_y]
  have hσ'fix : σ' yJZ = yJZ := by
    have hpow : ∀ n : ℕ, (σJ ^ n) yJZ = yJZ := by
      intro n
      induction n with
      | zero => rfl
      | succ n ih => rw [pow_succ, MulAut.mul_apply, hσJfix, ih]
    change (σJ ^ (orderOf σJ / 3)) yJZ = yJZ
    exact hpow _
  obtain ⟨b, hfb, -, hcardfix⟩ :=
    CFSG.LocalAnalysis.UniquenessCase.UCK.SzFix.card_fixed_of_orderOf_three
      (S := J ⧸ Subgroup.center J) (f := f) hSz (σ := σ') hσ'ord
  have hb0 : b = 0 := by omega
  subst hb0
  have hfix20 : Nat.card
      (CFSG.ComponentClassification.FixedCommutingProduct.fixedSubgroup σ') = 20 := by
    rw [hcardfix]
    norm_num
  have hyfix : yJZ ∈ CFSG.ComponentClassification.FixedCommutingProduct.fixedSubgroup σ' := by
    change σ' yJZ = yJZ
    exact hσ'fix
  have h7fix : 7 ∣ Nat.card
      (CFSG.ComponentClassification.FixedCommutingProduct.fixedSubgroup σ') := by
    have hle : Subgroup.zpowers yJZ ≤
        CFSG.ComponentClassification.FixedCommutingProduct.fixedSubgroup σ' :=
      Subgroup.zpowers_le.mpr hyfix
    have h := Subgroup.card_dvd_of_le hle
    rwa [Nat.card_zpowers, hyJZ7] at h
  rw [hfix20] at h7fix
  norm_num at h7fix

theorem suzukiComponents_centralize_of_f_eq_three'
    (c : Ctx82E3 D)
    (hON : ThreeCover (fun Y _ => IsSpor Y .ONan) c.Lbar) (h7 : D.sig = {7})
    (P : Subgroup G) (hP : CFSG.ABGLocalTools.IsSylowOf 3 P D.M)
    (hNZ : Subgroup.normalizer ((zSub P c.L : Subgroup G) : Set G) ≤ D.M)
    (e : G) (hP3 : CFSG.Open.pRank 7 (Subgroup.centralizer ({e} : Set G)) = 1)
    (hZ3 : ∀ J ∈ thetaComponentsAt 3 e, 3 ∣ Nat.card J →
      Nat.card (autThetaQuot (zSub P c.L) J) = 1)
    (he : e ∈ P ⊓ c.L) (he3 : orderOf e = 3) (heZ : e ∉ zSub P c.L)
    {J : Subgroup (componentsQuot e)} (hJ : CFSG.IsComponent J)
    (hntriv : ¬ TrivialZComponentAction (D := D) c P e J)
    {f : ℕ} (hSz : CFSG.Blueprint.SuzukiModel (J ⧸ Subgroup.center J) 2 f) (hf : f = 3) :
    componentsImage (D := D) e ≤ Subgroup.centralizer (J : Set _) := by
  classical
  have he1 : e ≠ 1 := by
    rintro rfl
    rw [orderOf_one] at he3
    norm_num at he3
  obtain ⟨y, hyM, hy7, hycent⟩ :=
    exists_seven_mem_centralizer_inf_L_of_onan c hON (by rw [h7]; simp) hP
  have hyC : y ∈ Subgroup.centralizer ((P ⊓ c.L : Subgroup G) : Set G) :=
    Subgroup.mem_centralizer_iff.mpr (fun q hq => (hycent q hq).symm)
  have hyH : y ∈ Subgroup.centralizer ({e} : Set G) := by
    change y ∈ Subgroup.centralizer ({e} : Set G)
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact (Subgroup.mem_centralizer_iff.mp hyC e he).symm
  by_cases hyθ : y ∈ theta3 (Subgroup.centralizer ({e} : Set G))
  · have hbot := componentsImage_eq_bot_of_mem_theta_wPL11 c h7 e hyM hy7 hyθ
    rw [hbot]
    exact bot_le
  · exact (false_of_not_mem_theta_of_suzuki_f_three_wPL11 c h7 P hP e hP3 he heZ hJ hntriv hSz hf
      hy7 hyC hyθ).elim

end
end CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82E3.ONan
