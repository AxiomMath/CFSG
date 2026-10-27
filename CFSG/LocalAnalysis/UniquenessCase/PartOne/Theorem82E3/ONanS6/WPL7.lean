module

public import CFSG.GroupTheory.CyclicOfSupCyclicRight
public import CFSG.GroupTheory.ExtraspecialThreeFive
public import CFSG.GroupTheory.IsCyclicOfLeOfPRankLeOne
public import CFSG.GroupTheory.IsSylowOfMapOfKerPrimeNotDvd
public import CFSG.LocalAnalysis.RankThreeUC.AGL81S15R1517B
public import CFSG.LocalAnalysis.UniquenessCase.UC6S19
public import CFSG.RankThree.GroupTheory.ThetaQuotientTransport
public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82E3.ONanKFacts
public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82E3.ONanS6.WPFF2
public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82E3.ONanS6.WPH2
public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82E3.ONanS6.WPL
public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82E3.ONanS6.WPL3
public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82E3.ONanS6.WPR
public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82E3.ONanS6.WPS
public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82E3.ONanS6.WPS2a
public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82E3.ONanS6.WS6
public import CFSG.Sporadic.ON
import CFSG.GroupTheory.CoprimeActionSupport.NormalSubgroupSylowJoin
import CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82E3.CaseOneONan
import CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82.KInputs811K3Holds
import CFSG.HardMathSupport.Solomon.Coordinator.ONCSylow
import CFSG.HardMathSupport.Solomon.Coordinator.C25Group

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82E3.ONan
section
open GroupTheory.CoprimeActionSupport.CentralizerOnQuotientMembership (mem_centralizerOnQuotient)
open CFSG
open scoped commutatorElement
open CFSG.Open
open CFSG.RankThree CFSG.RankThree.PartTwo.Sec4
open CFSG.LocalAnalysis.UniquenessCase.UC22 (Data IsSpor)
open CFSG.LocalAnalysis.UniquenessCase.UCK (ThreeCover)
open CFSG.ASVolI.ChIJK (IsWeaklyClosedIn)
variable {G : Type} [Group G] [Finite G] {D : Data G}

@[expose] def ThreeCoreFrame' (T Z : Subgroup G) (e : G) : Prop :=
  ⁅T, T⁆ ≤ Z ∧
    ∃ C₀ : Subgroup G,
      (∀ x ∈ T ⊓ Subgroup.centralizer (T : Set G), ∃ i : ℤ, ∃ c ∈ C₀, e ^ i * c = x) ∧
      (∀ c ∈ C₀, c ^ 3 = 1 → c ∈ Z)

theorem dichotomy_of_frame' {T U Z C₀ : Subgroup G} {e : G}
    (hUT : U ≤ T) (hUnorm : (U.subgroupOf T).Normal)
    (hU3 : IsPGroup 3 U) (heU : e ∈ U)
    (hZcard : Nat.card Z = 3)
    (hTT : ⁅T, T⁆ ≤ Z)
    (hZT : ∀ x ∈ T ⊓ Subgroup.centralizer (T : Set G), ∃ i : ℤ, ∃ c ∈ C₀, e ^ i * c = x)
    (hC₀ : ∀ c ∈ C₀, c ^ 3 = 1 → c ∈ Z) :
    Z ≤ U ∨ U = Subgroup.zpowers e := by
  classical
  by_cases hZU : Z ≤ U
  · exact Or.inl hZU
  · right
    have hdisj : Disjoint U Z := by
      rw [disjoint_iff, eq_bot_iff]
      intro x hx
      by_contra hx1
      apply hZU
      have hxU : x ∈ U := hx.1
      have hxZ : x ∈ Z := hx.2
      have hdvd : orderOf x ∣ Nat.card Z := Subgroup.orderOf_dvd_natCard Z hxZ
      rw [hZcard] at hdvd
      have hord : orderOf x = 3 := by
        rcases (Nat.dvd_prime Nat.prime_three).mp hdvd with h1 | h3
        · exact absurd (orderOf_eq_one_iff.mp h1) hx1
        · exact h3
      have hcard : Nat.card (Subgroup.zpowers x) = 3 := by
        rw [Nat.card_zpowers, hord]
      have hzle : Subgroup.zpowers x ≤ Z := Subgroup.zpowers_le.mpr hxZ
      have hzeq : Subgroup.zpowers x = Z :=
        Subgroup.eq_of_le_of_card_ge hzle (by rw [hcard, hZcard])
      exact hzeq.symm ▸ Subgroup.zpowers_le.mpr hxU
    have hUcent : U ≤ Subgroup.centralizer (T : Set G) := by
      intro u hu
      rw [Subgroup.mem_centralizer_iff]
      intro t ht
      have hconj : t * u * t⁻¹ ∈ U := by
        have hmemT : t * u * t⁻¹ ∈ T :=
          T.mul_mem (T.mul_mem ht (hUT hu)) (T.inv_mem ht)
        have hmem : (⟨t * u * t⁻¹, hmemT⟩ : T) ∈ U.subgroupOf T := by
          have h := hUnorm.conj_mem (⟨u, hUT hu⟩ : T)
            (Subgroup.mem_subgroupOf.mpr hu) ⟨t, ht⟩
          simpa [Subgroup.mem_subgroupOf, mul_assoc] using h
        exact hmem
      have hcommU : ⁅t, u⁆ ∈ U := by
        rw [commutatorElement_def]
        exact U.mul_mem hconj (U.inv_mem hu)
      have hcommZ : ⁅t, u⁆ ∈ Z :=
        hTT (Subgroup.commutator_mono le_rfl hUT
          (Subgroup.commutator_mem_commutator ht hu))
      have hbot : ⁅t, u⁆ = 1 := by
        have hmem : ⁅t, u⁆ ∈ U ⊓ Z := ⟨hcommU, hcommZ⟩
        rw [hdisj.eq_bot, Subgroup.mem_bot] at hmem
        exact hmem
      exact commutatorElement_eq_one_iff_mul_comm.mp hbot
    apply le_antisymm
    · intro u hu
      obtain ⟨i, c, hcC, huc⟩ := hZT u ⟨hUT hu, hUcent hu⟩
      have hcU : c ∈ U := by
        have heiU : e ^ i ∈ U := U.zpow_mem heU i
        have hc : c = (e ^ i)⁻¹ * u := by
          rw [← huc]
          group
        rw [hc]
        exact U.mul_mem (U.inv_mem heiU) hu
      by_cases hc1 : c = 1
      · rw [hc1, mul_one] at huc
        exact Subgroup.mem_zpowers_iff.mpr ⟨i, huc⟩
      · exfalso
        obtain ⟨n, hn⟩ := (IsPGroup.iff_orderOf.mp hU3) ⟨c, hcU⟩
        have hn0 : n ≠ 0 := by
          intro h0
          rw [h0] at hn
          simp at hn
          exact hc1 hn
        obtain ⟨m, hm⟩ := Nat.exists_eq_succ_of_ne_zero hn0
        have hdvd : 3 ∣ Nat.card (Subgroup.zpowers (⟨c, hcU⟩ : U)) := by
          have hcard : Nat.card (Subgroup.zpowers (⟨c, hcU⟩ : U)) = 3 ^ (m + 1) := by
            rw [Nat.card_zpowers, hn, hm]
          exact hcard ▸ dvd_pow_self 3 (Nat.succ_ne_zero m)
        obtain ⟨d, hdord⟩ := exists_prime_orderOf_dvd_card'
          (G := Subgroup.zpowers (⟨c, hcU⟩ : U)) 3 hdvd
        have hdU : (((d : Subgroup.zpowers (⟨c, hcU⟩ : U)) : U) : G) ∈ U :=
          ((d : Subgroup.zpowers (⟨c, hcU⟩ : U)) : U).2
        have hdC : (((d : Subgroup.zpowers (⟨c, hcU⟩ : U)) : U) : G) ∈ C₀ := by
          have hmem : (((d : Subgroup.zpowers (⟨c, hcU⟩ : U)) : U) : G) ∈ Subgroup.zpowers c := by
            obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp d.2
            refine Subgroup.mem_zpowers_iff.mpr ⟨k, ?_⟩
            have h := congrArg (fun z : U => (z : G)) hk
            simpa using h
          exact Subgroup.zpowers_le.mpr hcC hmem
        have hd3 : (((d : Subgroup.zpowers (⟨c, hcU⟩ : U)) : U) : G) ^ 3 = 1 := by
          have h := congrArg (fun z : Subgroup.zpowers (⟨c, hcU⟩ : U) => ((z : U) : G))
            (pow_orderOf_eq_one d)
          simpa [hdord] using h
        have hdZ : (((d : Subgroup.zpowers (⟨c, hcU⟩ : U)) : U) : G) ∈ Z := hC₀ _ hdC hd3
        have hd1 : (((d : Subgroup.zpowers (⟨c, hcU⟩ : U)) : U) : G) = 1 := by
          have hmem : (((d : Subgroup.zpowers (⟨c, hcU⟩ : U)) : U) : G) ∈ U ⊓ Z :=
            ⟨hdU, hdZ⟩
          rw [hdisj.eq_bot, Subgroup.mem_bot] at hmem
          exact hmem
        have hdne : d ≠ 1 := by
          intro h
          rw [h, orderOf_one] at hdord
          omega
        apply hdne
        apply Subtype.ext
        apply Subtype.ext
        exact hd1
    · exact Subgroup.zpowers_le.mpr heU

theorem pcore_centralizer_le_theta_threeCore_of_frame'
    (hK2 : K2ONanCentralizer) (c : Ctx82E3 D)
    (hON : ThreeCover (fun Y _ => IsSpor Y .ONan) c.Lbar) (h7 : D.sig = {7})
    {P : Subgroup G} (hP : CFSG.ABGLocalTools.IsSylowOf 3 P D.M)
    (hNZ : Subgroup.normalizer ((zSub P c.L : Subgroup G) : Set G) ≤ D.M)
    {e : G} (hP1 : CFSG.ABGLocalTools.IsSylowOf 3
      (P ⊓ Subgroup.centralizer ({e} : Set G)) (Subgroup.centralizer ({e} : Set G)))
    (he : e ∈ P ⊓ c.L) (he3 : orderOf e = 3) (heZ : e ∉ zSub P c.L)
    (hWC : IsWeaklyClosedIn (zSub P c.L) P)
    (hFrame : ThreeCoreFrame' (P ⊓ Subgroup.centralizer ({e} : Set G)) (zSub P c.L) e) :
    ((Subgroup.centralizer ({e} : Set G) ⊓ CFSG.Open.pCoreOf 2 D.M).subgroupOf
        (Subgroup.centralizer ({e} : Set G))).map
        (QuotientGroup.mk' (CFSG.RankThree.LocalRank.aschbacherSolvableCore 3
          ↥(Subgroup.centralizer ({e} : Set G)))) ≤
      Subgroup.centralizer
        ((CFSG.pCore 3 (↥(Subgroup.centralizer ({e} : Set G)) ⧸
          CFSG.RankThree.LocalRank.aschbacherSolvableCore 3
            ↥(Subgroup.centralizer ({e} : Set G))) : Subgroup _) : Set _) := by
  classical
  let H : Subgroup G := Subgroup.centralizer ({e} : Set G)
  let θ : Subgroup H := CFSG.RankThree.LocalRank.aschbacherSolvableCore 3 H
  let X := H ⧸ θ
  let π : H →* X := QuotientGroup.mk' θ
  let R : Subgroup H := (CFSG.pCore 3 X).comap π
  let T : Subgroup H := (P ⊓ H).subgroupOf H
  let U : Subgroup H := T ⊓ R
  let Z : Subgroup G := zSub P c.L
  let W : Subgroup G := Subgroup.centralizer ({e} : Set G) ⊓ CFSG.Open.pCoreOf 2 D.M
  let K : Subgroup G := H ⊓ D.M
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hθX : CFSG.RankThree.LocalRank.aschbacherSolvableCore 3 X = ⊥ :=
    (CFSG.RankThree.theta_quotient_core_and_ranks (G := H)).1
  have hcore2 : CFSG.pCore 2 X = ⊥ := by
    apply le_bot_iff.mp
    haveI : Group.IsNilpotent ↥(CFSG.pCore 2 X) :=
      (CFSG.pCore_isPGroup (p := 2) (G := X)).isNilpotent
    haveI : Group.IsSolvable ↥(CFSG.pCore 2 X) := inferInstance
    have hmaxX := (CFSG.RankThree.LocalRank.solvable_prime_complement_core_characterization (H := X)
      Nat.prime_three).2.2.2.1
    exact (hmaxX (CFSG.pCore 2 X) inferInstance inferInstance
      (CFSG.GroupTheory.not_dvd_card_of_isPGroup
        (CFSG.pCore_isPGroup (p := 2) (G := X)) Nat.prime_three (by norm_num))).trans
      (le_of_eq hθX)
  have hmapT : T.map H.subtype = P ⊓ H := by
    simpa [T] using Subgroup.map_subgroupOf_eq_of_le (H := P ⊓ H) (K := H) inf_le_right
  have hTH : CFSG.ABGLocalTools.IsSylowOf 3 T (⊤ : Subgroup H) := by
    rw [← CFSG.ABGLocalTools.isSylowOf_map_subtype_iff H]
    simpa [hmapT, H, Subgroup.map_top, Subgroup.range_subtype] using hP1
  have hRnormal : R.Normal := by
    dsimp [R]
    infer_instance
  have hUR : CFSG.ABGLocalTools.IsSylowOf 3 U R := by
    have htop : (⊤ : Subgroup H) ≤ Subgroup.normalizer (R : Set H) := by
      rw [Subgroup.normalizer_eq_top_iff.mpr hRnormal]
    simpa [U] using hTH.inf_of_le_normalizer (N := R) le_top htop
  have heH : e ∈ H := Subgroup.mem_centralizer_singleton_iff.mpr rfl
  let eH : H := ⟨e, heH⟩
  have heT : eH ∈ T := by
    rw [Subgroup.mem_subgroupOf]
    exact ⟨he.1, heH⟩
  have heH_center : eH ∈ Subgroup.center H := by
    rw [Subgroup.mem_center_iff]
    intro h
    apply Subtype.ext
    exact Subgroup.mem_centralizer_singleton_iff.mp h.2
  have heH3 : eH ^ 3 = 1 := by
    apply Subtype.ext
    change e ^ 3 = 1
    rw [← he3]
    exact pow_orderOf_eq_one e
  have heHne : eH ≠ 1 := by
    intro h1
    apply heZ
    have he1 : e = 1 := congrArg Subtype.val h1
    rw [he1]
    exact Subgroup.one_mem _
  have heHord : orderOf eH = 3 := orderOf_eq_prime heH3 heHne
  have hzp3 : IsPGroup 3 (Subgroup.zpowers eH) := by
    apply IsPGroup.of_card (n := 1)
    rw [Nat.card_zpowers, heHord]
    norm_num
  have hzp_normal : (Subgroup.zpowers eH).Normal :=
    Subgroup.normal_of_le_center (Subgroup.zpowers_le.mpr heH_center)
  have heH_pcore : eH ∈ CFSG.pCore 3 H := by
    change eH ∈ sSup {K : Subgroup H | K.Normal ∧ IsPGroup 3 K}
    exact le_sSup (s := {K : Subgroup H | K.Normal ∧ IsPGroup 3 K})
      ⟨hzp_normal, hzp3⟩ (Subgroup.mem_zpowers eH)
  have hle_map : (CFSG.pCore 3 H).map π ≤ CFSG.pCore 3 X :=
    (CFSG.RankThree.theta_quotient_three_subgroups (G := H)).2.1
  have heR : eH ∈ R := by
    rw [show R = (CFSG.pCore 3 X).comap π from rfl, Subgroup.mem_comap]
    exact hle_map (Subgroup.mem_map_of_mem π heH_pcore)
  have heU : eH ∈ U := Subgroup.mem_inf.mpr ⟨heT, heR⟩
  have hker3 : ¬ 3 ∣ Nat.card ↥(MonoidHom.ker π) := by
    rw [QuotientGroup.ker_mk']
    exact CFSG.RankThree.three_not_dvd_card_aschbacherSolvableCore
  have hRmap : R.map π = CFSG.pCore 3 X := by
    dsimp [R]
    exact Subgroup.map_comap_eq_self_of_surjective (QuotientGroup.mk'_surjective θ)
      (CFSG.pCore 3 X)
  have hSylπ : CFSG.ABGLocalTools.IsSylowOf 3 (U.map π) (CFSG.pCore 3 X) := by
    have h := CFSG.isSylowOf_map_of_not_dvd_card_ker π
      (QuotientGroup.mk'_surjective θ) Nat.prime_three hker3 hUR
    rwa [hRmap] at h
  have hUmaps : U.map π = CFSG.pCore 3 X := by
    have hEq : CFSG.pCore 3 X = U.map π :=
      hSylπ.eq_of_le hSylπ.le le_rfl (CFSG.pCore_isPGroup (p := 3) (G := X))
    exact hEq.symm
  have hZcard : Nat.card Z = 3 := by
    simpa [Z, zSub] using c.card_inf_centralizer_of_onan hON hP
  obtain ⟨hTT, C₀, hZT, hC₀⟩ := hFrame
  let TG : Subgroup G := P ⊓ H
  let UG : Subgroup G := U.map H.subtype
  have hUGleTG : UG ≤ TG := by
    intro x hx
    obtain ⟨u, hu, rfl⟩ := Subgroup.mem_map.mp hx
    exact Subgroup.mem_subgroupOf.mp hu.1
  have hU3 : IsPGroup 3 U := hUR.isPGroup
  have hUG3 : IsPGroup 3 UG := hU3.map H.subtype
  have hUnormG : (UG.subgroupOf TG).Normal := by
    refine ⟨fun w hw k => ?_⟩
    have hwUG : (w : G) ∈ UG := Subgroup.mem_subgroupOf.mp hw
    have hwTG : (w : G) ∈ TG := w.2
    have hkTG : (k : G) ∈ TG := k.2
    let wH : H := ⟨(w : G), hwTG.2⟩
    let kH : H := ⟨(k : G), hkTG.2⟩
    have hwU : wH ∈ U := by
      obtain ⟨u, huU, hu⟩ := Subgroup.mem_map.mp hwUG
      have hu_eq : u = wH := Subtype.ext hu
      rwa [hu_eq] at huU
    have hwT : wH ∈ T := Subgroup.mem_subgroupOf.mpr hwTG
    have hkT : kH ∈ T := Subgroup.mem_subgroupOf.mpr hkTG
    have hwR : wH ∈ R := hwU.2
    have hconjU : kH * wH * kH⁻¹ ∈ U := by
      refine ⟨T.mul_mem (T.mul_mem hkT hwT) (T.inv_mem hkT), ?_⟩
      exact hRnormal.conj_mem wH hwR kH
    refine Subgroup.mem_subgroupOf.mpr ?_
    exact Subgroup.mem_map.mpr ⟨kH * wH * kH⁻¹, hconjU, rfl⟩
  have heUG : e ∈ UG := Subgroup.mem_map.mpr ⟨eH, heU, rfl⟩
  have hWnormal : (W.subgroupOf K).Normal :=
    twoCoreCen_normal_in_cen_inf_M
      (Subgroup.le_normalizer.trans
        (CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 D.M))
  let WX : Subgroup X := (W.subgroupOf H).map π
  change WX ≤ Subgroup.centralizer ((CFSG.pCore 3 X : Subgroup X) : Set X)
  have hQ2 : IsPGroup 2 (CFSG.Open.pCoreOf 2 D.M) :=
    CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 D.M
  have hW2G : IsPGroup 2 W := hQ2.to_le inf_le_right
  have hW2H : IsPGroup 2 (W.subgroupOf H) :=
    hW2G.of_equiv (Subgroup.subgroupOfEquivOfLe (inf_le_left : W ≤ H)).symm
  have hWX2 : IsPGroup 2 WX := hW2H.map π
  have hDich : Z ≤ UG ∨ UG = Subgroup.zpowers e :=
    dichotomy_of_frame' hUGleTG hUnormG hUG3 heUG hZcard hTT hZT hC₀
  rcases hDich with hZU | hUG
  ·
    have hNleK : (⊤ ⊓ Subgroup.normalizer (U : Set H)) ≤ K.subgroupOf H := by
      intro n hn
      rw [Subgroup.mem_subgroupOf]
      refine ⟨n.2, ?_⟩
      have hnU : n ∈ Subgroup.normalizer (U : Set H) := hn.2
      have hconjUG : CFSG.conjugate UG n.1 = UG := by
        dsimp [UG]
        change CFSG.conjugate (U.map H.subtype) (H.subtype n) = U.map H.subtype
        rw [← CFSG.map_conjugate]
        rw [CFSG.conjugate_eq_self_of_mem_normalizer hnU]
      have hmemN : n.1 ∈ Subgroup.normalizer (UG : Set G) := by
        rw [Subgroup.mem_normalizer_iff]
        intro x
        constructor
        · intro hx
          have hxc : x ∈ CFSG.conjugate UG n.1 := by rw [hconjUG]; exact hx
          exact (CFSG.mem_conjugate_iff UG n.1 x).mp hxc
        · intro hx
          have hxc : x ∈ CFSG.conjugate UG n.1 := (CFSG.mem_conjugate_iff UG n.1 x).mpr hx
          rwa [hconjUG] at hxc
      exact normalizer_le_M_of_weaklyClosed hWC hNZ hZU
        (hUGleTG.trans inf_le_left) hmemN
    have hRtop : (⊤ : Subgroup H) ≤ Subgroup.normalizer (R : Set H) := by
      rw [Subgroup.normalizer_eq_top_iff.mpr hRnormal]
    have hfr : (⊤ : Subgroup H) = R ⊔ (⊤ ⊓ Subgroup.normalizer (U : Set H)) :=
      CFSG.LocalAnalysis.UniquenessCase.UC6.frattini_of_isSylowOf
        (H := (⊤ : Subgroup H)) (L := R) (P := U) le_top hRtop hUR
    have hHsplit : (⊤ : Subgroup H) ≤ θ ⊔ K.subgroupOf H := by
      intro h hh
      have hhfr : h ∈ R ⊔ (⊤ ⊓ Subgroup.normalizer (U : Set H)) := by
        rw [← hfr]
        exact hh
      haveI : R.Normal := hRnormal
      rw [Subgroup.mem_sup_of_normal_left] at hhfr
      obtain ⟨r, hr, n, hn, hrn⟩ := hhfr
      have hπr : π r ∈ CFSG.pCore 3 X := hr
      rw [← hUmaps] at hπr
      obtain ⟨u, huU, huπ⟩ := Subgroup.mem_map.mp hπr
      have hru_theta : r * u⁻¹ ∈ θ := by
        apply (QuotientGroup.eq_one_iff (r * u⁻¹)).mp
        change π (r * u⁻¹) = 1
        rw [map_mul, map_inv, huπ, mul_inv_cancel]
      have huN : u ∈ K.subgroupOf H :=
        hNleK (Subgroup.mem_inf.mpr ⟨Subgroup.mem_top u, Subgroup.le_normalizer huU⟩)
      have hnN : n ∈ K.subgroupOf H :=
        hNleK (Subgroup.mem_inf.mpr ⟨Subgroup.mem_top n, hn.2⟩)
      have hr_mem : r ∈ θ ⊔ K.subgroupOf H := by
        let v : H := r * u⁻¹
        have hvθ : v ∈ θ := hru_theta
        have h1 : r = v * u := by
          dsimp [v]
          group
        have hprod : v * u ∈ θ ⊔ K.subgroupOf H :=
          (θ ⊔ K.subgroupOf H).mul_mem
            (Subgroup.mem_sup_left hvθ) (Subgroup.mem_sup_right huN)
        exact h1.symm ▸ hprod
      rw [← hrn]
      exact (θ ⊔ K.subgroupOf H).mul_mem hr_mem (Subgroup.mem_sup_right hnN)
    let fK : K →* X := π.comp (Subgroup.inclusion (inf_le_left : K ≤ H))
    have hfKsurj : Function.Surjective fK := by
      intro x
      obtain ⟨h, rfl⟩ := QuotientGroup.mk'_surjective θ x
      have hh : h ∈ θ ⊔ K.subgroupOf H := hHsplit (Subgroup.mem_top h)
      haveI : θ.Normal := inferInstance
      rw [Subgroup.mem_sup_of_normal_left] at hh
      obtain ⟨t, ht, k, hk, htk⟩ := hh
      have hkK : k.1 ∈ K := Subgroup.mem_subgroupOf.mp hk
      refine ⟨⟨k.1, hkK⟩, ?_⟩
      change π k = π h
      have ht1 : π t = 1 := (QuotientGroup.eq_one_iff t).mpr ht
      rw [← htk, map_mul, ht1, one_mul]
    have hWXeq : (W.subgroupOf K).map fK = WX := by
      ext x
      constructor
      · intro hx
        obtain ⟨w, hw, rfl⟩ := Subgroup.mem_map.mp hx
        have hwW : w.1 ∈ W := Subgroup.mem_subgroupOf.mp hw
        refine Subgroup.mem_map.mpr ⟨⟨w.1, hwW.1⟩, ?_, rfl⟩
        exact Subgroup.mem_subgroupOf.mpr hwW
      · intro hx
        obtain ⟨w, hw, rfl⟩ := Subgroup.mem_map.mp hx
        have hwW : w.1 ∈ W := Subgroup.mem_subgroupOf.mp hw
        have hwK : w.1 ∈ K := ⟨hwW.1, Subgroup.map_subtype_le _ hwW.2⟩
        refine Subgroup.mem_map.mpr ⟨⟨w.1, hwK⟩, ?_, ?_⟩
        · exact Subgroup.mem_subgroupOf.mpr hwW
        · rfl
    have hWXnormal : WX.Normal := by
      rw [← hWXeq]
      exact Subgroup.Normal.map hWnormal fK hfKsurj
    have hWXle : WX ≤ CFSG.pCore 2 X := by
      change WX ≤ sSup {Q : Subgroup X | Q.Normal ∧ IsPGroup 2 Q}
      exact le_sSup (s := {Q : Subgroup X | Q.Normal ∧ IsPGroup 2 Q})
        ⟨hWXnormal, hWX2⟩
    have hWXbot : WX = ⊥ := le_bot_iff.mp (hWXle.trans (le_of_eq hcore2))
    rw [hWXbot]
    exact bot_le
  ·
    have hUGsub : (U.map H.subtype).subgroupOf H = U := by
      ext u
      rw [Subgroup.mem_subgroupOf, Subgroup.mem_map]
      constructor
      · rintro ⟨u', hu', hu''⟩
        rwa [Subtype.ext hu''] at hu'
      · intro hu
        exact ⟨u, hu, rfl⟩
    have hzp_sub : (Subgroup.zpowers e).subgroupOf H = Subgroup.zpowers eH := by
      ext x
      simp only [Subgroup.mem_subgroupOf, Subgroup.mem_zpowers_iff]
      constructor
      · rintro ⟨k, hk⟩
        exact ⟨k, Subtype.ext (by simpa [eH] using hk)⟩
      · rintro ⟨k, hk⟩
        exact ⟨k, by simpa [eH] using congrArg Subtype.val hk⟩
    have hpCore_eq : CFSG.pCore 3 X = Subgroup.zpowers (π eH) := by
      rw [← hUmaps]
      calc
        U.map π = ((U.map H.subtype).subgroupOf H).map π := by rw [hUGsub]
        _ = ((Subgroup.zpowers e).subgroupOf H).map π := by
          rw [show Subgroup.map H.subtype U = Subgroup.zpowers e from hUG]
        _ = (Subgroup.zpowers eH).map π := by rw [hzp_sub]
        _ = Subgroup.zpowers (π eH) := by rw [MonoidHom.map_zpowers]
    rw [hpCore_eq]
    intro x hx
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    change y ∈ Subgroup.zpowers (π eH) at hy
    rw [Subgroup.mem_zpowers_iff] at hy
    obtain ⟨k, rfl⟩ := hy
    obtain ⟨w, hw, rfl⟩ := Subgroup.mem_map.mp hx
    have hwW : w.1 ∈ W := Subgroup.mem_subgroupOf.mp hw
    have hwC : w.1 ∈ Subgroup.centralizer ({e} : Set G) := hwW.1
    have hcomm : w.1 * e = e * w.1 :=
      Subgroup.mem_centralizer_singleton_iff.mp hwC
    have hcommH : w * eH = eH * w := by
      apply Subtype.ext
      simpa [eH] using hcomm
    have hcommX : π w * π eH = π eH * π w := by
      rw [← map_mul, ← map_mul, hcommH]
    have hcommute : Commute (π w) (π eH) := hcommX
    exact (hcommute.zpow_right k).eq.symm

noncomputable abbrev pl7ModCen_wPL7 (c : Ctx82E3 D) : Subgroup G :=
  CFSG.LocalAnalysis.RankThreeUC.centralizerOnQuotient D.M
    (CFSG.Open.pCoreOf 2 c.L) c.L

noncomputable abbrev pl7Q_wPL7 {D : Data G} (P : Subgroup G) (c : Ctx82E3 D) :
    Subgroup G :=
  P ⊓ c.L

noncomputable abbrev pl7C0_wPL7 {D : Data G} (P : Subgroup G) (c : Ctx82E3 D) :
    Subgroup G :=
  P ⊓ pl7ModCen_wPL7 c

noncomputable abbrev pl7T_wPL7 (P : Subgroup G) (e : G) : Subgroup G :=
  P ⊓ Subgroup.centralizer ({e} : Set G)

theorem pl7_center_map_eq_wPL7 (Q : Subgroup G) :
    (Subgroup.center ↥Q).map Q.subtype = Q ⊓ Subgroup.centralizer (Q : Set G) := by
  ext x
  constructor
  · rintro ⟨z, hz, rfl⟩
    refine ⟨z.2, ?_⟩
    exact Subgroup.mem_centralizer_iff.mpr (fun y hy =>
      congrArg Subtype.val (Subgroup.mem_center_iff.mp hz ⟨y, hy⟩))
  · rintro ⟨hxQ, hxC⟩
    refine ⟨⟨x, hxQ⟩, ?_, rfl⟩
    exact Subgroup.mem_center_iff.mpr (fun y => Subtype.ext
      ((Subgroup.mem_centralizer_iff.mp hxC) y y.2))

theorem pl7_card_Lbar_wPL7
    (c : Ctx82E3 D) (hON : ThreeCover (fun Y _ => IsSpor Y .ONan) c.Lbar) :
    Nat.card c.Lbar = 3 * 460815505920 := by
  have h := Subgroup.card_eq_card_quotient_mul_card_subgroup (Subgroup.center c.Lbar)
  obtain ⟨e⟩ := hON.2.2
  have hq : Nat.card (c.Lbar ⧸ Subgroup.center c.Lbar) = 460815505920 := by
    rw [Nat.card_congr e.toEquiv]
    change Nat.card CFSG.Blueprint.NativeSporadic.ON = 460815505920
    exact CFSG.Sporadic.ON.card_ON_eq
  rw [h, hq, hON.2.1]

theorem pl7_factorization_card_Lbar_wPL7 (c : Ctx82E3 D)
    (hON : ThreeCover (fun Y _ => IsSpor Y .ONan) c.Lbar) :
    (Nat.card c.Lbar).factorization 3 = 5 := by
  rw [pl7_card_Lbar_wPL7 c hON]
  have h : 3 * 460815505920 = 3 ^ 5 * 5689080320 := by norm_num
  rw [h, Nat.factorization_mul (by norm_num) (by norm_num), Finsupp.add_apply,
    Nat.Prime.factorization_pow Nat.prime_three,
    Nat.factorization_eq_zero_of_not_dvd (by norm_num)]
  norm_num

theorem pl7_factorization_card_L_wPL7 (c : Ctx82E3 D)
    (hON : ThreeCover (fun Y _ => IsSpor Y .ONan) c.Lbar) :
    (Nat.card ↥c.L).factorization 3 = 5 := by
  let O : Subgroup ↥c.L := CFSG.Open.pCore 2 ↥c.L
  have hN3 : ¬ 3 ∣ Nat.card O :=
    CFSG.GroupTheory.not_dvd_card_of_isPGroup (p := 2) (q := 3)
      (CFSG.pCore_isPGroup (p := 2) (G := ↥c.L)) Nat.prime_three (by norm_num)
  have hcardL : Nat.card ↥c.L = Nat.card c.Lbar * Nat.card O :=
    Subgroup.card_eq_card_quotient_mul_card_subgroup O
  rw [hcardL, Nat.factorization_mul (Nat.card_pos.ne') (Nat.card_pos.ne'),
    Finsupp.add_apply, Nat.factorization_eq_zero_of_not_dvd hN3, add_zero,
    pl7_factorization_card_Lbar_wPL7 c hON]

theorem pl7_card_Q_wPL7 (c : Ctx82E3 D)
    (hON : ThreeCover (fun Y _ => IsSpor Y .ONan) c.Lbar)
    {P : Subgroup G} (hP : CFSG.ABGLocalTools.IsSylowOf 3 P D.M) :
    Nat.card ↥(pl7Q_wPL7 P c) = 3 ^ 5 := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hPL : CFSG.ABGLocalTools.IsSylowOf 3 (pl7Q_wPL7 P c) c.L :=
    hP.inf_of_le_normalizer c.hyp81.1 c.le_normalizer_L
  rw [hPL.card_eq, pl7_factorization_card_L_wPL7 c hON]

theorem pl7_card_center_Q_wPL7
    (c : Ctx82E3 D)
    (hON : ThreeCover (fun Y _ => IsSpor Y .ONan) c.Lbar)
    {P : Subgroup G} (hP : CFSG.ABGLocalTools.IsSylowOf 3 P D.M) :
    Nat.card (Subgroup.center ↥(pl7Q_wPL7 P c)) = 3 := by
  have hcardmap : Nat.card (Subgroup.center ↥(pl7Q_wPL7 P c)) =
      Nat.card ↥((Subgroup.center ↥(pl7Q_wPL7 P c)).map (pl7Q_wPL7 P c).subtype) :=
    (Subgroup.card_map_of_injective (pl7Q_wPL7 P c).subtype_injective).symm
  rw [hcardmap, pl7_center_map_eq_wPL7]
  simpa [zSub, pl7Q_wPL7] using c.card_inf_centralizer_of_onan hON hP

theorem pl7_exp_Q_wPL7
    (c : Ctx82E3 D) (hON : ThreeCover (fun Y _ => IsSpor Y .ONan) c.Lbar)
    {P : Subgroup G} (hP : CFSG.ABGLocalTools.IsSylowOf 3 P D.M) :
    ∀ x ∈ pl7Q_wPL7 P c, x ^ 3 = 1 :=
  c.pow_three_eq_one_of_mem_inf_L_of_onan hON hP

theorem pl7_commutator_Q_wPL7
    (c : Ctx82E3 D) (hON : ThreeCover (fun Y _ => IsSpor Y .ONan) c.Lbar)
    {P : Subgroup G} (hP : CFSG.ABGLocalTools.IsSylowOf 3 P D.M) :
    ⁅pl7Q_wPL7 P c, pl7Q_wPL7 P c⁆ ≤ zSub P c.L := by
  classical
  letI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  let O : Subgroup ↥c.L := CFSG.Open.pCore 2 ↥c.L
  let π : ↥c.L →* c.Lbar := QuotientGroup.mk' O
  let QL : Subgroup ↥c.L := (pl7Q_wPL7 P c).subgroupOf c.L
  have hQ3 : IsPGroup 3 (pl7Q_wPL7 P c) := hP.isPGroup.to_le inf_le_left
  have hQL3 : IsPGroup 3 QL := hQ3.comap_subtype
  have hQbar3 : IsPGroup 3 (QL.map π) := hQL3.map π
  obtain ⟨S, hSle⟩ := IsPGroup.exists_le_sylow hQbar3
  have hHat : CFSG.HardMathSupport.Solomon.LocalBalance.IsHatON c.Lbar :=
    isHatON_lbar_of_onan_wPH2 c hON
  have hcommS := (CFSG.HardMathSupport.Solomon.Coordinator.inputONSylow_holds
    c.Lbar hHat S).2.2.1
  rw [Subgroup.commutator_le]
  intro x hx y hy
  have hxL : x ∈ c.L := hx.2
  have hyL : y ∈ c.L := hy.2
  have hxQL : (⟨x, hxL⟩ : ↥c.L) ∈ QL :=
    Subgroup.mem_subgroupOf.mpr hx
  have hyQL : (⟨y, hyL⟩ : ↥c.L) ∈ QL :=
    Subgroup.mem_subgroupOf.mpr hy
  have hxS : π ⟨x, hxL⟩ ∈ (S : Subgroup c.Lbar) :=
    hSle (Subgroup.mem_map_of_mem π hxQL)
  have hyS : π ⟨y, hyL⟩ ∈ (S : Subgroup c.Lbar) :=
    hSle (Subgroup.mem_map_of_mem π hyQL)
  have hcommSub : (⁅(⟨x, hxL⟩ : ↥c.L), (⟨y, hyL⟩ : ↥c.L)⁆) ∈
      (Subgroup.center c.Lbar).comap π := by
    rw [Subgroup.mem_comap, map_commutatorElement]
    exact hcommS _ hxS _ hyS
  have hmemCP : ⁅x, y⁆ ∈ centerPreimage_of_onan c := by
    refine Subgroup.mem_map.mpr ⟨⁅(⟨x, hxL⟩ : ↥c.L), (⟨y, hyL⟩ : ↥c.L)⁆, hcommSub, ?_⟩
    simp [commutatorElement_def]
  have hxyP : ⁅x, y⁆ ∈ P := by
    rw [commutatorElement_def]
    exact P.mul_mem (P.mul_mem (P.mul_mem hx.1 hy.1) (P.inv_mem hx.1)) (P.inv_mem hy.1)
  exact inf_centerPreimage_sylow_le_zSub_of_onan c hON hP ⟨hmemCP, hxyP⟩

theorem pl7_e_not_center_Q_wPL7 (c : Ctx82E3 D)
    {P : Subgroup G} {e : G} (he : e ∈ pl7Q_wPL7 P c) (heZ : e ∉ zSub P c.L) :
    (⟨e, he⟩ : ↥(pl7Q_wPL7 P c)) ∉ Subgroup.center ↥(pl7Q_wPL7 P c) := by
  intro hcenter
  have hmem : e ∈ (Subgroup.center ↥(pl7Q_wPL7 P c)).map (pl7Q_wPL7 P c).subtype :=
    Subgroup.mem_map.mpr ⟨⟨e, he⟩, hcenter, rfl⟩
  rw [pl7_center_map_eq_wPL7] at hmem
  exact heZ (by simpa [zSub, pl7Q_wPL7] using hmem)

theorem pl7_card_centralizer_of_card_three_pow_five_wPL7 {Q : Type*} [Group Q] [Finite Q]
    (hcard : Nat.card Q = 3 ^ 5) (hZ : Nat.card (Subgroup.center Q) = 3)
    (hcomm : ∀ a b : Q, ⁅a, b⁆ ∈ Subgroup.center Q) {g : Q}
    (hg : g ∉ Subgroup.center Q) :
    Nat.card (Subgroup.centralizer ({g} : Set Q)) = 81 := by
  classical
  letI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hidx_le : (Subgroup.centralizer ({g} : Set Q)).index ≤ 3 :=
    CFSG.HardMathSupport.Solomon.Coordinator.c25_index_centralizer_le hZ hcomm g
  have hidx_dvd : (Subgroup.centralizer ({g} : Set Q)).index ∣ 3 ^ 5 := by
    rw [← hcard]
    exact Subgroup.index_dvd_card _
  obtain ⟨i, -, hi⟩ := (Nat.dvd_prime_pow Nat.prime_three).mp hidx_dvd
  have hi_le : i ≤ 1 := by
    by_contra h
    have h2 : 2 ≤ i := by omega
    have h3 : 3 ^ 2 ≤ 3 ^ i := Nat.pow_le_pow_right (by norm_num) h2
    rw [hi] at hidx_le
    norm_num at h3
    omega
  have hidx_ne : (Subgroup.centralizer ({g} : Set Q)).index ≠ 1 := by
    intro hone
    apply hg
    have htop : Subgroup.centralizer ({g} : Set Q) = ⊤ := Subgroup.index_eq_one.mp hone
    refine Subgroup.mem_center_iff.mpr (fun x => ?_)
    have hx : x ∈ Subgroup.centralizer ({g} : Set Q) := by rw [htop]; exact Subgroup.mem_top x
    exact Subgroup.mem_centralizer_singleton_iff.mp hx
  have hidx : (Subgroup.centralizer ({g} : Set Q)).index = 3 := by
    interval_cases i
    · rw [hi] at hidx_ne
      norm_num at hidx_ne
    · simpa [hi] using rfl
  have hmul := Subgroup.card_mul_index (Subgroup.centralizer ({g} : Set Q))
  rw [hidx, hcard] at hmul
  norm_num at hmul ⊢
  omega

theorem pl7_card_centralizer_Q_wPL7
    (c : Ctx82E3 D) (hON : ThreeCover (fun Y _ => IsSpor Y .ONan) c.Lbar)
    {P : Subgroup G} (hP : CFSG.ABGLocalTools.IsSylowOf 3 P D.M)
    {e : G} (he : e ∈ pl7Q_wPL7 P c) (heZ : e ∉ zSub P c.L) :
    Nat.card ↥(pl7Q_wPL7 P c ⊓ Subgroup.centralizer ({e} : Set G)) = 81 := by
  classical
  let Q : Subgroup G := pl7Q_wPL7 P c
  have hcomm : ∀ a b : ↥Q, ⁅a, b⁆ ∈ Subgroup.center ↥Q := by
    intro a b
    have hamb : ⁅(a : G), (b : G)⁆ ∈ zSub P c.L :=
      pl7_commutator_Q_wPL7 c hON hP (Subgroup.commutator_mem_commutator a.2 b.2)
    rw [show zSub P c.L = (Subgroup.center ↥Q).map Q.subtype from
      (pl7_center_map_eq_wPL7 Q).symm] at hamb
    obtain ⟨z, hz, hzeq⟩ := Subgroup.mem_map.mp hamb
    have hEq : ⁅a, b⁆ = z := by
      apply Subtype.ext
      simpa [commutatorElement_def] using hzeq.symm
    rwa [hEq]
  have hcard : Nat.card ↥Q = 3 ^ 5 := pl7_card_Q_wPL7 c hON hP
  have hZ : Nat.card (Subgroup.center ↥Q) = 3 := pl7_card_center_Q_wPL7 c hON hP
  have hg : (⟨e, he⟩ : ↥Q) ∉ Subgroup.center ↥Q := pl7_e_not_center_Q_wPL7 c he heZ
  have hcent := pl7_card_centralizer_of_card_three_pow_five_wPL7 hcard hZ hcomm hg
  have hmap : (Subgroup.centralizer ({⟨e, he⟩} : Set ↥Q)).map Q.subtype =
      Q ⊓ Subgroup.centralizer ({e} : Set G) := by
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      refine ⟨y.2, ?_⟩
      exact Subgroup.mem_centralizer_singleton_iff.mpr
        (congrArg Subtype.val (Subgroup.mem_centralizer_singleton_iff.mp hy))
    · rintro ⟨hxQ, hxC⟩
      refine ⟨⟨x, hxQ⟩, ?_, rfl⟩
      exact Subgroup.mem_centralizer_singleton_iff.mpr
        (Subtype.ext (Subgroup.mem_centralizer_singleton_iff.mp hxC))
  have hcardmap : Nat.card ↥((Subgroup.centralizer ({⟨e, he⟩} : Set ↥Q)).map Q.subtype) =
      Nat.card ↥(Subgroup.centralizer ({⟨e, he⟩} : Set ↥Q)) :=
    Subgroup.card_map_of_injective Q.subtype_injective
  rw [← hmap, hcardmap]
  exact hcent

theorem pl7_center_centralizer_Q_wPL7
    (c : Ctx82E3 D) (hON : ThreeCover (fun Y _ => IsSpor Y .ONan) c.Lbar)
    {P : Subgroup G} (hP : CFSG.ABGLocalTools.IsSylowOf 3 P D.M)
    {e : G} (he : e ∈ pl7Q_wPL7 P c) (he3 : orderOf e = 3) (heZ : e ∉ zSub P c.L) :
    (Subgroup.center ↥(pl7Q_wPL7 P c ⊓ Subgroup.centralizer ({e} : Set G))).map
        (pl7Q_wPL7 P c ⊓ Subgroup.centralizer ({e} : Set G)).subtype =
      Subgroup.zpowers e ⊔ zSub P c.L := by
  classical
  letI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  let Q : Subgroup G := pl7Q_wPL7 P c
  let S : Subgroup G := Q ⊓ Subgroup.centralizer ({e} : Set G)
  let Z : Subgroup G := zSub P c.L
  have hS_card : Nat.card ↥S = 81 := pl7_card_centralizer_Q_wPL7 c hON hP he heZ
  have hS_exp : ∀ x ∈ S, x ^ 3 = 1 := fun x hx => pl7_exp_Q_wPL7 c hON hP x hx.1
  have hZ_card : Nat.card Z = 3 := c.card_inf_centralizer_of_onan hON hP
  have heS : e ∈ S :=
    ⟨he, Subgroup.mem_centralizer_singleton_iff.mpr (by group)⟩
  have hZleQ : Z ≤ Q := inf_le_left
  have hZleC : Z ≤ Subgroup.centralizer ({e} : Set G) := by
    intro z hz
    exact Subgroup.mem_centralizer_singleton_iff.mpr
      (Subgroup.mem_centralizer_iff.mp hz.2 e he).symm
  have hZleS : Z ≤ S := le_inf hZleQ hZleC
  have hcomm : ∀ a ∈ Subgroup.zpowers e, ∀ b ∈ Z, a * b = b * a := by
    intro a ha b hb
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp ha
    have hbe : Commute e b := Subgroup.mem_centralizer_iff.mp hb.2 e he
    exact (hbe.zpow_left k).eq
  have hdisj : Subgroup.zpowers e ⊓ Z = ⊥ := by
    rw [eq_bot_iff]
    intro x hx
    by_contra hx1
    have hHcard : Nat.card (Subgroup.zpowers x) = 3 := by
      have hdvd : Nat.card (Subgroup.zpowers x) ∣ 3 := by
        have h := Subgroup.card_dvd_of_le (Subgroup.zpowers_le.mpr hx.1)
        rwa [Nat.card_zpowers e, he3] at h
      rcases (Nat.dvd_prime Nat.prime_three).mp hdvd with h | h
      · exfalso
        apply hx1
        have hxord : orderOf x = 1 := by
          rw [← Nat.card_zpowers x, h]
        exact orderOf_eq_one_iff.mp hxord
      · exact h
    have hzx : Subgroup.zpowers x = Subgroup.zpowers e :=
      Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le.mpr hx.1)
        (by rw [hHcard, Nat.card_zpowers e, he3])
    have hxZle : Subgroup.zpowers x ≤ Z := Subgroup.zpowers_le.mpr hx.2
    exact heZ (hxZle (by rw [hzx]; exact Subgroup.mem_zpowers e))
  have hcardSup : Nat.card ↥(Subgroup.zpowers e ⊔ Z) = 9 := by
    have hsupcard := CFSG.card_sup_eq_mul_of_commute (G := G) (Subgroup.zpowers e) Z
      (fun a ha b hb => hcomm a ha b hb) hdisj
    change Nat.card ↥(Subgroup.zpowers e ⊔ Z) = 9
    rw [hsupcard, Nat.card_zpowers e, he3, hZ_card]
  have he_center : (⟨e, heS⟩ : ↥S) ∈ Subgroup.center ↥S := by
    rw [Subgroup.mem_center_iff]
    intro y
    apply Subtype.ext
    exact Subgroup.mem_centralizer_singleton_iff.mp y.2.2
  have hzp_le : Subgroup.zpowers e ≤ (Subgroup.center ↥S).map S.subtype :=
    Subgroup.zpowers_le.mpr (Subgroup.mem_map.mpr ⟨⟨e, heS⟩, he_center, rfl⟩)
  have hZ_center : Z ≤ (Subgroup.center ↥S).map S.subtype := by
    intro z hz
    have hzS : z ∈ S :=
      ⟨hz.1, Subgroup.mem_centralizer_singleton_iff.mpr
        (Subgroup.mem_centralizer_iff.mp hz.2 e he).symm⟩
    have hzc : (⟨z, hzS⟩ : ↥S) ∈ Subgroup.center ↥S := by
      rw [Subgroup.mem_center_iff]
      intro y
      apply Subtype.ext
      exact Subgroup.mem_centralizer_iff.mp hz.2 (y : G) y.2.1
    exact Subgroup.mem_map.mpr ⟨⟨z, hzS⟩, hzc, rfl⟩
  have hSupLe : Subgroup.zpowers e ⊔ Z ≤ (Subgroup.center ↥S).map S.subtype :=
    sup_le hzp_le hZ_center
  have h9le : 9 ≤ Nat.card (Subgroup.center ↥S) := by
    have := Subgroup.card_le_of_le hSupLe
    rw [hcardSup, Subgroup.card_map_of_injective S.subtype_injective] at this
    exact this
  have hdvd : Nat.card (Subgroup.center ↥S) ∣ 81 := by
    have h := Subgroup.card_dvd_of_le (show Subgroup.center ↥S ≤ ⊤ from le_top)
    rw [Subgroup.card_top, hS_card] at h
    exact h
  have hdvd' : Nat.card (Subgroup.center ↥S) ∣ 3 ^ 4 := by
    simpa using hdvd
  obtain ⟨i, hi_le, hi⟩ := (Nat.dvd_prime_pow Nat.prime_three).mp hdvd' 
  have hi2 : 2 ≤ i := by
    by_contra h
    have h1 : i ≤ 1 := by omega
    have h3 : 3 ^ i ≤ 3 ^ 1 := Nat.pow_le_pow_right (by norm_num) h1
    rw [hi] at h9le
    norm_num at h3 h9le
    omega
  have hne3 : i ≠ 3 := by
    intro h3
    have hcardCent : Nat.card (Subgroup.center ↥S) = 27 := by
      rw [hi, h3]
      norm_num
    have hquot : Nat.card (↥S ⧸ Subgroup.center ↥S) = 3 := by
      have hmul := Subgroup.card_eq_card_quotient_mul_card_subgroup (Subgroup.center ↥S)
      rw [hS_card, hcardCent] at hmul
      norm_num at hmul ⊢
      omega
    haveI : IsCyclic (↥S ⧸ Subgroup.center ↥S) := isCyclic_of_prime_card hquot
    have hab : IsMulCommutative ↥S :=
      isMulCommutative_of_isCyclic_quotient_center_self ↥S
    have htop : Subgroup.center ↥S = ⊤ := Subgroup.center_eq_top_iff.mpr hab
    rw [htop, Subgroup.card_top, hS_card] at hcardCent
    norm_num at hcardCent
  have hne4 : i ≠ 4 := by
    intro h4
    have hcardCent : Nat.card (Subgroup.center ↥S) = 81 := by
      rw [hi, h4]
      norm_num
    have htop : Subgroup.center ↥S = ⊤ :=
      Subgroup.eq_top_of_card_eq _ (by rw [hcardCent]; exact hS_card.symm)
    have hab : IsMulCommutative ↥S := Subgroup.center_eq_top_iff.mp htop
    have hS_ea : CFSG.Open.IsElemAbelian 3 S := ⟨hab, fun x hx => hS_exp x hx⟩
    have hSleM : S ≤ D.M := (inf_le_left.trans inf_le_left).trans hP.le
    have hle := CFSG.SectionRank.le_pRank (p := 3) (by norm_num) hSleM hS_ea
      (by rw [hS_card]; norm_num : Nat.card S = 3 ^ 4)
    rw [c.pRank_three_M] at hle
    norm_num at hle
  have hcenter_card : Nat.card (Subgroup.center ↥S) = 9 := by
    have hi_eq : i = 2 := by omega
    rw [hi, hi_eq]
    norm_num
  exact (Subgroup.eq_of_le_of_card_ge
    (H := Subgroup.zpowers e ⊔ Z)
    (K := (Subgroup.center ↥S).map S.subtype)
    hSupLe (by
      rw [Subgroup.card_map_of_injective S.subtype_injective, hcenter_card, hcardSup])).symm

theorem pl7_exists_E27_wPL7
    (c : Ctx82E3 D) (hON : ThreeCover (fun Y _ => IsSpor Y .ONan) c.Lbar)
    {P : Subgroup G} (hP : CFSG.ABGLocalTools.IsSylowOf 3 P D.M) :
    ∃ E : Subgroup G, E ≤ pl7Q_wPL7 P c ∧ CFSG.Open.IsElemAbelian 3 E ∧ Nat.card E = 27 := by
  classical
  let Q : Subgroup G := pl7Q_wPL7 P c
  have hcard : Nat.card ↥Q = 3 ^ 5 := pl7_card_Q_wPL7 c hON hP
  have hZ : Nat.card (Subgroup.center ↥Q) = 3 := pl7_card_center_Q_wPL7 c hON hP
  have hexp : ∀ x : ↥Q, x ^ 3 = 1 := fun x =>
    Subtype.ext (pl7_exp_Q_wPL7 c hON hP x x.2)
  have hcomm : commutator ↥Q ≤ Subgroup.center ↥Q := by
    change ⁅(⊤ : Subgroup ↥Q), (⊤ : Subgroup ↥Q)⁆ ≤ Subgroup.center ↥Q
    rw [Subgroup.commutator_le]
    intro a ha b hb
    have hamb : ⁅(a : G), (b : G)⁆ ∈ zSub P c.L :=
      pl7_commutator_Q_wPL7 c hON hP (Subgroup.commutator_mem_commutator a.2 b.2)
    rw [show zSub P c.L = (Subgroup.center ↥Q).map Q.subtype from
      (pl7_center_map_eq_wPL7 Q).symm] at hamb
    obtain ⟨z, hz, hzeq⟩ := Subgroup.mem_map.mp hamb
    have hEq : ⁅a, b⁆ = z := by
      apply Subtype.ext
      simpa [commutatorElement_def] using hzeq.symm
    rwa [hEq]
  obtain ⟨E₁, -, -, hE1ea, hE1card, -, -⟩ :=
    CFSG.GroupTheory.ExtraspecialThreeFive.exists_two_elemAbelian_27
      (R := ↥Q) hcard hexp hZ hcomm
  refine ⟨E₁.map Q.subtype, Subgroup.map_subtype_le E₁, hE1ea.map Q.subtype, ?_⟩
  rw [Subgroup.card_map_of_injective Q.subtype_injective, hE1card]

theorem pl7_commute_C0_Q_wPL7 (c : Ctx82E3 D)
    {P : Subgroup G} (hP : CFSG.ABGLocalTools.IsSylowOf 3 P D.M) :
    ∀ x ∈ pl7C0_wPL7 P c, ∀ y ∈ pl7Q_wPL7 P c, x * y = y * x := by
  classical
  intro x hx y hy
  have hcommem : x * y * x⁻¹ * y⁻¹ ∈ CFSG.Open.pCoreOf 2 c.L :=
    (mem_centralizerOnQuotient.mp
      hx.2).2.2.2 y hy.2
  have hcommP : x * y * x⁻¹ * y⁻¹ ∈ P :=
    P.mul_mem (P.mul_mem (P.mul_mem hx.1 hy.1) (P.inv_mem hx.1)) (P.inv_mem hy.1)
  have hO2 : IsPGroup 2 (CFSG.Open.pCoreOf 2 c.L) :=
    CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 c.L
  have hdisj : P ⊓ CFSG.Open.pCoreOf 2 c.L = ⊥ :=
    (IsPGroup.disjoint_of_ne 3 2 (by norm_num) P _ hP.isPGroup hO2).eq_bot
  have hone : x * y * x⁻¹ * y⁻¹ = 1 := by
    have hmem : x * y * x⁻¹ * y⁻¹ ∈ P ⊓ CFSG.Open.pCoreOf 2 c.L :=
      ⟨hcommP, hcommem⟩
    rw [hdisj] at hmem
    exact Subgroup.mem_bot.mp hmem
  calc x * y = (x * y * x⁻¹ * y⁻¹) * (y * x) := by group
    _ = y * x := by rw [hone, one_mul]

theorem pl7_mem_center_lbar_iff_wPL7
    (c : Ctx82E3 D) (hON : ThreeCover (fun Y _ => IsSpor Y .ONan) c.Lbar)
    {P : Subgroup G} (hP : CFSG.ABGLocalTools.IsSylowOf 3 P D.M) {a : G}
    (ha : a ∈ pl7Q_wPL7 P c) :
    QuotientGroup.mk (s := CFSG.Open.pCore 2 ↥c.L) ⟨a, ha.2⟩ ∈ Subgroup.center c.Lbar ↔
      a ∈ zSub P c.L := by
  classical
  letI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  let O : Subgroup ↥c.L := CFSG.Open.pCore 2 ↥c.L
  let π : ↥c.L →* c.Lbar := QuotientGroup.mk' O
  have hPdisjO : P ⊓ CFSG.Open.pCoreOf 2 c.L = ⊥ := by
    have hO2 : IsPGroup 2 (CFSG.Open.pCoreOf 2 c.L) :=
      CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 c.L
    exact (IsPGroup.disjoint_of_ne 3 2 (by norm_num) P _ hP.isPGroup hO2).eq_bot
  have hcomm_mem : ∀ (t : G) (ht : t ∈ pl7Q_wPL7 P c),
      ⁅π ⟨t, ht.2⟩, π ⟨a, ha.2⟩⁆ = 1 → ⁅t, a⁆ = 1 := by
    intro t ht hcomm
    have hPLmem : ⁅t, a⁆ ∈ P ⊓ c.L :=
      ⟨Subgroup.commutator_le_self P (Subgroup.commutator_mem_commutator ht.1 ha.1),
        Subgroup.commutator_le_self c.L (Subgroup.commutator_mem_commutator ht.2 ha.2)⟩
    have hO : (⟨⁅t, a⁆, hPLmem.2⟩ : ↥c.L) ∈ O := by
      rw [← QuotientGroup.eq_one_iff]
      have hsub : (⟨⁅t, a⁆, hPLmem.2⟩ : ↥c.L) =
          ⁅(⟨t, ht.2⟩ : ↥c.L), (⟨a, ha.2⟩ : ↥c.L)⁆ := by
        ext
        rfl
      have hmap : π (⟨⁅t, a⁆, hPLmem.2⟩ : ↥c.L) = 1 := by
        rw [hsub, map_commutatorElement]
        exact hcomm
      simpa [π, O] using hmap
    have hmemO : ⁅t, a⁆ ∈ CFSG.Open.pCoreOf 2 c.L :=
      Subgroup.mem_map.mpr ⟨⟨⁅t, a⁆, hPLmem.2⟩, hO, rfl⟩
    have hbot : ⁅t, a⁆ ∈ (⊥ : Subgroup G) := by
      rw [← hPdisjO]
      exact ⟨hPLmem.1, hmemO⟩
    simpa using hbot
  constructor
  · intro hcenter
    refine ⟨ha, ?_⟩
    refine Subgroup.mem_centralizer_iff.mpr ?_
    intro t ht
    have hcomm_at : ⁅π ⟨a, ha.2⟩, π ⟨t, ht.2⟩⁆ = 1 := by
      rw [commutatorElement_eq_one_iff_commute]
      exact (Subgroup.mem_center_iff.mp hcenter (π ⟨t, ht.2⟩)).symm
    have hcomm : ⁅π ⟨t, ht.2⟩, π ⟨a, ha.2⟩⁆ = 1 :=
      commutatorElement_eq_one_iff_commute.mpr
        ((commutatorElement_eq_one_iff_commute.mp hcomm_at).symm)
    exact commutatorElement_eq_one_iff_commute.mp (hcomm_mem t ht hcomm)
  · intro haZ
    have hzsub : (⟨a, ha.2⟩ : ↥c.L) ∈ (zSub P c.L).subgroupOf c.L :=
      Subgroup.mem_subgroupOf.mpr haZ
    simpa [π, O] using map_zSub_le_center_of_onan c hON hP
      (Subgroup.mem_map.mpr ⟨⟨a, ha.2⟩, hzsub, rfl⟩)

theorem pl7_P_le_sup_wPL7
    (c : Ctx82E3 D) (hON : ThreeCover (fun Y _ => IsSpor Y .ONan) c.Lbar)
    {P : Subgroup G} (hP : CFSG.ABGLocalTools.IsSylowOf 3 P D.M) :
    P ≤ pl7Q_wPL7 P c ⊔ pl7C0_wPL7 P c := by
  classical
  letI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  let φ : ↥D.M →* MulAut c.Lbar :=
    CFSG.GroupTheory.conjModPCore 2 c.L D.M c.le_normalizer_L
  let Psub : Subgroup ↥D.M := P.subgroupOf D.M
  let Qsub : Subgroup ↥D.M := (pl7Q_wPL7 P c).subgroupOf D.M
  let φP : Subgroup (MulAut c.Lbar) := Psub.map φ
  let φQ : Subgroup (MulAut c.Lbar) := Qsub.map φ
  have hPsub3 : IsPGroup 3 Psub := hP.isPGroup.comap_subtype
  have hQsub3 : IsPGroup 3 Qsub := (hP.isPGroup.to_le inf_le_left).comap_subtype
  have hφP3 : IsPGroup 3 φP := hPsub3.map φ
  have hφQ3 : IsPGroup 3 φQ := hQsub3.map φ
  have hHat : CFSG.HardMathSupport.Solomon.LocalBalance.IsHatON c.Lbar :=
    isHatON_lbar_of_onan_wPH2 c hON
  have hφPcard : Nat.card ↥φP ≤ 3 ^ 4 :=
    CFSG.HardMathSupport.Solomon.Coordinator.inputONAut_holds c.Lbar hHat φP hφP3
  have hQsub_card : Nat.card ↥Qsub = 3 ^ 5 := by
    have h1 : Nat.card ↥Qsub = Nat.card ↥(pl7Q_wPL7 P c) :=
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe
        ((inf_le_left : pl7Q_wPL7 P c ≤ P).trans hP.le)).toEquiv
    rw [h1, pl7_card_Q_wPL7 c hON hP]
  have hkerEq : Qsub ⊓ φ.ker = (zSub P c.L).subgroupOf D.M := by
    ext x
    constructor
    · intro hx
      have hxQ : (x : G) ∈ pl7Q_wPL7 P c := Subgroup.mem_subgroupOf.mp hx.1
      have hxφ : φ x = 1 := hx.2
      have hxL : (x : G) ∈ c.L := hxQ.2
      have hconj : MulAut.conj (QuotientGroup.mk (s := CFSG.Open.pCore 2 ↥c.L)
          ⟨(x : G), hxL⟩) = 1 := by
        rw [← CFSG.GroupTheory.conjModPCore_apply_eq_conj_mk 2 c.L D.M
          c.le_normalizer_L x.2 hxL]
        exact hxφ
      have hπcenter : QuotientGroup.mk (s := CFSG.Open.pCore 2 ↥c.L)
          ⟨(x : G), hxL⟩ ∈ Subgroup.center c.Lbar := by
        rw [Subgroup.mem_center_iff]
        intro w
        have hw := congrArg (fun f : MulAut c.Lbar => f w) hconj
        simp only [MulAut.conj_apply, MulAut.one_apply] at hw
        have h2 : QuotientGroup.mk (s := CFSG.Open.pCore 2 ↥c.L) ⟨(x : G), hxL⟩ * w =
            w * QuotientGroup.mk (s := CFSG.Open.pCore 2 ↥c.L) ⟨(x : G), hxL⟩ := by
          calc QuotientGroup.mk (s := CFSG.Open.pCore 2 ↥c.L) ⟨(x : G), hxL⟩ * w =
              (QuotientGroup.mk (s := CFSG.Open.pCore 2 ↥c.L) ⟨(x : G), hxL⟩ * w *
                (QuotientGroup.mk (s := CFSG.Open.pCore 2 ↥c.L) ⟨(x : G), hxL⟩)⁻¹) *
                QuotientGroup.mk (s := CFSG.Open.pCore 2 ↥c.L) ⟨(x : G), hxL⟩ := by group
            _ = w * QuotientGroup.mk (s := CFSG.Open.pCore 2 ↥c.L) ⟨(x : G), hxL⟩ := by rw [hw]
        exact h2.symm
      exact (pl7_mem_center_lbar_iff_wPL7 c hON hP hxQ).mp hπcenter
    · intro hx
      have hxZ : (x : G) ∈ zSub P c.L := Subgroup.mem_subgroupOf.mp hx
      have hxQ : (x : G) ∈ pl7Q_wPL7 P c := (inf_le_left : zSub P c.L ≤ pl7Q_wPL7 P c) hxZ
      refine ⟨Subgroup.mem_subgroupOf.mpr hxQ, ?_⟩
      have hxL : (x : G) ∈ c.L := hxQ.2
      have hzsub : (⟨(x : G), hxL⟩ : ↥c.L) ∈ (zSub P c.L).subgroupOf c.L :=
        Subgroup.mem_subgroupOf.mpr hxZ
      have hπcenter := map_zSub_le_center_of_onan c hON hP
        (Subgroup.mem_map.mpr ⟨⟨(x : G), hxL⟩, hzsub, rfl⟩)
      have hconj : MulAut.conj (QuotientGroup.mk (s := CFSG.Open.pCore 2 ↥c.L)
          ⟨(x : G), hxL⟩) = 1 := by
        ext w
        rw [MulAut.conj_apply, MulAut.one_apply]
        have hcomm : QuotientGroup.mk (s := CFSG.Open.pCore 2 ↥c.L) ⟨(x : G), hxL⟩ * w =
            w * QuotientGroup.mk (s := CFSG.Open.pCore 2 ↥c.L) ⟨(x : G), hxL⟩ :=
          (Subgroup.mem_center_iff.mp hπcenter w).symm
        calc QuotientGroup.mk (s := CFSG.Open.pCore 2 ↥c.L) ⟨(x : G), hxL⟩ * w *
            (QuotientGroup.mk (s := CFSG.Open.pCore 2 ↥c.L) ⟨(x : G), hxL⟩)⁻¹ =
            (w * QuotientGroup.mk (s := CFSG.Open.pCore 2 ↥c.L) ⟨(x : G), hxL⟩) *
              (QuotientGroup.mk (s := CFSG.Open.pCore 2 ↥c.L) ⟨(x : G), hxL⟩)⁻¹ := by
              rw [hcomm]
          _ = w := by group
      change φ x = 1
      rw [CFSG.GroupTheory.conjModPCore_apply_eq_conj_mk 2 c.L D.M
        c.le_normalizer_L x.2 hxL]
      exact hconj
  have hker_card : Nat.card ↥(Qsub ⊓ φ.ker) = 3 := by
    rw [hkerEq]
    have hzle : zSub P c.L ≤ D.M := (inf_le_left.trans inf_le_left).trans hP.le
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hzle).toEquiv]
    exact c.card_inf_centralizer_of_onan hON hP
  have hφQcard : Nat.card ↥φQ = 81 := by
    have h := CFSG.GorensteinWalter.card_map_eq_card_mul_card_ker φ Qsub
    change Nat.card ↥Qsub = Nat.card ↥φQ * Nat.card ↥(Qsub ⊓ φ.ker) at h
    rw [hQsub_card, hker_card] at h
    norm_num at h ⊢
    omega
  have hQsub_le_Psub : Qsub ≤ Psub := by
    intro x hx
    exact Subgroup.mem_subgroupOf.mpr
      ((inf_le_left : pl7Q_wPL7 P c ≤ P) (Subgroup.mem_subgroupOf.mp hx))
  have hφQle : φQ ≤ φP := Subgroup.map_mono hQsub_le_Psub
  have hφQeq : φQ = φP :=
    Subgroup.eq_of_le_of_card_ge hφQle (by rw [hφQcard]; exact hφPcard)
  intro p hp
  have hpM : p ∈ D.M := hP.le hp
  let pm : ↥D.M := ⟨p, hpM⟩
  have hpmP : pm ∈ Psub := Subgroup.mem_subgroupOf.mpr hp
  have hφp_mem : φ pm ∈ φP := Subgroup.mem_map_of_mem φ hpmP
  rw [← hφQeq] at hφp_mem
  obtain ⟨qm, hqm, hφeq⟩ := Subgroup.mem_map.mp hφp_mem
  have hqQ : (qm : G) ∈ pl7Q_wPL7 P c := Subgroup.mem_subgroupOf.mp hqm
  have hker : qm⁻¹ * pm ∈ φ.ker := by
    rw [MonoidHom.mem_ker, map_mul, map_inv, hφeq, inv_mul_cancel]
  have hmapker : (φ.ker).map D.M.subtype = pl7ModCen_wPL7 c :=
    map_ker_conjModPCore_eq_centralizerOnQuotient c
  have hmemC : (qm⁻¹ * pm : ↥D.M).1 ∈ pl7ModCen_wPL7 c := by
    rw [← hmapker]
    exact Subgroup.mem_map.mpr ⟨qm⁻¹ * pm, hker, rfl⟩
  have hmemP : (qm⁻¹ * pm : ↥D.M).1 ∈ P :=
    P.mul_mem (P.inv_mem hqQ.1) hp
  have hC0 : (qm⁻¹ * pm : ↥D.M).1 ∈ pl7C0_wPL7 P c := ⟨hmemP, hmemC⟩
  have hpeq : p = (qm : G) * (qm⁻¹ * pm : ↥D.M).1 := by
    simp [pm]
  rw [hpeq]
  exact Subgroup.mul_mem_sup hqQ hC0

theorem pl7_phi_eq_one_of_mem_C0_wPL7
    (c : Ctx82E3 D) (hON : ThreeCover (fun Y _ => IsSpor Y .ONan) c.Lbar)
    {P : Subgroup G} (hP : CFSG.ABGLocalTools.IsSylowOf 3 P D.M) {z : G}
    (hz : z ∈ pl7C0_wPL7 P c) :
    CFSG.GroupTheory.conjModPCore 2 c.L D.M c.le_normalizer_L
      ⟨z, hP.le hz.1⟩ = 1 := by
  let φ : ↥D.M →* MulAut c.Lbar :=
    CFSG.GroupTheory.conjModPCore 2 c.L D.M c.le_normalizer_L
  have hmapker : (φ.ker).map D.M.subtype = pl7ModCen_wPL7 c :=
    map_ker_conjModPCore_eq_centralizerOnQuotient c
  have hzmod : z ∈ (φ.ker).map D.M.subtype := by
    rw [hmapker]
    exact hz.2
  obtain ⟨zm, hzm, hzmval⟩ := Subgroup.mem_map.mp hzmod
  have hzm1 : φ zm = 1 := MonoidHom.mem_ker.mp hzm
  have hsub : (⟨z, hP.le hz.1⟩ : ↥D.M) = zm := Subtype.ext hzmval.symm
  rwa [hsub]

theorem pl7_zSub_le_C0_wPL7
    (c : Ctx82E3 D) (hON : ThreeCover (fun Y _ => IsSpor Y .ONan) c.Lbar)
    {P : Subgroup G} (hP : CFSG.ABGLocalTools.IsSylowOf 3 P D.M) :
    zSub P c.L ≤ pl7C0_wPL7 P c := by
  classical
  letI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  let φ : ↥D.M →* MulAut c.Lbar :=
    CFSG.GroupTheory.conjModPCore 2 c.L D.M c.le_normalizer_L
  intro z hz
  have hzQ : z ∈ pl7Q_wPL7 P c := (inf_le_left : zSub P c.L ≤ pl7Q_wPL7 P c) hz
  have hzL : z ∈ c.L := hzQ.2
  have hzM : z ∈ D.M := hP.le hzQ.1
  have hzcenter : QuotientGroup.mk (s := CFSG.Open.pCore 2 ↥c.L) ⟨z, hzL⟩ ∈
      Subgroup.center c.Lbar := by
    have hzsub : (⟨z, hzL⟩ : ↥c.L) ∈ (zSub P c.L).subgroupOf c.L :=
      Subgroup.mem_subgroupOf.mpr hz
    simpa using map_zSub_le_center_of_onan c hON hP
      (Subgroup.mem_map.mpr ⟨⟨z, hzL⟩, hzsub, rfl⟩)
  have hzker : φ ⟨z, hzM⟩ = 1 := by
    rw [CFSG.GroupTheory.conjModPCore_apply_eq_conj_mk 2 c.L D.M
      c.le_normalizer_L hzM hzL]
    ext w
    rw [MulAut.conj_apply, MulAut.one_apply]
    have hcomm : QuotientGroup.mk (s := CFSG.Open.pCore 2 ↥c.L) ⟨z, hzL⟩ * w =
        w * QuotientGroup.mk (s := CFSG.Open.pCore 2 ↥c.L) ⟨z, hzL⟩ :=
      (Subgroup.mem_center_iff.mp hzcenter w).symm
    calc QuotientGroup.mk (s := CFSG.Open.pCore 2 ↥c.L) ⟨z, hzL⟩ * w *
        (QuotientGroup.mk (s := CFSG.Open.pCore 2 ↥c.L) ⟨z, hzL⟩)⁻¹ =
        (w * QuotientGroup.mk (s := CFSG.Open.pCore 2 ↥c.L) ⟨z, hzL⟩) *
          (QuotientGroup.mk (s := CFSG.Open.pCore 2 ↥c.L) ⟨z, hzL⟩)⁻¹ := by rw [hcomm]
      _ = w := by group
  have hmod : z ∈ pl7ModCen_wPL7 c := by
    have hmapker : (φ.ker).map D.M.subtype = pl7ModCen_wPL7 c :=
      map_ker_conjModPCore_eq_centralizerOnQuotient c
    rw [← hmapker]
    exact Subgroup.mem_map.mpr ⟨⟨z, hzM⟩, MonoidHom.mem_ker.mpr hzker, rfl⟩
  exact ⟨hzQ.1, hmod⟩

theorem pl7_cyclic_C0_wPL7
    (c : Ctx82E3 D) (hON : ThreeCover (fun Y _ => IsSpor Y .ONan) c.Lbar)
    {P : Subgroup G} (hP : CFSG.ABGLocalTools.IsSylowOf 3 P D.M) :
    IsCyclic ↥(pl7C0_wPL7 P c) := by
  classical
  letI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  let C0 : Subgroup G := pl7C0_wPL7 P c
  have hC0p : IsPGroup 3 C0 := hP.isPGroup.to_le inf_le_left
  have hrank : CFSG.Open.pRank 3 C0 ≤ 1 := by
    by_contra h
    have h2 : 2 ≤ CFSG.Open.pRank 3 C0 := by omega
    obtain ⟨E, hEC0, hEea, hEcard⟩ :=
      CFSG.SectionRank.exists_pRank (p := 3) (by norm_num) C0
    have hE9 : 9 ≤ Nat.card E := by
      rw [hEcard]
      have := Nat.pow_le_pow_right (by norm_num : (0:ℕ) < 3) h2
      norm_num at this
      exact this
    obtain ⟨Q0, hQ0Q, hQ0ea, hQ0card⟩ := pl7_exists_E27_wPL7 c hON hP
    have hcomm : ∀ e ∈ E, ∀ q ∈ Q0, e * q = q * e :=
      fun e he q hq => pl7_commute_C0_Q_wPL7 c hP e (hEC0 he) q (hQ0Q hq)
    have hFp : IsPGroup 3 (E ⊔ Q0 : Subgroup G) := hP.isPGroup.to_le
      (sup_le (hEC0.trans inf_le_left) (hQ0Q.trans inf_le_left))
    have hFea : CFSG.Open.IsElemAbelian 3 (E ⊔ Q0 : Subgroup G) :=
      hEea.sup_of_commute hQ0ea hcomm
    have hnorm : E ≤ Subgroup.normalizer (Q0 : Set G) := by
      rw [Subgroup.le_normalizer_iff]
      intro e he q hq
      rw [show e * q * e⁻¹ = q by rw [hcomm e he q hq]; group]
      exact hq
    have hprod :=
      CFSG.GroupTheory.CoprimeActionSupport.NormalSubgroupSylowJoin.card_sup_mul_card_inf
        (H := E) (K := Q0) hnorm
    have hinf_le : Nat.card (E ⊓ Q0 : Subgroup G) ≤ 3 := by
      have hle : E ⊓ Q0 ≤ zSub P c.L := by
        intro z hz
        refine ⟨hQ0Q hz.2, Subgroup.mem_centralizer_iff.mpr ?_⟩
        intro y hy
        exact (pl7_commute_C0_Q_wPL7 c hP z (hEC0 hz.1) y hy).symm
      have hzcard : Nat.card (zSub P c.L) = 3 := c.card_inf_centralizer_of_onan hON hP
      exact (Subgroup.card_le_of_le hle).trans (le_of_eq hzcard)
    have h81 : 81 ≤ Nat.card (E ⊔ Q0 : Subgroup G) := by
      have hmul : 243 ≤ Nat.card E * Nat.card Q0 := by
        have := Nat.mul_le_mul hE9 (le_of_eq hQ0card.symm)
        norm_num at this ⊢
        omega
      have hmul2 : Nat.card (E ⊔ Q0 : Subgroup G) *
          Nat.card (E ⊓ Q0 : Subgroup G) = Nat.card E * Nat.card Q0 := hprod
      have hle3 : Nat.card (E ⊔ Q0 : Subgroup G) * Nat.card (E ⊓ Q0 : Subgroup G) ≤
          Nat.card (E ⊔ Q0 : Subgroup G) * 3 := Nat.mul_le_mul_left _ hinf_le
      omega
    obtain ⟨k, hk⟩ := (IsPGroup.iff_card).mp hFp
    have hk4 : 4 ≤ k := by
      by_contra hknot
      have hk3 : k ≤ 3 := by omega
      have h3k : 3 ^ k ≤ 3 ^ 3 := Nat.pow_le_pow_right (by norm_num) hk3
      rw [hk] at h81
      norm_num at h3k h81
      omega
    have hFleM : (E ⊔ Q0 : Subgroup G) ≤ D.M :=
      (sup_le (hEC0.trans inf_le_left) (hQ0Q.trans inf_le_left)).trans hP.le
    have hle := CFSG.SectionRank.le_pRank (p := 3) (by norm_num) hFleM hFea hk
    rw [c.pRank_three_M] at hle
    omega
  exact CFSG.isCyclic_of_le_of_pRank_le_one Nat.prime_three (by norm_num)
    hC0p le_rfl hrank

theorem pl7_T_eq_wPL7
    (c : Ctx82E3 D) (hON : ThreeCover (fun Y _ => IsSpor Y .ONan) c.Lbar)
    {P : Subgroup G} (hP : CFSG.ABGLocalTools.IsSylowOf 3 P D.M) {e : G}
    (he : e ∈ pl7Q_wPL7 P c) :
    pl7T_wPL7 P e = (pl7Q_wPL7 P c ⊓ Subgroup.centralizer ({e} : Set G)) ⊔ pl7C0_wPL7 P c := by
  classical
  apply le_antisymm
  · intro p hp
    have hpP : p ∈ P := hp.1
    have hpC : p ∈ Subgroup.centralizer ({e} : Set G) := hp.2
    have hPsup : p ∈ pl7Q_wPL7 P c ⊔ pl7C0_wPL7 P c := pl7_P_le_sup_wPL7 c hON hP hpP
    have hcommQC : ∀ a ∈ pl7Q_wPL7 P c, ∀ b ∈ pl7C0_wPL7 P c, a * b = b * a :=
      fun a ha b hb => (pl7_commute_C0_Q_wPL7 c hP b hb a ha).symm
    obtain ⟨q, hqQ, c0, hc0C, hqc⟩ := CFSG.mem_sup_of_commute
      (A := pl7Q_wPL7 P c) (B := pl7C0_wPL7 P c)
      (fun a ha b hb => hcommQC a ha b hb) |>.1 hPsup
    have hpec : p * e = e * p := Subgroup.mem_centralizer_singleton_iff.mp hpC
    have hc0e : Commute c0 e := pl7_commute_C0_Q_wPL7 c hP c0 hc0C e he
    have hqe : q * e = e * q := by
      have hqeq : q = p * c0⁻¹ := by rw [← hqc]; group
      rw [hqeq]
      calc p * c0⁻¹ * e = p * (c0⁻¹ * e) := by group
        _ = p * (e * c0⁻¹) := by rw [hc0e.inv_left.eq]
        _ = (p * e) * c0⁻¹ := by group
        _ = (e * p) * c0⁻¹ := by rw [hpec]
        _ = e * (p * c0⁻¹) := by group
    have hqcent : q ∈ Subgroup.centralizer ({e} : Set G) :=
      Subgroup.mem_centralizer_singleton_iff.mpr hqe
    rw [← hqc]
    exact Subgroup.mul_mem_sup ⟨hqQ, hqcent⟩ hc0C
  · refine sup_le ?_ ?_
    · intro x hx
      exact ⟨(inf_le_left : pl7Q_wPL7 P c ≤ P) hx.1, hx.2⟩
    · intro x hx
      refine ⟨hx.1, ?_⟩
      exact Subgroup.mem_centralizer_singleton_iff.mpr
        (pl7_commute_C0_Q_wPL7 c hP x hx e he)

theorem threeCoreFrame_of_onan''
    (hK2 : K2ONanCentralizer) (c : Ctx82E3 D)
    (hON : ThreeCover (fun Y _ => IsSpor Y .ONan) c.Lbar)
    {P : Subgroup G} (hP : CFSG.ABGLocalTools.IsSylowOf 3 P D.M)
    {e : G} (he : e ∈ P ⊓ c.L) (he3 : orderOf e = 3) (heZ : e ∉ zSub P c.L) :
    ThreeCoreFrame' (P ⊓ Subgroup.centralizer ({e} : Set G)) (zSub P c.L) e := by
  classical
  letI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  let Q : Subgroup G := pl7Q_wPL7 P c
  let C0 : Subgroup G := pl7C0_wPL7 P c
  let Z : Subgroup G := zSub P c.L
  let T : Subgroup G := pl7T_wPL7 P e
  let S : Subgroup G := Q ⊓ Subgroup.centralizer ({e} : Set G)
  let φ : ↥D.M →* MulAut c.Lbar :=
    CFSG.GroupTheory.conjModPCore 2 c.L D.M c.le_normalizer_L
  have hP_eq : P = Q ⊔ C0 := le_antisymm (pl7_P_le_sup_wPL7 c hON hP)
    (sup_le inf_le_left inf_le_left)
  have hT_eq : T = S ⊔ C0 := pl7_T_eq_wPL7 c hON hP he
  have hcommQC : ∀ a ∈ Q, ∀ b ∈ C0, a * b = b * a :=
    fun a ha b hb => (pl7_commute_C0_Q_wPL7 c hP b hb a ha).symm
  constructor
  ·
    have hTT_C0 : ⁅T, T⁆ ≤ C0 := by
      rw [Subgroup.commutator_le]
      intro x hxT y hyT
      have hxP : x ∈ P := hxT.1
      have hyP : y ∈ P := hyT.1
      obtain ⟨q1, hq1, c1, hc1, hdec1⟩ := (CFSG.mem_sup_of_commute
        (A := Q) (B := C0) (fun a ha b hb => hcommQC a ha b hb)).mp
        (pl7_P_le_sup_wPL7 c hON hP hxP)
      obtain ⟨q2, hq2, c2, hc2, hdec2⟩ := (CFSG.mem_sup_of_commute
        (A := Q) (B := C0) (fun a ha b hb => hcommQC a ha b hb)).mp
        (pl7_P_le_sup_wPL7 c hON hP hyP)
      have hc1ker : φ ⟨c1, hP.le hc1.1⟩ = 1 :=
        pl7_phi_eq_one_of_mem_C0_wPL7 c hON hP hc1
      have hc2ker : φ ⟨c2, hP.le hc2.1⟩ = 1 :=
        pl7_phi_eq_one_of_mem_C0_wPL7 c hON hP hc2
      have hφx : φ ⟨x, hP.le hxP⟩ = φ ⟨q1, hP.le hq1.1⟩ := by
        have hxsub : (⟨x, hP.le hxP⟩ : ↥D.M) =
            ⟨q1, hP.le hq1.1⟩ * ⟨c1, hP.le hc1.1⟩ := by
          apply Subtype.ext
          simpa using hdec1.symm
        rw [hxsub, map_mul, hc1ker, mul_one]
      have hφy : φ ⟨y, hP.le hyP⟩ = φ ⟨q2, hP.le hq2.1⟩ := by
        have hysub : (⟨y, hP.le hyP⟩ : ↥D.M) =
            ⟨q2, hP.le hq2.1⟩ * ⟨c2, hP.le hc2.1⟩ := by
          apply Subtype.ext
          simpa using hdec2.symm
        rw [hysub, map_mul, hc2ker, mul_one]
      have hxyP : ⁅x, y⁆ ∈ P :=
        Subgroup.commutator_le_self P (Subgroup.commutator_mem_commutator hxP hyP)
      have hq12Z : ⁅q1, q2⁆ ∈ Z :=
        pl7_commutator_Q_wPL7 c hON hP (Subgroup.commutator_mem_commutator hq1 hq2)
      have hq12C0 : ⁅q1, q2⁆ ∈ C0 := pl7_zSub_le_C0_wPL7 c hON hP hq12Z
      have hφq12 : φ ⟨⁅q1, q2⁆, hP.le hq12C0.1⟩ = 1 :=
        pl7_phi_eq_one_of_mem_C0_wPL7 c hON hP hq12C0
      have hφq12' : φ (⁅(⟨q1, hP.le hq1.1⟩ : ↥D.M),
          (⟨q2, hP.le hq2.1⟩ : ↥D.M)⁆) = 1 := by
        change φ ⟨⁅q1, q2⁆, hP.le hq12C0.1⟩ = 1
        exact hφq12
      have hφcomm : φ ⟨⁅x, y⁆, hP.le hxyP⟩ = 1 := by
        change φ (⁅(⟨x, hP.le hxP⟩ : ↥D.M),
          (⟨y, hP.le hyP⟩ : ↥D.M)⁆) = 1
        rw [map_commutatorElement, hφx, hφy, ← map_commutatorElement]
        exact hφq12'
      have hmapker : (φ.ker).map D.M.subtype = pl7ModCen_wPL7 c :=
        map_ker_conjModPCore_eq_centralizerOnQuotient c
      have hmemC : ⁅x, y⁆ ∈ pl7ModCen_wPL7 c := by
        rw [← hmapker]
        exact Subgroup.mem_map.mpr ⟨⟨⁅x, y⁆, hP.le hxyP⟩,
          MonoidHom.mem_ker.mpr hφcomm, rfl⟩
      exact ⟨hxyP, hmemC⟩
    have hPP_Q : ⁅P, P⁆ ≤ Q := by
      let QP : Subgroup ↥P := Q.subgroupOf P
      let C0P : Subgroup ↥P := C0.subgroupOf P
      have hQPnorm : QP.Normal := by
        refine ⟨fun q hq p => ?_⟩
        have hqQ : (q : G) ∈ Q := Subgroup.mem_subgroupOf.mp hq
        have hpP : (p : G) ∈ P := p.2
        have hpL : (p : G) ∈ Subgroup.normalizer (c.L : Set G) := c.le_normalizer_L (hP.le hpP)
        refine Subgroup.mem_subgroupOf.mpr ⟨?_, ?_⟩
        · exact P.mul_mem (P.mul_mem hpP hqQ.1) (P.inv_mem hpP)
        · exact (Subgroup.mem_normalizer_iff.mp hpL _).1 hqQ.2
      haveI := hQPnorm
      have hsup : QP ⊔ C0P = ⊤ := by
        apply le_antisymm le_top
        intro x hx
        have hx : (x : G) ∈ Q ⊔ C0 := by
          rw [← hP_eq]
          exact x.2
        obtain ⟨q, hq, c, hc, hqc⟩ := (CFSG.mem_sup_of_commute
          (A := Q) (B := C0) (fun a ha b hb => hcommQC a ha b hb)).mp hx
        have hqP : q ∈ P := (inf_le_left : Q ≤ P) hq
        have hcP : c ∈ P := (inf_le_left : C0 ≤ P) hc
        have hxeq : x = ⟨q, hqP⟩ * ⟨c, hcP⟩ := Subtype.ext hqc.symm
        rw [hxeq]
        exact Subgroup.mul_mem_sup (Subgroup.mem_subgroupOf.mpr hq)
          (Subgroup.mem_subgroupOf.mpr hc)
      have hC0Pcyc : IsCyclic ↥C0P := by
        haveI : IsCyclic ↥C0 := pl7_cyclic_C0_wPL7 c hON hP
        exact (MulEquiv.isCyclic (Subgroup.subgroupOfEquivOfLe
          (show C0 ≤ P from inf_le_left))).mpr ‹IsCyclic ↥C0›
      haveI : IsCyclic (↥P ⧸ QP) :=
        CFSG.quotient_isCyclic_of_sup_cyclic_right hsup hC0Pcyc
      have hcommquot : IsMulCommutative (↥P ⧸ QP) := inferInstance
      have hPPsub : commutator ↥P ≤ QP :=
        Subgroup.Normal.quotient_commutative_iff_commutator_le.mp hcommquot
      rw [Subgroup.commutator_le]
      intro p1 hp1 p2 hp2
      have hcommP : ⁅p1, p2⁆ ∈ P :=
        Subgroup.commutator_le_self P
          (Subgroup.commutator_mem_commutator hp1 hp2)
      have hsub : (⟨⁅p1, p2⁆, hcommP⟩ : ↥P) =
          ⁅(⟨p1, hp1⟩ : ↥P), (⟨p2, hp2⟩ : ↥P)⁆ := by
        ext
        simp [commutatorElement_def]
      have hmem : (⟨⁅p1, p2⁆, hcommP⟩ : ↥P) ∈ commutator ↥P := by
        rw [hsub]
        exact Subgroup.commutator_mem_commutator (Subgroup.mem_top _) (Subgroup.mem_top _)
      exact Subgroup.mem_subgroupOf.mp (hPPsub hmem)
    have hTT_Q : ⁅T, T⁆ ≤ Q :=
      (Subgroup.commutator_mono (show T ≤ P from inf_le_left)
        (show T ≤ P from inf_le_left)).trans hPP_Q
    rw [Subgroup.commutator_le]
    intro x hxT y hyT
    have hxyQ : ⁅x, y⁆ ∈ Q :=
      hTT_Q (Subgroup.commutator_mem_commutator hxT hyT)
    have hxyC0 : ⁅x, y⁆ ∈ C0 :=
      hTT_C0 (Subgroup.commutator_mem_commutator hxT hyT)
    refine ⟨hxyQ, Subgroup.mem_centralizer_iff.mpr ?_⟩
    intro t ht
    exact (pl7_commute_C0_Q_wPL7 c hP ⁅x, y⁆ hxyC0 t ht).symm
  ·
    refine ⟨C0, ?_, ?_⟩
    · intro x hxTC
      have hxT : x ∈ T := hxTC.1
      have heT : e ∈ T := ⟨he.1, Subgroup.mem_centralizer_singleton_iff.mpr (by group)⟩
      have hxC : x ∈ Subgroup.centralizer ({e} : Set G) :=
        Subgroup.mem_centralizer_singleton_iff.mpr
          (Subgroup.mem_centralizer_iff.mp hxTC.2 e heT).symm
      have hxSsup : x ∈ S ⊔ C0 := by
        rw [hT_eq] at hxT
        exact hxT
      have hcommSC : ∀ a ∈ S, ∀ b ∈ C0, a * b = b * a :=
        fun a ha b hb => (pl7_commute_C0_Q_wPL7 c hP b hb a ha.1).symm
      obtain ⟨q, hqS, c0, hc0C, hqc⟩ := (CFSG.mem_sup_of_commute
        (A := S) (B := C0) (fun a ha b hb => hcommSC a ha b hb)).mp hxSsup
      have hqcentS : (⟨q, hqS⟩ : ↥S) ∈ Subgroup.center ↥S := by
        rw [Subgroup.mem_center_iff]
        intro y
        apply Subtype.ext
        have hyT : (y : G) ∈ T := by
          rw [hT_eq]
          exact Subgroup.mem_sup_left y.2
        have hxy : (y : G) * x = x * (y : G) :=
          Subgroup.mem_centralizer_iff.mp hxTC.2 (y : G) hyT
        have hcy : c0 * (y : G) = (y : G) * c0 :=
          pl7_commute_C0_Q_wPL7 c hP c0 hc0C (y : G) y.2.1
        have hEq : ((y : G) * q) * c0 = (q * (y : G)) * c0 := by
          calc ((y : G) * q) * c0 = (y : G) * (q * c0) := by group
            _ = (y : G) * x := by rw [hqc]
            _ = x * (y : G) := hxy
            _ = (q * c0) * (y : G) := by rw [← hqc]
            _ = q * (c0 * (y : G)) := by group
            _ = q * ((y : G) * c0) := by rw [hcy]
            _ = (q * (y : G)) * c0 := by group
        exact mul_right_cancel hEq
      have hq_map : q ∈ (Subgroup.center ↥S).map S.subtype :=
        Subgroup.mem_map.mpr ⟨⟨q, hqS⟩, hqcentS, rfl⟩
      rw [pl7_center_centralizer_Q_wPL7 c hON hP he he3 heZ] at hq_map
      have hcommEZ : ∀ a ∈ Subgroup.zpowers e, ∀ b ∈ Z, a * b = b * a := by
        intro a ha b hb
        obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp ha
        have hbe : Commute e b := Subgroup.mem_centralizer_iff.mp hb.2 e he
        exact (hbe.zpow_left k).eq
      obtain ⟨a, ha, z, hzZ, hqeq⟩ := (CFSG.mem_sup_of_commute
        (A := Subgroup.zpowers e) (B := Z)
        (fun a ha b hb => hcommEZ a ha b hb)).mp hq_map
      obtain ⟨i, hi_eq⟩ := Subgroup.mem_zpowers_iff.mp ha
      have hzC0 : z ∈ C0 := pl7_zSub_le_C0_wPL7 c hON hP hzZ
      refine ⟨i, z * c0, C0.mul_mem hzC0 hc0C, ?_⟩
      calc e ^ i * (z * c0) = (a * z) * c0 := by rw [hi_eq]; group
        _ = q * c0 := by rw [hqeq]
        _ = x := hqc
    · intro c0 hc0C hc03
      have hc0Q : c0 ∈ Q := by
        have hc0L : c0 ∈ c.L :=
          c.forall_pow_three_eq_one_mem_L_of_threeCover
            CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82.k3Exp_holds
            (CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82.k3Out_holds c.Lbar hON)
            hON hP c0 hc0C.1 hc03
        exact ⟨hc0C.1, hc0L⟩
      refine ⟨hc0Q, Subgroup.mem_centralizer_iff.mpr ?_⟩
      intro t ht
      exact (pl7_commute_C0_Q_wPL7 c hP c0 hc0C t ht).symm

theorem pcore_centralizer_le_theta_threeCore''
    (hK2 : K2ONanCentralizer) (c : Ctx82E3 D)
    (hON : ThreeCover (fun Y _ => IsSpor Y .ONan) c.Lbar) (h7 : D.sig = {7})
    {P : Subgroup G} (hP : CFSG.ABGLocalTools.IsSylowOf 3 P D.M)
    (hNZ : Subgroup.normalizer ((zSub P c.L : Subgroup G) : Set G) ≤ D.M)
    {e : G} (hP1 : CFSG.ABGLocalTools.IsSylowOf 3
      (P ⊓ Subgroup.centralizer ({e} : Set G)) (Subgroup.centralizer ({e} : Set G)))
    (he : e ∈ P ⊓ c.L) (he3 : orderOf e = 3) (heZ : e ∉ zSub P c.L) :
    ((Subgroup.centralizer ({e} : Set G) ⊓ CFSG.Open.pCoreOf 2 D.M).subgroupOf
        (Subgroup.centralizer ({e} : Set G))).map
        (QuotientGroup.mk' (CFSG.RankThree.LocalRank.aschbacherSolvableCore 3
          ↥(Subgroup.centralizer ({e} : Set G)))) ≤
      Subgroup.centralizer
        ((CFSG.pCore 3 (↥(Subgroup.centralizer ({e} : Set G)) ⧸
          CFSG.RankThree.LocalRank.aschbacherSolvableCore 3
            ↥(Subgroup.centralizer ({e} : Set G))) : Subgroup _) : Set _) :=
  pcore_centralizer_le_theta_threeCore_of_frame' hK2 c hON h7 hP hNZ hP1 he he3 heZ
    (weaklyClosed_zSub_of_onan_cover' c hON h7 hP hNZ)
    (threeCoreFrame_of_onan'' hK2 c hON hP he he3 heZ)

end
end CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82E3.ONan
