module

public import CFSG.GroupTheory.MulAutCongr
public import CFSG.RankThree.PartTwo.Sec14.Item14Res4ProofL34
public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82E3.ONanS6.WPC4

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82E3.ONan
section
open CFSG.Open
open CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo.Sec4
open CFSG.ComponentClassification.PerfectAutomorphisms (centerQuotientHom)
open CFSG.ComponentClassification.PerfectAutomorphisms (centerQuotientHom_injective)
open CFSG.ComponentClassification.PerfectAutomorphisms (onCenterQuotient_apply_mk)
open CFSG.LocalAnalysis.UniquenessCase.UC22 (Data IsSpor)
open scoped commutatorElement
variable {G : Type} [Group G] [Finite G]
variable {D : Data G}

theorem eq_Lz_of_card_autThetaQuot_eq_nine
    (c : Ctx82E3 D)
    (hON : UCK.ThreeCover (fun Y _ => IsSpor Y .ONan) c.Lbar)
    {P A : Subgroup G} (hP : CFSG.ABGLocalTools.IsSylowOf 3 P D.M)
    (hA : CFSG.Open.IsElemAbelian 3 A) (hZA : zSub P c.L ≤ A)
    (hAPL : A ≤ P ⊓ c.L) {x : G} (hx : x ∈ zSub P c.L) (hx1 : x ≠ 1)
    (hC : Subgroup.centralizer ({x} : Set G) ≤ D.M)
    {L : Subgroup G} (hL : L ∈ thetaComponentsAt 3 x)
    (h9 : Nat.card (autThetaQuot A L) = 9) :
    L = Lz c x := by
  classical
  by_contra hne
  have hLC : L ≤ Cbar c :=
    thetaComponent_le_C_of_ne_Lz_core' c hON hP hA hZA hx hx1 hC hL hne
  have hLW : L ≤ Subgroup.centralizer ({x} : Set G) :=
    CFSG.RankThree.PartTwo.Sec6.le_centralizer_of_mem_thetaComponentsAt hL
  have hLM : L ≤ D.M := hLW.trans hC
  have hAN : A ≤ Subgroup.normalizer (L : Set G) :=
    normalizes_of_le_C''' c hON hP hA hZA hAPL hx hx1 hC hL hLC
  have hAL : A ≤ c.L := hAPL.trans inf_le_right
  have hcommL : ⁅c.L, L⁆ ≤ CFSG.Open.pCoreOf 2 c.L :=
    (CFSG.GroupTheory.le_map_ker_conjModPCore_iff_commutator 2 c.L D.M L
      c.le_normalizer_L hLM).mp hLC
  have hLA : ⁅L, A⁆ ≤ CFSG.Open.pCoreOf 2 c.L := by
    rw [Subgroup.commutator_comm]
    exact (Subgroup.commutator_mono hAL le_rfl).trans hcommL
  have hLAN : ⁅L, A⁆ ≤ L := Subgroup.le_normalizer_iff_commutator_le_left.mp hAN
  have hLAinf : ⁅L, A⁆ ≤ L ⊓ CFSG.Open.pCoreOf 2 c.L := le_inf hLAN hLA
  have hLNcL : L ≤ Subgroup.normalizer (c.L : Set G) := hLM.trans c.le_normalizer_L
  have hLNp : L ≤ Subgroup.normalizer (CFSG.Open.pCoreOf 2 c.L : Set G) :=
    normalizer_pCoreOf_le hLNcL
  have hnorm : ((L ⊓ CFSG.Open.pCoreOf 2 c.L).subgroupOf L).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer inf_le_left).mpr
      (CFSG.RankThree.PartOne.le_normalizer_inf_of_le_normalizer
        Subgroup.le_normalizer hLNp)
  have hQ2 : IsPGroup 2 ↥(L ⊓ CFSG.Open.pCoreOf 2 c.L) :=
    (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 c.L).to_le inf_le_right
  have hQ2' : IsPGroup 2 ↥((L ⊓ CFSG.Open.pCoreOf 2 c.L).subgroupOf L) := by
    obtain ⟨n, hn⟩ := hQ2.exists_card_eq
    rw [IsPGroup.iff_card]
    exact ⟨n, (Nat.card_congr (Subgroup.subgroupOfEquivOfLe inf_le_left).toEquiv).trans hn⟩
  have hQsolv : Group.IsSolvable ↥((L ⊓ CFSG.Open.pCoreOf 2 c.L).subgroupOf L) :=
    @IsNilpotent.to_isSolvable _ _ hQ2'.isNilpotent
  have hQ3 : ¬ 3 ∣ Nat.card ↥((L ⊓ CFSG.Open.pCoreOf 2 c.L).subgroupOf L) := by
    obtain ⟨n, hn⟩ := hQ2'.exists_card_eq
    intro h
    rw [hn] at h
    exact absurd (Nat.prime_three.dvd_of_dvd_pow h) (by norm_num)
  have hle_theta : ⁅L, A⁆ ≤ inSubgroup (aschbacherSolvableCore 3) L := by
    have hmax := (solvable_prime_complement_core_characterization (H := ↥L)
      (p := 3) Nat.prime_three).2.2.2.1
    have hsub : (L ⊓ CFSG.Open.pCoreOf 2 c.L).subgroupOf L ≤
        aschbacherSolvableCore 3 ↥L := hmax _ hnorm hQsolv hQ3
    calc ⁅L, A⁆ ≤ L ⊓ CFSG.Open.pCoreOf 2 c.L := hLAinf
      _ = Subgroup.map L.subtype ((L ⊓ CFSG.Open.pCoreOf 2 c.L).subgroupOf L) :=
          (Subgroup.map_subgroupOf_eq_of_le inf_le_left).symm
      _ ≤ Subgroup.map L.subtype (aschbacherSolvableCore 3 ↥L) := Subgroup.map_mono hsub
      _ = inSubgroup (aschbacherSolvableCore 3) L := rfl
  have hcentral : A ≤ thetaQuotCentralizer L := by
    intro a ha
    refine (CFSG.RankThree.PartTwo.Sec14.Res4L34.mem_thetaQuotCentralizer_iff'
      (L := L) (hAN ha)).mpr (fun l hl => ?_)
    have h := Subgroup.commutator_le.mp hle_theta l hl a ha
    have h2 : (a * l * a⁻¹ * l⁻¹) = ⁅l, a⁆⁻¹ := by
      rw [commutatorElement_def, mul_inv_rev, mul_inv_rev, inv_inv, inv_inv]
      group
    rw [h2]
    exact (inSubgroup (aschbacherSolvableCore 3) L).inv_mem h
  have hbot : autThetaQuot A L = ⊥ := by
    rw [eq_bot_iff]
    intro τ hτ
    rw [mem_autThetaQuot_iff] at hτ
    obtain ⟨a, hN, haA, rfl⟩ := hτ
    obtain ⟨n, hn, hna⟩ := hcentral haA
    have hsub : n = (⟨a, hN⟩ : Subgroup.normalizer (L : Set G)) := Subtype.ext hna
    rw [← hsub]
    exact hn
  rw [hbot, Subgroup.card_bot] at h9
  exact absurd h9 (by norm_num)

@[expose] noncomputable def LzToLbar (c : Ctx82E3 D) (x : G) : ↥(Lz c x) →* c.Lbar :=
  (QuotientGroup.mk' (CFSG.Open.pCore 2 ↥c.L)).comp
    (Subgroup.inclusion ((Subgroup.map_subtype_le _).trans inf_le_left))

theorem LzToLbar_surjective
    (c : Ctx82E3 D)
    (hON : UCK.ThreeCover (fun Y _ => IsSpor Y .ONan) c.Lbar)
    {P A : Subgroup G} (hP : CFSG.ABGLocalTools.IsSylowOf 3 P D.M)
    (hA : CFSG.Open.IsElemAbelian 3 A) (hZA : zSub P c.L ≤ A)
    {x : G} (hx : x ∈ zSub P c.L) (hx1 : x ≠ 1)
    (hC : Subgroup.centralizer ({x} : Set G) ≤ D.M) :
    Function.Surjective (LzToLbar c x) := by
  intro y
  have htop := Lz_image_eq_top c hON hP hA hZA hx hx1 hC
  have hy : y ∈ ((Lz c x).subgroupOf c.L).map
      (QuotientGroup.mk' (CFSG.Open.pCore 2 ↥c.L)) := by
    rw [htop]
    exact Subgroup.mem_top y
  obtain ⟨z, hz, hzy⟩ := Subgroup.mem_map.mp hy
  refine ⟨⟨(z : G), Subgroup.mem_subgroupOf.mp hz⟩, ?_⟩
  exact hzy

theorem LzToLbar_ker (c : Ctx82E3 D) (x : G) :
    (LzToLbar c x).ker = ((Lz c x) ⊓ CFSG.Open.pCoreOf 2 c.L).subgroupOf (Lz c x) := by
  have hLscL : Lz c x ≤ c.L := (Subgroup.map_subtype_le _).trans inf_le_left
  ext y
  rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf, Subgroup.mem_inf]
  constructor
  · intro hy
    refine ⟨y.2, ?_⟩
    have hmem : (⟨(y : G), hLscL y.2⟩ : ↥c.L) ∈ CFSG.Open.pCore 2 ↥c.L := by
      rw [← QuotientGroup.eq_one_iff]
      exact hy
    exact Subgroup.mem_map_of_mem c.L.subtype hmem
  · rintro ⟨-, hmem⟩
    obtain ⟨z, hz, hzy⟩ := Subgroup.mem_map.mp hmem
    have hzeq : (⟨(y : G), hLscL y.2⟩ : ↥c.L) = z := Subtype.ext hzy.symm
    show (QuotientGroup.mk' (CFSG.Open.pCore 2 ↥c.L))
      ((Subgroup.inclusion ((Subgroup.map_subtype_le _).trans inf_le_left)) y) = 1
    rw [show (Subgroup.inclusion ((Subgroup.map_subtype_le _).trans inf_le_left)) y =
      ⟨(y : G), hLscL y.2⟩ from rfl, hzeq]
    rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
    exact hz

theorem aschbacherSolvableCore_Lz
    (c : Ctx82E3 D)
    (hON : UCK.ThreeCover (fun Y _ => IsSpor Y .ONan) c.Lbar)
    {P A : Subgroup G} (hP : CFSG.ABGLocalTools.IsSylowOf 3 P D.M)
    (hA : CFSG.Open.IsElemAbelian 3 A) (hZA : zSub P c.L ≤ A)
    {x : G} (hx : x ∈ zSub P c.L) (hx1 : x ≠ 1)
    (hC : Subgroup.centralizer ({x} : Set G) ≤ D.M) :
    aschbacherSolvableCore 3 ↥(Lz c x) =
      ((Lz c x) ⊓ CFSG.Open.pCoreOf 2 c.L).subgroupOf (Lz c x) := by
  classical
  have hLscL : Lz c x ≤ c.L := (Subgroup.map_subtype_le _).trans inf_le_left
  have hLsperf : Group.IsPerfect ↥(Lz c x) :=
    CFSG.RankThree.PartOne.isPerfect_of_mem_thetaComponentsAt
      (Lz_mem_thetaComponentsAt c hON hP hA hZA hx hx1 hC)
  haveI : Group.IsPerfect ↥(Lz c x) := hLsperf
  have hsurj : Function.Surjective (LzToLbar c x) :=
    LzToLbar_surjective c hON hP hA hZA hx hx1 hC
  haveI hLbarperf : Group.IsPerfect c.Lbar := Group.isPerfect_def.mpr hON.1.1
  have hQ : CFSG.IsQuasisimple c.Lbar :=
    (CFSG.ComponentClassification.AssemblyBPredicates.isQuasisimple_iff_native c.Lbar).mp hON.1
  have hθ := solvable_prime_complement_core_characterization (H := ↥(Lz c x))
    (p := 3) Nat.prime_three
  have hθsmall : aschbacherSolvableCore 3 ↥(Lz c x) ≤
      ((Lz c x) ⊓ CFSG.Open.pCoreOf 2 c.L).subgroupOf (Lz c x) := by
    set N := aschbacherSolvableCore 3 ↥(Lz c x) with hN
    haveI : Group.IsSolvable ↥N := hθ.1
    have hmapN_normal : (N.map (LzToLbar c x)).Normal :=
      (inferInstance : N.Normal).map (LzToLbar c x) hsurj
    have hmapN_solv : Group.IsSolvable ↥(N.map (LzToLbar c x)) := by
      have h := Group.isSolvable_of_surjective
        ((LzToLbar c x).comp N.subtype).rangeRestrict_surjective
      rwa [MonoidHom.range_comp, Subgroup.range_subtype] at h
    have hmapN_3 : ¬ 3 ∣ Nat.card ↥(N.map (LzToLbar c x)) := by
      intro h
      exact hθ.2.2.1 (h.trans (Subgroup.card_map_dvd (H := N) (LzToLbar c x)))
    have hmapN_le : N.map (LzToLbar c x) ≤ Subgroup.center c.Lbar := by
      rcases CFSG.LocalCores.quasisimple_normal_subgroups hQ hmapN_normal with htop | hcen
      · exfalso
        have h3L : 3 ∣ Nat.card c.Lbar := by
          rw [← hON.2.1]
          exact Subgroup.card_subgroup_dvd_card (Subgroup.center c.Lbar)
        have htopcard : Nat.card ↥(N.map (LzToLbar c x)) = Nat.card c.Lbar := by
          rw [htop]
          exact Nat.card_congr Subgroup.topEquiv.toEquiv
        exact hmapN_3 (htopcard ▸ h3L)
      · exact hcen
    have hone : Nat.card ↥(N.map (LzToLbar c x)) = 1 := by
      have h1 : Nat.card ↥(N.map (LzToLbar c x)) =
          Nat.card ↥((N.map (LzToLbar c x)).subgroupOf
            (Subgroup.center c.Lbar)) :=
        Nat.card_congr (Subgroup.subgroupOfEquivOfLe hmapN_le).symm.toEquiv
      have h2 : Nat.card ↥((N.map (LzToLbar c x)).subgroupOf
          (Subgroup.center c.Lbar)) ∣ 3 := by
        rw [← hON.2.1]
        exact Subgroup.card_subgroup_dvd_card _
      have h3 : ¬ 3 ∣ Nat.card ↥((N.map (LzToLbar c x)).subgroupOf
          (Subgroup.center c.Lbar)) := by
        rw [← h1]
        exact hmapN_3
      rcases (Nat.dvd_prime Nat.prime_three).mp h2 with h | h
      · exact h1.trans h
      · exact absurd (by rw [h]) h3
    have hbot : N.map (LzToLbar c x) = ⊥ :=
      Subgroup.eq_bot_of_card_eq (N.map (LzToLbar c x)) hone
    have hkerN : N ≤ (LzToLbar c x).ker := (Subgroup.map_eq_bot_iff N).mp hbot
    rwa [LzToLbar_ker] at hkerN
  have hker_le : ((Lz c x) ⊓ CFSG.Open.pCoreOf 2 c.L).subgroupOf (Lz c x) ≤
      aschbacherSolvableCore 3 ↥(Lz c x) := by
    have hNp : Lz c x ≤ Subgroup.normalizer (CFSG.Open.pCoreOf 2 c.L : Set G) :=
      normalizer_pCoreOf_le (hLscL.trans Subgroup.le_normalizer)
    have hnorm : (((Lz c x) ⊓ CFSG.Open.pCoreOf 2 c.L).subgroupOf (Lz c x)).Normal :=
      (Subgroup.normal_subgroupOf_iff_le_normalizer inf_le_left).mpr
        (CFSG.RankThree.PartOne.le_normalizer_inf_of_le_normalizer
          Subgroup.le_normalizer hNp)
    have h2 : IsPGroup 2 ↥(((Lz c x) ⊓ CFSG.Open.pCoreOf 2 c.L).subgroupOf (Lz c x)) := by
      have hP : IsPGroup 2 ↥((Lz c x) ⊓ CFSG.Open.pCoreOf 2 c.L) :=
        (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 c.L).to_le inf_le_right
      obtain ⟨n, hn⟩ := hP.exists_card_eq
      rw [IsPGroup.iff_card]
      exact ⟨n, (Nat.card_congr (Subgroup.subgroupOfEquivOfLe inf_le_left).toEquiv).trans hn⟩
    have hsolv : Group.IsSolvable
        ↥(((Lz c x) ⊓ CFSG.Open.pCoreOf 2 c.L).subgroupOf (Lz c x)) :=
      @IsNilpotent.to_isSolvable _ _ h2.isNilpotent
    have h3 : ¬ 3 ∣ Nat.card
        ↥(((Lz c x) ⊓ CFSG.Open.pCoreOf 2 c.L).subgroupOf (Lz c x)) := by
      obtain ⟨n, hn⟩ := h2.exists_card_eq
      intro h
      rw [hn] at h
      exact absurd (Nat.prime_three.dvd_of_dvd_pow h) (by norm_num)
    exact hθ.2.2.2.1 _ hnorm hsolv h3
  exact le_antisymm hθsmall hker_le

@[expose] noncomputable def thetaQuot_Lz_mulEquiv_Lbar
    (c : Ctx82E3 D)
    (hON : UCK.ThreeCover (fun Y _ => IsSpor Y .ONan) c.Lbar)
    {P A : Subgroup G} (hP : CFSG.ABGLocalTools.IsSylowOf 3 P D.M)
    (hA : CFSG.Open.IsElemAbelian 3 A) (hZA : zSub P c.L ≤ A)
    {x : G} (hx : x ∈ zSub P c.L) (hx1 : x ≠ 1)
    (hC : Subgroup.centralizer ({x} : Set G) ≤ D.M) :
    (↥(Lz c x) ⧸ aschbacherSolvableCore 3 ↥(Lz c x)) ≃* c.Lbar :=
  (QuotientGroup.quotientMulEquivOfEq
      ((aschbacherSolvableCore_Lz c hON hP hA hZA hx hx1 hC).trans
        (LzToLbar_ker c x).symm)).trans
    (QuotientGroup.quotientKerEquivOfSurjective (LzToLbar c x)
      (LzToLbar_surjective c hON hP hA hZA hx hx1 hC))

theorem theta_centralizer_autThetaQuot_eq_bot_core''
    (hK4 : K4) (c : Ctx82E3 D)
    (hON : UCK.ThreeCover (fun Y _ => IsSpor Y .ONan) c.Lbar)
    {P A : Subgroup G} (hP : CFSG.ABGLocalTools.IsSylowOf 3 P D.M)
    (hNZ : Subgroup.normalizer ((zSub P c.L : Subgroup G) : Set G) ≤ D.M)
    (hA : CFSG.Open.IsElemAbelian 3 A) (hA27 : Nat.card A = 27) (hZA : zSub P c.L ≤ A)
    (hAPL : A ≤ P ⊓ c.L) {x : G} (hx : x ∈ zSub P c.L) (hx1 : x ≠ 1)
    (hC : Subgroup.centralizer ({x} : Set G) ≤ D.M)
    {L : Subgroup G} (hL : L ∈ thetaComponentsAt 3 x)
    (h9 : Nat.card (autThetaQuot A L) = 9)
    {b : ↥(autThetaQuot (Subgroup.centralizer ({x} : Set G)) L)}
    (hb : (b : MulAut (L ⧸ aschbacherSolvableCore 3 L)) ∈ autThetaQuot A L) (hb1 : b ≠ 1) :
    inSubgroup (aschbacherSolvableCore 3)
      (Subgroup.centralizer ({b} : Set
        ↥(autThetaQuot (Subgroup.centralizer ({x} : Set G)) L))) = ⊥ := by
  classical
  have hLz : L = Lz c x :=
    eq_Lz_of_card_autThetaQuot_eq_nine c hON hP hA hZA hAPL hx hx1 hC hL h9
  subst hLz
  let H0 : Subgroup (MulAut (Lz c x ⧸ aschbacherSolvableCore 3 (Lz c x))) :=
    autThetaQuot (Subgroup.centralizer ({x} : Set G)) (Lz c x)
  let e := thetaQuot_Lz_mulEquiv_Lbar c hON hP hA hZA hx hx1 hC
  let eZ : ((Lz c x ⧸ aschbacherSolvableCore 3 (Lz c x)) ⧸
      Subgroup.center (Lz c x ⧸ aschbacherSolvableCore 3 (Lz c x))) ≃*
      (c.Lbar ⧸ Subgroup.center c.Lbar) :=
    QuotientGroup.congr _ _ e (Subgroup.map_center_eq e)
  let φ : MulAut (Lz c x ⧸ aschbacherSolvableCore 3 (Lz c x)) →*
      MulAut (c.Lbar ⧸ Subgroup.center c.Lbar) :=
    (MulAut.congr eZ).toMonoidHom.comp
      (CFSG.ComponentClassification.PerfectAutomorphisms.centerQuotientHom
        (Lz c x ⧸ aschbacherSolvableCore 3 (Lz c x)))
  have hΛperf : Group.IsPerfect (Lz c x ⧸ aschbacherSolvableCore 3 (Lz c x)) := by
    haveI : Group.IsPerfect ↥(Lz c x) :=
      CFSG.RankThree.PartOne.isPerfect_of_mem_thetaComponentsAt
        (Lz_mem_thetaComponentsAt c hON hP hA hZA hx hx1 hC)
    infer_instance
  haveI := hΛperf
  have hφinj : Function.Injective φ := by
    intro σ τ h
    refine CFSG.ComponentClassification.PerfectAutomorphisms.centerQuotientHom_injective _ ?_
    exact (MulAut.congr eZ).injective (by simpa [φ] using h)
  have hb3 : (b : MulAut (Lz c x ⧸ aschbacherSolvableCore 3 (Lz c x))) ^ 3 = 1 :=
    CFSG.RankThree.PartTwo.Sec13.autThetaQuot_pow_three (E := A) (L := Lz c x)
      (fun y hy => hA.2 y hy) hb
  have hbne : (b : MulAut (Lz c x ⧸ aschbacherSolvableCore 3 (Lz c x))) ≠ 1 :=
    fun h => hb1 (Subtype.ext (by simpa using h))
  have hbord : orderOf (b : MulAut (Lz c x ⧸ aschbacherSolvableCore 3 (Lz c x))) = 3 :=
    orderOf_eq_prime hb3 hbne
  have hσord : orderOf (φ (b : MulAut (Lz c x ⧸ aschbacherSolvableCore 3 (Lz c x)))) = 3 := by
    have h3 : (φ (b : MulAut (Lz c x ⧸ aschbacherSolvableCore 3 (Lz c x)))) ^ 3 = 1 := by
      rw [← map_pow, hb3, map_one]
    have hne : φ (b : MulAut (Lz c x ⧸ aschbacherSolvableCore 3 (Lz c x))) ≠ 1 := by
      intro h
      exact hbne (hφinj (by rw [h, map_one]))
    exact orderOf_eq_prime h3 hne
  have hthetaConj : ∀ l : ↥(Lz c x),
      thetaQuotMulAut ↥(Lz c x) (MulAut.conj l) =
        MulAut.conj (QuotientGroup.mk' (aschbacherSolvableCore 3 ↥(Lz c x)) l) := by
    intro l
    refine MulEquiv.ext fun q => ?_
    obtain ⟨z, rfl⟩ := QuotientGroup.mk'_surjective (aschbacherSolvableCore 3 ↥(Lz c x)) q
    rw [QuotientGroup.mk'_apply, thetaQuotMulAut_mk, MulAut.conj_apply]
    simp
  have hInnΛ : (MulAut.conj : (Lz c x ⧸ aschbacherSolvableCore 3 (Lz c x)) →*
      MulAut (Lz c x ⧸ aschbacherSolvableCore 3 (Lz c x))).range ≤ H0 := by
    rintro τ ⟨lam, rfl⟩
    obtain ⟨l, rfl⟩ := QuotientGroup.mk_surjective lam
    rw [mem_autThetaQuot_iff]
    refine ⟨(l : G), (Lz c x).le_normalizer l.2, ?_, ?_⟩
    · exact CFSG.RankThree.PartTwo.Sec6.le_centralizer_of_mem_thetaComponentsAt
        (Lz_mem_thetaComponentsAt c hON hP hA hZA hx hx1 hC) l.2
    · have hstep : (Lz c x).normalizerMonoidHom
          (⟨(l : G), (Lz c x).le_normalizer l.2⟩ : Subgroup.normalizer ((Lz c x) : Set G)) =
          MulAut.conj l := by
        refine MulEquiv.ext fun z => Subtype.ext ?_
        simp [CFSG.RankThree.PartTwo.Sec4.normalizerMonoidHom_apply_coe, MulAut.conj_apply]
      rw [hstep, hthetaConj, QuotientGroup.mk'_apply]
  have hcq : ∀ lam : (Lz c x ⧸ aschbacherSolvableCore 3 (Lz c x)),
      centerQuotientHom (Lz c x ⧸ aschbacherSolvableCore 3 (Lz c x)) (MulAut.conj lam) =
        MulAut.conj (QuotientGroup.mk'
          (Subgroup.center (Lz c x ⧸ aschbacherSolvableCore 3 (Lz c x))) lam) := by
    intro lam
    refine MulEquiv.ext fun q => ?_
    obtain ⟨z, rfl⟩ := QuotientGroup.mk'_surjective
      (Subgroup.center (Lz c x ⧸ aschbacherSolvableCore 3 (Lz c x))) q
    change CFSG.ComponentClassification.PerfectAutomorphisms.onCenterQuotient
      (MulAut.conj lam) ↑z = MulAut.conj (QuotientGroup.mk'
        (Subgroup.center (Lz c x ⧸ aschbacherSolvableCore 3 (Lz c x))) lam) ↑z
    rw [← QuotientGroup.mk'_apply (Subgroup.center (Lz c x ⧸ aschbacherSolvableCore 3 (Lz c x))) z,
      CFSG.ComponentClassification.PerfectAutomorphisms.onCenterQuotient_apply_mk,
      MulAut.conj_apply]
    simp
  let H : Subgroup (MulAut (c.Lbar ⧸ Subgroup.center c.Lbar)) := H0.map φ
  have hσH : φ (b : MulAut (Lz c x ⧸ aschbacherSolvableCore 3 (Lz c x))) ∈ H :=
    Subgroup.mem_map_of_mem φ b.2
  have hInn : (MulAut.conj : (c.Lbar ⧸ Subgroup.center c.Lbar) →*
      MulAut (c.Lbar ⧸ Subgroup.center c.Lbar)).range ≤ H := by
    rintro τ ⟨g, rfl⟩
    obtain ⟨q, rfl⟩ := eZ.surjective g
    obtain ⟨lam, rfl⟩ := QuotientGroup.mk_surjective q
    have hstep : MulAut.conj (eZ (lam : (Lz c x ⧸ aschbacherSolvableCore 3 (Lz c x)) ⧸
        Subgroup.center (Lz c x ⧸ aschbacherSolvableCore 3 (Lz c x)))) =
        φ (MulAut.conj lam) := by
      rw [show φ (MulAut.conj lam) = MulAut.congr eZ
          (centerQuotientHom (Lz c x ⧸ aschbacherSolvableCore 3 (Lz c x))
            (MulAut.conj lam)) from rfl, hcq lam]
      exact (CFSG.mulAut_congr_conj eZ lam).symm
    rw [hstep]
    exact Subgroup.mem_map_of_mem φ (hInnΛ ⟨lam, rfl⟩)
  have hK4' := hK4 (c.Lbar ⧸ Subgroup.center c.Lbar) hON.2.2 H hInn
    (φ (b : MulAut (Lz c x ⧸ aschbacherSolvableCore 3 (Lz c x)))) hσH hσord
  have hK'bot : aschbacherSolvableCore 3
      ↥(H ⊓ Subgroup.centralizer
        ({φ (b : MulAut (Lz c x ⧸ aschbacherSolvableCore 3 (Lz c x)))} :
          Set (MulAut (c.Lbar ⧸ Subgroup.center c.Lbar)))) = ⊥ := by
    have h := (Subgroup.map_eq_bot_iff
      (H := aschbacherSolvableCore 3
        ↥(H ⊓ Subgroup.centralizer
          ({φ (b : MulAut (Lz c x ⧸ aschbacherSolvableCore 3 (Lz c x)))} :
            Set (MulAut (c.Lbar ⧸ Subgroup.center c.Lbar)))))
      (f := (H ⊓ Subgroup.centralizer
        ({φ (b : MulAut (Lz c x ⧸ aschbacherSolvableCore 3 (Lz c x)))} :
          Set (MulAut (c.Lbar ⧸ Subgroup.center c.Lbar)))).subtype)).mp hK4'.2
    have hker : (H ⊓ Subgroup.centralizer
        ({φ (b : MulAut (Lz c x ⧸ aschbacherSolvableCore 3 (Lz c x)))} :
          Set (MulAut (c.Lbar ⧸ Subgroup.center c.Lbar)))).subtype.ker = ⊥ :=
      (MonoidHom.ker_eq_bot_iff _).mpr (Subgroup.subtype_injective _)
    rw [hker] at h
    exact le_bot_iff.mp h
  let ψhom : ↥H0 →* ↥H :=
    { toFun := fun y => ⟨φ (y : MulAut (Lz c x ⧸ aschbacherSolvableCore 3 (Lz c x))),
        Subgroup.mem_map_of_mem φ y.2⟩
      map_one' := Subtype.ext (map_one φ)
      map_mul' := fun y z => Subtype.ext
        (map_mul φ (y : MulAut (Lz c x ⧸ aschbacherSolvableCore 3 (Lz c x)))
          (z : MulAut (Lz c x ⧸ aschbacherSolvableCore 3 (Lz c x)))) }
  have hψinj : Function.Injective ψhom := by
    intro y z h
    exact Subtype.ext (hφinj (congrArg
      (fun w : ↥H => (w : MulAut (c.Lbar ⧸ Subgroup.center c.Lbar))) h))
  have hψsurj : Function.Surjective ψhom := by
    rintro ⟨y, hy⟩
    obtain ⟨z, hz, rfl⟩ := Subgroup.mem_map.mp hy
    exact ⟨⟨z, hz⟩, rfl⟩
  let σ : MulAut (c.Lbar ⧸ Subgroup.center c.Lbar) :=
    φ (b : MulAut (Lz c x ⧸ aschbacherSolvableCore 3 (Lz c x)))
  have hσmem : σ ∈ H := Subgroup.mem_map_of_mem φ b.2
  have hcent : ∀ v : MulAut (c.Lbar ⧸ Subgroup.center c.Lbar),
      v ∈ Subgroup.centralizer ({σ} : Set (MulAut (c.Lbar ⧸ Subgroup.center c.Lbar))) ↔
        v * σ = σ * v := fun v => Subgroup.mem_centralizer_singleton_iff
  have hcent0 : ∀ v : ↥H0, v ∈ Subgroup.centralizer ({b} : Set ↥H0) ↔
      (v : MulAut (Lz c x ⧸ aschbacherSolvableCore 3 (Lz c x))) *
        (b : MulAut (Lz c x ⧸ aschbacherSolvableCore 3 (Lz c x))) =
      (b : MulAut (Lz c x ⧸ aschbacherSolvableCore 3 (Lz c x))) *
        (v : MulAut (Lz c x ⧸ aschbacherSolvableCore 3 (Lz c x))) := by
    intro v
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact ⟨fun h => congrArg (fun w : ↥H0 => (w : MulAut
      (Lz c x ⧸ aschbacherSolvableCore 3 (Lz c x)))) h, fun h => Subtype.ext h⟩
  have hmemK' : ∀ v : ↥H,
      v ∈ (H ⊓ Subgroup.centralizer
        ({σ} : Set (MulAut (c.Lbar ⧸ Subgroup.center c.Lbar)))).subgroupOf H ↔
      (v : MulAut (c.Lbar ⧸ Subgroup.center c.Lbar)) ∈
        H ⊓ Subgroup.centralizer
          ({σ} : Set (MulAut (c.Lbar ⧸ Subgroup.center c.Lbar))) :=
    fun v => Subgroup.mem_subgroupOf
  have hmeminf : ∀ v : MulAut (c.Lbar ⧸ Subgroup.center c.Lbar),
      v ∈ H ⊓ Subgroup.centralizer
          ({σ} : Set (MulAut (c.Lbar ⧸ Subgroup.center c.Lbar))) ↔
        v ∈ H ∧ v ∈ Subgroup.centralizer
          ({σ} : Set (MulAut (c.Lbar ⧸ Subgroup.center c.Lbar))) :=
    fun v => Subgroup.mem_inf
  have hKmem : ∀ v : ↥H0,
      ψhom v ∈ (H ⊓ Subgroup.centralizer
        ({σ} : Set (MulAut (c.Lbar ⧸ Subgroup.center c.Lbar)))).subgroupOf H ↔
      (v : MulAut (Lz c x ⧸ aschbacherSolvableCore 3 (Lz c x))) *
        (b : MulAut (Lz c x ⧸ aschbacherSolvableCore 3 (Lz c x))) =
      (b : MulAut (Lz c x ⧸ aschbacherSolvableCore 3 (Lz c x))) *
        (v : MulAut (Lz c x ⧸ aschbacherSolvableCore 3 (Lz c x))) := by
    intro v
    rw [hmemK' (ψhom v), hmeminf (ψhom v), hcent (ψhom v)]
    constructor
    · rintro ⟨-, h⟩
      rw [show (ψhom v : MulAut (c.Lbar ⧸ Subgroup.center c.Lbar)) =
        φ (v : MulAut (Lz c x ⧸ aschbacherSolvableCore 3 (Lz c x))) from rfl] at h
      rw [show σ = φ (b : MulAut (Lz c x ⧸ aschbacherSolvableCore 3 (Lz c x)))
        from rfl] at h
      rw [← map_mul, ← map_mul] at h
      exact hφinj h
    · intro h
      refine ⟨(ψhom v).2, ?_⟩
      rw [show (ψhom v : MulAut (c.Lbar ⧸ Subgroup.center c.Lbar)) =
        φ (v : MulAut (Lz c x ⧸ aschbacherSolvableCore 3 (Lz c x))) from rfl,
        show σ = φ (b : MulAut (Lz c x ⧸ aschbacherSolvableCore 3 (Lz c x))) from rfl,
        ← map_mul, ← map_mul]
      exact congrArg φ h
  have hKmap : (Subgroup.centralizer ({b} : Set ↥H0)).map ψhom =
      (H ⊓ Subgroup.centralizer
        ({σ} : Set (MulAut (c.Lbar ⧸ Subgroup.center c.Lbar)))).subgroupOf H := by
    ext w
    constructor
    · rintro ⟨y, hy, rfl⟩
      exact (hKmem y).mpr ((hcent0 y).mp hy)
    · intro hw
      obtain ⟨hyH, hyC⟩ := (hmeminf w).mp ((hmemK' w).mp hw)
      obtain ⟨y, hy⟩ := hψsurj ⟨w, hyH⟩
      have hval : (ψhom y : MulAut (c.Lbar ⧸ Subgroup.center c.Lbar)) = w :=
        congrArg (fun v : ↥H => (v : MulAut (c.Lbar ⧸ Subgroup.center c.Lbar))) hy
      refine Subgroup.mem_map.mpr ⟨y, ?_, hy⟩
      have h1 : ψhom y ∈ (H ⊓ Subgroup.centralizer
          ({σ} : Set (MulAut (c.Lbar ⧸ Subgroup.center c.Lbar)))).subgroupOf H := by
        rw [hy]
        exact (hmemK' w).mp hw
      exact (hcent0 y).mpr ((hKmem y).mp h1)
  have hK'bot' : aschbacherSolvableCore 3
      ↥((H ⊓ Subgroup.centralizer
        ({σ} : Set (MulAut (c.Lbar ⧸ Subgroup.center c.Lbar)))).subgroupOf H) = ⊥ := by
    have hmap := CFSG.RankThree.aschbacherSolvableCore_map_mulEquiv Nat.prime_three
      (Subgroup.subgroupOfEquivOfLe (inf_le_left :
        H ⊓ Subgroup.centralizer
          ({σ} : Set (MulAut (c.Lbar ⧸ Subgroup.center c.Lbar))) ≤ H))
    rw [hK'bot] at hmap
    have h2 := (Subgroup.map_eq_bot_iff (H := aschbacherSolvableCore 3
      ↥((H ⊓ Subgroup.centralizer
        ({σ} : Set (MulAut (c.Lbar ⧸ Subgroup.center c.Lbar)))).subgroupOf H))
      (f := (Subgroup.subgroupOfEquivOfLe (inf_le_left :
        H ⊓ Subgroup.centralizer
          ({σ} : Set (MulAut (c.Lbar ⧸ Subgroup.center c.Lbar))) ≤ H)).toMonoidHom)).mp hmap
    have hker : (Subgroup.subgroupOfEquivOfLe (inf_le_left :
        H ⊓ Subgroup.centralizer
          ({σ} : Set (MulAut (c.Lbar ⧸ Subgroup.center c.Lbar))) ≤ H)).toMonoidHom.ker = ⊥ :=
      (MonoidHom.ker_eq_bot_iff _).mpr
        (Subgroup.subgroupOfEquivOfLe (inf_le_left :
          H ⊓ Subgroup.centralizer
            ({σ} : Set (MulAut (c.Lbar ⧸ Subgroup.center c.Lbar))) ≤ H)).injective
    rw [hker] at h2
    exact le_bot_iff.mp h2
  have hKbot : aschbacherSolvableCore 3 ↥(Subgroup.centralizer ({b} : Set ↥H0)) = ⊥ := by
    let eKhom : ↥(Subgroup.centralizer ({b} : Set ↥H0)) →*
        ↥((H ⊓ Subgroup.centralizer
          ({σ} : Set (MulAut (c.Lbar ⧸ Subgroup.center c.Lbar)))).subgroupOf H) :=
      { toFun := fun y => ⟨ψhom y, (hKmem y).mpr ((hcent0 y).mp y.2)⟩
        map_one' := Subtype.ext (map_one ψhom)
        map_mul' := fun y z => Subtype.ext
          (map_mul ψhom (y : ↥H0) (z : ↥H0)) }
    have heKinj : Function.Injective eKhom := by
      intro y z h
      exact Subtype.ext (hψinj (congrArg Subtype.val h))
    have heKsurj : Function.Surjective eKhom := by
      rintro ⟨w, hw⟩
      obtain ⟨hyH, hyC⟩ := (hmeminf w).mp ((hmemK' w).mp hw)
      obtain ⟨y, hy⟩ := hψsurj ⟨w, hyH⟩
      have hval : (ψhom y : MulAut (c.Lbar ⧸ Subgroup.center c.Lbar)) = w :=
        congrArg (fun v : ↥H => (v : MulAut (c.Lbar ⧸ Subgroup.center c.Lbar))) hy
      have hyK : y ∈ Subgroup.centralizer ({b} : Set ↥H0) := by
        rw [hcent0 y]
        refine (hKmem y).mp ?_
        rw [hy]
        exact (hmemK' w).mp hw
      refine ⟨⟨y, hyK⟩, Subtype.ext hy⟩
    let eK : ↥(Subgroup.centralizer ({b} : Set ↥H0)) ≃*
        ↥((H ⊓ Subgroup.centralizer
          ({σ} : Set (MulAut (c.Lbar ⧸ Subgroup.center c.Lbar)))).subgroupOf H) :=
      MulEquiv.ofBijective eKhom ⟨heKinj, heKsurj⟩
    have hmap := CFSG.RankThree.aschbacherSolvableCore_map_mulEquiv Nat.prime_three eK
    rw [hK'bot'] at hmap
    have h2 := (Subgroup.map_eq_bot_iff (H := aschbacherSolvableCore 3
      ↥(Subgroup.centralizer ({b} : Set ↥H0))) (f := eK.toMonoidHom)).mp hmap
    have hker : eK.toMonoidHom.ker = ⊥ := (MonoidHom.ker_eq_bot_iff _).mpr eK.injective
    rw [hker] at h2
    exact le_bot_iff.mp h2
  rw [show inSubgroup (aschbacherSolvableCore 3)
      (Subgroup.centralizer ({b} : Set ↥H0)) =
      (aschbacherSolvableCore 3 ↥(Subgroup.centralizer ({b} : Set ↥H0))).map
        (Subgroup.centralizer ({b} : Set ↥H0)).subtype from rfl, hKbot, Subgroup.map_bot]

theorem theta_centralizer_autThetaQuot_eq_bot''''
    (hK4 : K4) (c : Ctx82E3 D)
    (hON : UCK.ThreeCover (fun Y _ => IsSpor Y .ONan) c.Lbar)
    {P A : Subgroup G} (hP : CFSG.ABGLocalTools.IsSylowOf 3 P D.M)
    (hNZ : Subgroup.normalizer ((zSub P c.L : Subgroup G) : Set G) ≤ D.M)
    (hA : CFSG.Open.IsElemAbelian 3 A) (hA27 : Nat.card A = 27) (hZA : zSub P c.L ≤ A)
    (hAPL : A ≤ P ⊓ c.L) {x : G} (hx : x ∈ zSub P c.L) (hx1 : x ≠ 1)
    (hC : Subgroup.centralizer ({x} : Set G) ≤ D.M)
    {L : Subgroup G} (hL : L ∈ thetaComponentsAt 3 x)
    (h9 : Nat.card (autThetaQuot A L) = 9)
    {b : ↥(autThetaQuot (Subgroup.centralizer ({x} : Set G)) L)}
    (hb : (b : MulAut (L ⧸ aschbacherSolvableCore 3 L)) ∈ autThetaQuot A L) (hb1 : b ≠ 1) :
    inSubgroup (aschbacherSolvableCore 3)
      (Subgroup.centralizer ({b} : Set
        ↥(autThetaQuot (Subgroup.centralizer ({x} : Set G)) L))) = ⊥ :=
  theta_centralizer_autThetaQuot_eq_bot_core'' hK4 c hON hP hNZ hA hA27 hZA hAPL hx hx1 hC
    hL h9 hb hb1

end
end CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82E3.ONan

namespace CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82E3.ONan
section
open CFSG.Open
open CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo.Sec4
open CFSG.LocalAnalysis.UniquenessCase.UC22 (Data IsSpor)
variable {G : Type} [Group G] [Finite G]
variable {D : Data G}

theorem thetaAlpha_center_eq_bot
    (hK4 : K4) (c : Ctx82E3 D)
    (hON : UCK.ThreeCover (fun Y _ => IsSpor Y .ONan) c.Lbar)
    {P A : Subgroup G} (hP : CFSG.ABGLocalTools.IsSylowOf 3 P D.M)
    (hNZ : Subgroup.normalizer ((zSub P c.L : Subgroup G) : Set G) ≤ D.M)
    (hA : CFSG.Open.IsElemAbelian 3 A) (hA27 : Nat.card A = 27) (hZA : zSub P c.L ≤ A)
    (hAPL : A ≤ P ⊓ c.L) {x : G} (hx : x ∈ zSub P c.L) (hx1 : x ≠ 1)
    (hC : Subgroup.centralizer ({x} : Set G) ≤ D.M)
    {L : Subgroup G} (hL : L ∈ thetaComponentsAt 3 x)
    (h9 : Nat.card (autThetaQuot A L) = 9) :
    thetaAlpha 3 ((autThetaQuot A L).subgroupOf
      (autThetaQuot (Subgroup.centralizer ({x} : Set G)) L)) = ⊥ := by
  classical
  have hAC : A ≤ Subgroup.centralizer ({x} : Set G) :=
    le_centralizer_of_le_inf c hAPL hx
  have hAH : autThetaQuot A L ≤ autThetaQuot (Subgroup.centralizer ({x} : Set G)) L :=
    CFSG.RankThree.PartTwo.Sec13.autThetaQuot_mono hAC L
  have hcard : Nat.card ((autThetaQuot A L).subgroupOf
      (autThetaQuot (Subgroup.centralizer ({x} : Set G)) L)) = 9 :=
    (Nat.card_congr (Subgroup.subgroupOfEquivOfLe hAH).toEquiv).trans h9
  refine CFSG.RankThree.PartTwo.Sec4.Res423Two.thetaAlpha_eq_bot_of_forall ?_ ?_
  · intro hbot
    have h1 : Nat.card ((autThetaQuot A L).subgroupOf
        (autThetaQuot (Subgroup.centralizer ({x} : Set G)) L)) = 1 := by
      rw [hbot, Subgroup.card_bot]
    omega
  · intro b hb hb1
    exact theta_centralizer_autThetaQuot_eq_bot'''' hK4 c hON hP hNZ hA hA27 hZA hAPL hx hx1 hC
      hL h9 (Subgroup.mem_subgroupOf.mp hb) hb1

theorem k341_hyps_center'
    (hK4 : K4) (c : Ctx82E3 D)
    (hON : UCK.ThreeCover (fun Y _ => IsSpor Y .ONan) c.Lbar)
    (h7 : D.sig = {7})
    {P A : Subgroup G} (hP : CFSG.ABGLocalTools.IsSylowOf 3 P D.M)
    (hNZ : Subgroup.normalizer ((zSub P c.L : Subgroup G) : Set G) ≤ D.M)
    (hA : CFSG.Open.IsElemAbelian 3 A) (hA27 : Nat.card A = 27) (hZA : zSub P c.L ≤ A)
    (hAPL : A ≤ P ⊓ c.L)
    {x : G} (hx : x ∈ zSub P c.L) (hx1 : x ≠ 1) :
    (∀ L ∈ thetaComponentsAt 3 x, A ≤ Subgroup.normalizer (L : Set G)) ∧
    (∀ L ∈ thetaComponentsAt 3 x, Nat.card (autThetaQuot A L) = 9 →
      thetaAlpha 3 ((autThetaQuot A L).subgroupOf
        (autThetaQuot (Subgroup.centralizer ({x} : Set G)) L)) = ⊥) := by
  have hZcard : Nat.card (zSub P c.L) = 3 := card_zSub_of_onan' c hON hP
  have hC : Subgroup.centralizer ({x} : Set G) ≤ D.M :=
    centralizer_le_M_of_mem_zSub c hZcard hNZ hA hZA hx hx1
  exact ⟨thetaComponentsAt_center_normalized''' c hON hP hNZ hA hA27 hZA hAPL hx hx1 hC,
   fun L hL h9 =>
    thetaAlpha_center_eq_bot hK4 c hON hP hNZ hA hA27 hZA hAPL hx hx1 hC hL h9⟩

end
end CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82E3.ONan
