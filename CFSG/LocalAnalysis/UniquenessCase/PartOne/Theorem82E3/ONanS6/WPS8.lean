module

public import CFSG.GroupTheory.ExtraspecialThreeFive
public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82E3.ONanK8K9
public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82E3.ONanK2
public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82E3.ONanKFacts
public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82E3.ONanSz
public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82E3.ONanS6.WPF9I
public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82E3.ONanS6.WPFF2
public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82E3.ONanS6.WPL
public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82E3.ONanS6.WPL4
public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82E3.ONanS6.WPL5
public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82E3.ONanS6.WPL9
public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82E3.ONanS6.WPS
public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82E3.ONanS6.WPS2a
public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82E3.ONanS6.WPS2b
public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82E3.ONanS6.WPS3b
public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82E3.ONanS6.WPS5b
public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82E3.ONanS6.WPS6g4
public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82E3.ONanS6.WPS7a
public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82E3.ONanS6.WPS7b
public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82E3.ONanS6.WPZ
public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82E3.ONanS6.WPZ2b
public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82E3.ONanS6.WPZs
public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82E3.ONanS6.WS6
public import CFSG.GH74.GLS.Stage2.Signalizer.Odd87GrpSwap
import CFSG.RankThree.PartTwo.Sec18.Transport

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82E3.ONan
section
open GroupTheory.CoprimeActionSupport.TwoModuloExtension (perfectResidual_le_of_isSolvable_quotient)
open CFSG.Open
open CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo.Sec4
open CFSG.LocalAnalysis.UniquenessCase.UC22 (Data IsSpor IsAlt)
open CFSG.RankThree.PartTwo.Sec4 (IsTripleCover)
open scoped commutatorElement
variable {G : Type} [Group G] [Finite G]
variable {D : Data G}

theorem perfectCoreGeneration_holds'
    (c : Ctx82E3 D) {P A : Subgroup G} {a : G}
    (hON : UCK.ThreeCover (fun Y _ => IsSpor Y .ONan) c.Lbar)
    (hP : CFSG.ABGLocalTools.IsSylowOf 3 P D.M)
    (hA : CFSG.Open.IsElemAbelian 3 A) (hA27 : Nat.card A = 27)
    (hZA : zSub P c.L ≤ A) (hAPL : A ≤ P ⊓ c.L) (ha : a ∈ A)
    (haZ : a ∉ zSub P c.L) :
    PerfectCoreGeneration c A a := by
  classical
  letI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have haPL : a ∈ P ⊓ c.L := hAPL ha
  have haP : a ∈ P := haPL.1
  have haL : a ∈ c.L := haPL.2
  let O : Subgroup ↥c.L := CFSG.Open.pCore 2 ↥c.L
  let π : ↥c.L →* c.Lbar := QuotientGroup.mk' O
  let aL : ↥c.L := ⟨a, haL⟩
  let x : c.Lbar := π aL
  let K : Subgroup G := c.L ⊓ Subgroup.centralizer ({a} : Set G)
  let H : Subgroup ↥c.L := K.subgroupOf c.L
  let C : Subgroup c.Lbar := Subgroup.centralizer ({x} : Set c.Lbar)
  have haL3 : aL ^ 3 = 1 := by
    apply Subtype.ext
    simpa [aL] using hA.2 a ha
  have ha1 : a ≠ 1 := by
    intro h1
    exact haZ (by rw [h1]; exact Subgroup.one_mem _)
  have ha1L : aL ≠ 1 := fun h => ha1 (Subtype.ext_iff.mp h)
  have haL_order : orderOf aL = 3 := orderOf_eq_prime haL3 ha1L
  have hx_ne : x ≠ 1 := by
    intro hx1
    have hxO : aL ∈ O :=
      (QuotientGroup.eq_one_iff (N := O) aL).mp (by simpa [x, π] using hx1)
    have h3dvd : 3 ∣ Nat.card O := by
      have h := Subgroup.orderOf_dvd_natCard O hxO
      rwa [haL_order] at h
    exact CFSG.GroupTheory.not_dvd_card_of_isPGroup (p := 2) (q := 3)
      CFSG.pCore_isPGroup Nat.prime_three (by norm_num) h3dvd
  have hx3 : orderOf x = 3 := by
    have hxdvd : orderOf x ∣ 3 := by
      have h := orderOf_map_dvd π aL
      rwa [haL_order] at h
    rcases (Nat.dvd_prime Nat.prime_three).mp hxdvd with h1 | h3
    · exact absurd (orderOf_eq_one_iff.mp h1) hx_ne
    · exact h3
  have hxZ : x ∉ Subgroup.center c.Lbar :=
    image_not_center_of_not_mem_zSub c hON hP haP haL haZ
  have hK2 := K2ONanCentralizer_holds (Y := c.Lbar) hON x hx3 hxZ
  dsimp only at hK2
  obtain ⟨hCcard, hZY, hJcard, hCeq, hAlt⟩ := hK2
  let J : Subgroup c.Lbar := ⁅C, C⁆
  have hCeq' : C = Subgroup.zpowers x ⊔ J := hCeq
  have hJleC : J ≤ C := Subgroup.commutator_le_self C
  have hxcentC : x ∈ Subgroup.centralizer (C : Set c.Lbar) := by
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    exact Subgroup.mem_centralizer_singleton_iff.mp hy
  have hJperf : Group.IsPerfect ↥J :=
    isPerfect_commutator_of_centralizer_decomp hCeq' rfl hxcentC
  have hperfJC : Group.IsPerfect ↥(J.subgroupOf C) :=
    Group.IsPerfect.ofSurjective (f := (Subgroup.subgroupOfEquivOfLe hJleC).symm.toMonoidHom)
      (Subgroup.subgroupOfEquivOfLe hJleC).symm.surjective
  have hJ_le_perf : J ≤ (CFSG.perfectResidual ↥C).map C.subtype := by
    have hJC : J.subgroupOf C ≤ CFSG.perfectResidual ↥C :=
      CFSG.RankThreeCoreUniqueness.Helpers.perfect_subgroup_le_perfectResidual
        (J.subgroupOf C) hperfJC
    have hmap := Subgroup.map_mono (f := C.subtype) hJC
    rwa [Subgroup.map_subgroupOf_eq_of_le hJleC] at hmap
  have hJeq : (CFSG.perfectResidual ↥C).map C.subtype = J := by
    refine le_antisymm ?_ ?_
    · haveI : (J.subgroupOf C).Normal :=
        CFSG.GroupTheory.normal_subgroupOf_of_commutator_le (le_refl J)
      have hiscomm : IsMulCommutative (↥C ⧸ J.subgroupOf C) :=
        CFSG.GroupTheory.isMulCommutative_quotient_subgroupOf_of_commutator_le
          (V := J) (W := C) (le_refl J)
      letI : IsMulCommutative (↥C ⧸ J.subgroupOf C) := hiscomm
      have hsolv : Group.IsSolvable (↥C ⧸ J.subgroupOf C) :=
        Group.isSolvable_of_comm (fun p q => (IsMulCommutative.is_comm).comm p q)
      have hle :=
        perfectResidual_le_of_isSolvable_quotient
          (N := J.subgroupOf C) hsolv
      calc (CFSG.perfectResidual ↥C).map C.subtype
          ≤ (J.subgroupOf C).map C.subtype := Subgroup.map_mono hle
        _ = J := Subgroup.map_subgroupOf_eq_of_le hJleC
    · exact hJ_le_perf
  have hzp3 : IsPGroup 3 ↥(Subgroup.zpowers aL) := by
    refine IsPGroup.of_card (n := 1) ?_
    rw [Nat.card_zpowers, haL_order]
    norm_num
  letI : Fact (IsPGroup 3 ↥(Subgroup.zpowers aL)) := ⟨hzp3⟩
  have hcopO : Nat.Coprime 3 (Nat.card O) :=
    (Nat.prime_three.coprime_iff_not_dvd).mpr
      (CFSG.GroupTheory.not_dvd_card_of_isPGroup (p := 2) (q := 3)
        CFSG.pCore_isPGroup Nat.prime_three (by norm_num))
  have hcentral :=
    CFSG.centralizer_map_quotient_eq_map_centralizer (p := 3)
      (T := Subgroup.zpowers aL) (M := O) (by infer_instance) hcopO
  have hzp_map : Subgroup.map π (Subgroup.zpowers aL) = Subgroup.zpowers x := by
    simpa [x, π] using MonoidHom.map_zpowers π aL
  have hcent_zp : Subgroup.centralizer (Subgroup.zpowers aL : Set ↥c.L) = H := by
    rw [Subgroup.zpowers_eq_closure, Subgroup.centralizer_closure]
    ext y
    simp [H, K, aL, Subgroup.mem_subgroupOf, Subgroup.mem_inf,
      Subgroup.mem_centralizer_iff, Subgroup.mem_centralizer_singleton_iff]
    constructor
    · intro h
      exact congrArg Subtype.val h
    · intro h
      exact Subtype.ext h
  have hcent_zpx : Subgroup.centralizer (Subgroup.zpowers x : Set c.Lbar) = C := by
    rw [Subgroup.zpowers_eq_closure, Subgroup.centralizer_closure]
  have hHmapC : H.map π = C := by
    have h := hcentral
    dsimp only at h
    rw [hzp_map, hcent_zp, hcent_zpx] at h
    exact h.symm
  let φH : ↥H →* c.Lbar := π.comp H.subtype
  have hφH_range : φH.range = C := by
    rw [show φH = π.comp H.subtype from rfl, MonoidHom.range_comp, Subgroup.range_subtype]
    exact hHmapC
  let φC : ↥H →* ↥C := φH.codRestrict C (fun h => by
    have hh : φH h ∈ φH.range := ⟨h, rfl⟩
    rwa [hφH_range] at hh)
  have hφC_surj : Function.Surjective φC := by
    intro y
    have hy : (y : c.Lbar) ∈ φH.range := by
      rw [hφH_range]
      exact y.2
    obtain ⟨h, hh⟩ := hy
    exact ⟨h, Subtype.ext hh⟩
  have hmapCsurj :=
    CFSG.RankThreeCoreUniqueness.Helpers.finite_perfectResidual_map_eq φC hφC_surj
  let IP : Subgroup ↥H := CFSG.perfectResidual H
  have hmapJ : IP.map φH = J := by
    have hcomp : C.subtype.comp φC = φH := MonoidHom.ext (fun _ => rfl)
    calc IP.map φH = IP.map (C.subtype.comp φC) := by rw [hcomp]
      _ = (IP.map φC).map C.subtype := (Subgroup.map_map _ _ _).symm
      _ = (CFSG.perfectResidual ↥C).map C.subtype := by
        rw [show IP.map φC = CFSG.perfectResidual ↥C from hmapCsurj]
      _ = J := hJeq
  let fG : ↥H →* G := c.L.subtype.comp H.subtype
  have hHmapK : H.map c.L.subtype = K := by
    change (K.subgroupOf c.L).map c.L.subtype = K
    rw [Subgroup.subgroupOf_map_subtype, inf_eq_left]
    exact inf_le_left
  have hIPmap : IP.map fG = perfectCoreL c a := by
    have h1 : IP.map (c.L.subtype.comp H.subtype) =
        inSubgroup perfectResidual (H.map c.L.subtype) := by
      rw [← Subgroup.map_map,
        CFSG.RankThree.PartTwo.Sec18.inSubgroup_perfectResidual_map
          (f := c.L.subtype) (hf := c.L.subtype_injective)]
      rfl
    rw [h1, hHmapK]
  have haK : a ∈ K :=
    Subgroup.mem_inf.mpr ⟨haL, Subgroup.mem_centralizer_singleton_iff.mpr (by rfl)⟩
  let aH : ↥H := ⟨aL, Subgroup.mem_subgroupOf.mpr haK⟩
  have hzp_aL : (Subgroup.zpowers a).subgroupOf c.L = Subgroup.zpowers aL := by
    ext y
    rw [Subgroup.mem_subgroupOf, Subgroup.mem_zpowers_iff, Subgroup.mem_zpowers_iff]
    constructor
    · rintro ⟨k, hk⟩
      exact ⟨k, Subtype.ext (by simpa [aL] using hk)⟩
    · rintro ⟨k, hk⟩
      exact ⟨k, by simpa [aL] using congrArg Subtype.val hk⟩
  have hzp_map_H : (Subgroup.zpowers aH).map H.subtype =
      (Subgroup.zpowers a).subgroupOf c.L := by
    rw [MonoidHom.map_zpowers]
    change Subgroup.zpowers aL = (Subgroup.zpowers a).subgroupOf c.L
    rw [hzp_aL]
  have hIP_map_H : IP.map H.subtype = (perfectCoreL c a).subgroupOf c.L := by
    apply Subgroup.map_injective (f := c.L.subtype) c.L.subtype_injective
    calc (IP.map H.subtype).map c.L.subtype
        = IP.map (c.L.subtype.comp H.subtype) := (Subgroup.map_map _ _ _)
      _ = perfectCoreL c a := hIPmap
      _ = ((perfectCoreL c a).subgroupOf c.L).map c.L.subtype :=
        (Subgroup.map_subgroupOf_eq_of_le ((perfectCoreL_le c a).trans inf_le_left)).symm
  have hI_le_L : perfectCoreL c a ≤ c.L :=
    (perfectCoreL_le c a).trans inf_le_left
  have hzp_le_L : Subgroup.zpowers a ≤ c.L := Subgroup.zpowers_le.mpr haL
  let B : Subgroup G := Subgroup.zpowers a ⊔ perfectCoreL c a
  let B_H : Subgroup ↥H := Subgroup.zpowers aH ⊔ IP
  have hBH_map : B_H.map H.subtype = B.subgroupOf c.L := by
    change (Subgroup.zpowers aH ⊔ IP).map H.subtype = B.subgroupOf c.L
    rw [Subgroup.map_sup, hzp_map_H, hIP_map_H]
    change (Subgroup.zpowers a).subgroupOf c.L ⊔ (perfectCoreL c a).subgroupOf c.L =
      (Subgroup.zpowers a ⊔ perfectCoreL c a).subgroupOf c.L
    rw [Subgroup.subgroupOf_sup hzp_le_L hI_le_L]
  have haH_center : aH ∈ Subgroup.center ↥H := by
    rw [Subgroup.mem_center_iff]
    intro h
    apply Subtype.ext
    apply Subtype.ext
    have hK : ((h : ↥c.L) : G) ∈ K := Subgroup.mem_subgroupOf.mp h.2
    have hcent : ((h : ↥c.L) : G) ∈ Subgroup.centralizer ({a} : Set G) := hK.2
    exact Subgroup.mem_centralizer_singleton_iff.mp hcent
  have hBHnormal : B_H.Normal := by
    haveI hIPchar : IP.Characteristic :=
      CFSG.RankThreeCoreUniqueness.Helpers.perfectResidual_characteristic (G := ↥H)
    haveI hIPnormal : IP.Normal := inferInstance
    haveI hzp_normal : (Subgroup.zpowers aH).Normal :=
      Subgroup.normal_of_le_center (Subgroup.zpowers_le.mpr haH_center)
    change (Subgroup.zpowers aH ⊔ IP).Normal
    infer_instance
  have hBHmapC : B_H.map φH = C := by
    change (Subgroup.zpowers aH ⊔ IP).map φH = C
    rw [Subgroup.map_sup]
    have hzp : (Subgroup.zpowers aH).map φH = Subgroup.zpowers x := by
      rw [MonoidHom.map_zpowers]
      rfl
    rw [hzp, hmapJ, hCeq']
  have hA_L : A ≤ c.L := hAPL.trans inf_le_right
  have hA_K : A ≤ K := by
    intro y hy
    refine Subgroup.mem_inf.mpr ⟨hA_L hy, ?_⟩
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact congrArg Subtype.val ((hA.1.is_comm).comm ⟨y, hy⟩ ⟨a, ha⟩)
  let A_L : Subgroup ↥c.L := A.subgroupOf c.L
  have hA_L_H : A_L ≤ H := by
    intro y hy
    exact Subgroup.mem_subgroupOf.mpr (hA_K (Subgroup.mem_subgroupOf.mp hy))
  let A_H : Subgroup ↥H := A_L.subgroupOf H
  have hA3 : IsPGroup 3 ↥A := by
    refine IsPGroup.of_card (n := 3) ?_
    rw [hA27]
    norm_num
  have hA_H_3 : IsPGroup 3 ↥A_H := by
    let eA : ↥A ≃* ↥A_H :=
      (Subgroup.subgroupOfEquivOfLe hA_L).symm.trans
        (Subgroup.subgroupOfEquivOfLe hA_L_H).symm
    exact IsPGroup.of_equiv hA3 eA
  let qH : ↥H →* (↥H ⧸ B_H) := QuotientGroup.mk' B_H
  let O_H : Subgroup ↥H := O.subgroupOf H
  have hO_H_2 : IsPGroup 2 ↥O_H := CFSG.pCore_isPGroup.comap_subtype
  have hker : φH.ker = O_H := by
    ext h
    rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf]
    change π (H.subtype h) = 1 ↔ (H.subtype h : ↥c.L) ∈ O
    exact QuotientGroup.eq_one_iff (N := O) (H.subtype h)
  let ψ : ↥O_H →* (↥H ⧸ B_H) := qH.comp O_H.subtype
  have hψ_surj : Function.Surjective ψ := by
    intro y
    obtain ⟨h, rfl⟩ := QuotientGroup.mk'_surjective B_H y
    have hhC : φH h ∈ C := by
      rw [← hφH_range]
      exact ⟨h, rfl⟩
    have hhB : φH h ∈ B_H.map φH := by
      rwa [hBHmapC]
    obtain ⟨b, hbB, hbφ⟩ := Subgroup.mem_map.mp hhB
    have hzmem : b⁻¹ * h ∈ O_H := by
      rw [show O_H = φH.ker from hker.symm, MonoidHom.mem_ker, map_mul, map_inv, hbφ]
      group
    refine ⟨⟨b⁻¹ * h, hzmem⟩, ?_⟩
    change qH (b⁻¹ * h) = qH h
    have hbq : qH b = 1 := (QuotientGroup.eq_one_iff (N := B_H) b).mpr hbB
    rw [map_mul, map_inv, hbq, inv_one, one_mul]
  have hquot2 : IsPGroup 2 (↥H ⧸ B_H) :=
    IsPGroup.of_surjective hO_H_2 ψ hψ_surj
  have hA_H_le_BH : A_H ≤ B_H := by
    let M : Subgroup (↥H ⧸ B_H) := A_H.map qH
    have hM2 : IsPGroup 2 M := hquot2.to_subgroup M
    have hM3 : IsPGroup 3 M := hA_H_3.map qH
    have hdisj := IsPGroup.disjoint_of_ne 2 3 (by norm_num) M M hM2 hM3
    have hMbot : M = ⊥ := by simpa using hdisj.eq_bot
    have hleker : A_H ≤ qH.ker :=
      (Subgroup.map_eq_bot_iff (H := A_H) (f := qH)).mp hMbot
    have hqker : qH.ker = B_H := QuotientGroup.ker_mk' B_H
    rwa [hqker] at hleker
  have hA_L_le_BL : A_L ≤ B.subgroupOf c.L := by
    have hmap := Subgroup.map_mono (f := H.subtype) hA_H_le_BH
    rwa [Subgroup.map_subgroupOf_eq_of_le hA_L_H, hBH_map] at hmap
  have hAB : A ≤ B := by
    have hmap := Subgroup.map_mono (f := c.L.subtype) hA_L_le_BL
    rwa [Subgroup.map_subgroupOf_eq_of_le hA_L,
      Subgroup.map_subgroupOf_eq_of_le (sup_le hzp_le_L hI_le_L)] at hmap
  show A ≤ Subgroup.closure ({a} : Set G) ⊔ perfectCoreL c a
  rw [← Subgroup.zpowers_eq_closure]
  exact hAB

end
end CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82E3.ONan

namespace CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82E3.ONan
section
open CFSG.Open
open CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo.Sec4
open CFSG.RankThree.PartOne (IsStronglyPEmbedded)
open CFSG.LocalAnalysis.UniquenessCase.UC22 (Data IsSpor IsAlt)
open CFSG.ASVolI.ChIJK (IsWeaklyClosedIn)
open CFSG.Blueprint (LieModel)
variable {G : Type} [Group G] [Finite G]
variable {D : Data G}
variable (c : Ctx82E3 D) {P A : Subgroup G} {a : G}

theorem normalizer_suzukiComp''
    (hPSz : CFSG.RankThree.PartTwo.KFacts.KPSz) (hK8 : K8Cat)
    (hON : UCK.ThreeCover (fun Y _ => IsSpor Y .ONan) c.Lbar) (h7 : D.sig = {7})
    (hP : CFSG.ABGLocalTools.IsSylowOf 3 P D.M)
    (hNZ : Subgroup.normalizer ((zSub P c.L : Subgroup G) : Set G) ≤ D.M)
    (hA : CFSG.Open.IsElemAbelian 3 A) (hA27 : Nat.card A = 27) (hZA : zSub P c.L ≤ A)
    (hAPL : A ≤ P ⊓ c.L)
    (ha : a ∈ A) (haZ : a ∉ zSub P c.L)
    {J : Subgroup G} (hJ : J ∈ thetaComponentsAt 3 a) (h3 : ¬ 3 ∣ Nat.card J) :
    A ≤ Subgroup.normalizer (J : Set G) := by
  letI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have haPL : a ∈ P ⊓ c.L := hAPL ha
  have ha3 : orderOf a = 3 := by
    have ha1 : a ≠ 1 := by
      rintro rfl
      exact haZ (Subgroup.one_mem _)
    exact orderOf_eq_prime (hA.2 a ha) ha1
  have hK2 : K2ONanCentralizer := K2ONanCentralizer_holds
  have hF9in : F9Input c P a := f9_perfectCore' c hON hP haPL ha3 haZ hK2
  have hF9 : F9PerfectCore c P a := ⟨hF9in.1, hF9in.2.1, hF9in.2.2.1⟩
  have hgen : PerfectCoreGeneration c A a :=
    perfectCoreGeneration_holds' c hON hP hA hA27 hZA hAPL ha haZ
  have hP2 := perfectCoreL_structure' c hF9 hgen hON hA hA27 hAPL ha haZ
  have hP3 := pRank_seven_centralizer_le_one''' c hON h7 hP hNZ (hAPL ha) haZ
  have hP5 := perfect_threePrime_le_centralizerOnQuotient' c hPSz hK8 hON
  have hI := threePrimeComponent_normalized' c hPSz hK8 hON h7 hP hNZ hA hA27 hZA hAPL ha haZ
    hP2 hP3 hP5 hJ h3
  have haN : a ∈ Subgroup.normalizer (J : Set G) :=
    a_mem_normalizer_of_mem_thetaComponentsAt hJ
  have hsup : Subgroup.closure ({a} : Set G) ⊔ perfectCoreL c a ≤
      Subgroup.normalizer (J : Set G) :=
    sup_le ((Subgroup.closure_le (Subgroup.normalizer (J : Set G))).mpr
      (by rintro y rfl; exact haN)) hI
  exact hP2.2.2.2.trans hsup

end
end CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82E3.ONan

namespace CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82E3.ONan
section
open CFSG
open CFSG.RankThree.LocalRank
open CFSG.Open
open CFSG.RankThree CFSG.RankThree.PartTwo.Sec4
open CFSG.LocalAnalysis.UniquenessCase.UC22 (Data IsSpor)
open CFSG.LocalAnalysis.UniquenessCase.UCK (ThreeCover)
open CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82 (K3)
variable {G : Type} [Group G] [Finite G] {D : Data G}

theorem zSub_le_normalizer_thetaComponent'
    (hK3 : K3) (hK8 : K8Cat)
    (hPSz : CFSG.RankThree.PartTwo.KFacts.KPSz)
    (hSzB : Sz.SzBorel) (hSzO : Sz.SzOutOdd) (hSzF : Sz.SzFix) (c : Ctx82E3 D)
    (hON : ThreeCover (fun Y _ => IsSpor Y .ONan) c.Lbar) (h7 : D.sig = {7})
    {P : Subgroup G} (hP : CFSG.ABGLocalTools.IsSylowOf 3 P D.M)
    (hNZ : Subgroup.normalizer ((zSub P c.L : Subgroup G) : Set G) ≤ D.M)
    {e : G} (hP3 : CFSG.Open.pRank 7 (Subgroup.centralizer ({e} : Set G)) = 1)
    (hZ3 : ∀ J ∈ thetaComponentsAt 3 e, 3 ∣ Nat.card J →
      Nat.card (autThetaQuot (zSub P c.L) J) = 1)
    (he : e ∈ P ⊓ c.L) (he3 : orderOf e = 3) (heZ : e ∉ zSub P c.L)
    {L : Subgroup G} (hL : L ∈ thetaComponentsAt 3 e) :
    zSub P c.L ≤ Subgroup.normalizer (L : Set G) := by
  classical
  by_cases h3 : 3 ∣ Nat.card L
  · intro z hz
    have hzP : z ∈ P := (inf_le_left.trans inf_le_left : zSub P c.L ≤ P) hz
    have hzQ : z ∈ P ⊓ c.L := (inf_le_left : zSub P c.L ≤ P ⊓ c.L) hz
    have hza : z ∈ Subgroup.centralizer ({e} : Set G) := by
      rw [Subgroup.mem_centralizer_singleton_iff]
      exact (Subgroup.mem_centralizer_iff.mp hz.2 e he).symm
    exact normalizer_thetaComp_of_three_element' c hON h7 hP hNZ he he3 heZ hL h3 hza
      (hP.isPGroup.to_le (Subgroup.zpowers_le.mpr hzP))
  · obtain ⟨A, hAea, hA27, heA, hAPL, hZA⟩ :=
      exists_E27_frame_at_wPL9 hK3 c hON hP hNZ he heZ
    exact hZA.trans (normalizer_suzukiComp'' c hPSz hK8 hON h7 hP hNZ hAea hA27 hZA hAPL
      heA heZ hL h3)

theorem component_le_centralizer_zSubMap_wPL9
    (hK3 : K3) (hK8 : K8Cat)
    (hPSz : CFSG.RankThree.PartTwo.KFacts.KPSz)
    (hSzB : Sz.SzBorel) (hSzO : Sz.SzOutOdd) (hSzF : Sz.SzFix) (c : Ctx82E3 D)
    (hON : ThreeCover (fun Y _ => IsSpor Y .ONan) c.Lbar) (h7 : D.sig = {7})
    {P : Subgroup G} (hP : CFSG.ABGLocalTools.IsSylowOf 3 P D.M)
    (hNZ : Subgroup.normalizer ((zSub P c.L : Subgroup G) : Set G) ≤ D.M)
    {e : G} (hP3 : CFSG.Open.pRank 7 (Subgroup.centralizer ({e} : Set G)) = 1)
    (hZ3 : ∀ J ∈ thetaComponentsAt 3 e, 3 ∣ Nat.card J →
      Nat.card (autThetaQuot (zSub P c.L) J) = 1)
    (he : e ∈ P ⊓ c.L) (he3 : orderOf e = 3) (heZ : e ∉ zSub P c.L)
    {J : Subgroup (componentsQuot e)} {L₀ : Subgroup G}
    (hL₀ : L₀ ∈ thetaComponentsAt 3 e)
    (hL : (L₀.subgroupOf (thetaCen_wPL9 e)).map (thetaMap_wPL9 e) = J)
    (haut : Nat.card (autThetaQuot (zSub P c.L) L₀) = 1) :
    J ≤ Subgroup.centralizer
      ((((zSub P c.L).subgroupOf (thetaCen_wPL9 e)).map (thetaMap_wPL9 e)) :
        Set (componentsQuot e)) := by
  classical
  have hLK : L₀ ≤ thetaCen_wPL9 e := thetaComponent_le_cen_wPL9 hL₀
  have haut_bot : autThetaQuot (zSub P c.L) L₀ = ⊥ :=
    Subgroup.eq_bot_of_card_eq _ haut
  have hZN : ∀ z ∈ zSub P c.L, z ∈ Subgroup.normalizer (L₀ : Set G) :=
    zSub_le_normalizer_thetaComponent' hK3 hK8 hPSz hSzB hSzO hSzF c hON h7 hP hNZ
      hP3 hZ3 he he3 heZ hL₀
  intro j hj
  rw [← hL] at hj
  rw [Subgroup.mem_centralizer_iff]
  intro t ht
  obtain ⟨lK, hlK, rfl⟩ := Subgroup.mem_map.mp hj
  obtain ⟨zK, hzK, rfl⟩ := Subgroup.mem_map.mp ht
  set z : G := (zK : G) with hzdef
  set l0 : G := (lK : G) with hldef
  have hzZ' : z ∈ zSub P c.L := by
    simpa [z] using Subgroup.mem_subgroupOf.mp hzK
  have hl0 : l0 ∈ L₀ := by
    simpa [l0] using Subgroup.mem_subgroupOf.mp hlK
  have hzN : z ∈ Subgroup.normalizer (L₀ : Set G) := hZN z hzZ'
  let l : L₀ := ⟨l0, hl0⟩
  let zH : thetaCen_wPL9 e := ⟨z, zSub_le_thetaCen_wPL9 c he hzZ'⟩
  have hlEq : Subgroup.inclusion hLK l = lK := by ext; simp [l, l0]
  have hzEq : zH = zK := by ext; simp [zH, z]
  have hact := thetaMap_conj_eq_of_autThetaQuot_bot_wPL9 c he hL₀ hzZ' hzN haut_bot l
  have hleft : thetaMap_wPL9 e (Subgroup.inclusion hLK
      ((L₀.normalizerMonoidHom ⟨z, hzN⟩) l)) =
      thetaMap_wPL9 e ⟨z * l0 * z⁻¹, by
        refine (thetaCen_wPL9 e).mul_mem ((thetaCen_wPL9 e).mul_mem zH.2 ?_) ?_
        · exact hLK hl0
        · exact (thetaCen_wPL9 e).inv_mem zH.2⟩ := by
    congr 1
  have hright : thetaMap_wPL9 e (Subgroup.inclusion hLK l) =
      thetaMap_wPL9 e ⟨l0, hLK hl0⟩ := by
    congr 1
  rw [hleft, hright] at hact
  have hconj : (thetaMap_wPL9 e zH) * (thetaMap_wPL9 e ⟨l0, hLK hl0⟩) * (thetaMap_wPL9 e zH)⁻¹ =
      thetaMap_wPL9 e ⟨l0, hLK hl0⟩ := by
    have h1 : thetaMap_wPL9 e ⟨z * l0 * z⁻¹, by
        refine (thetaCen_wPL9 e).mul_mem ((thetaCen_wPL9 e).mul_mem zH.2 ?_) ?_
        · exact hLK hl0
        · exact (thetaCen_wPL9 e).inv_mem zH.2⟩ =
        (thetaMap_wPL9 e zH) * (thetaMap_wPL9 e ⟨l0, hLK hl0⟩) * (thetaMap_wPL9 e zH)⁻¹ := by
      have hz : (⟨z * l0 * z⁻¹, by
          refine (thetaCen_wPL9 e).mul_mem ((thetaCen_wPL9 e).mul_mem zH.2 ?_) ?_
          · exact hLK hl0
          · exact (thetaCen_wPL9 e).inv_mem zH.2⟩ : thetaCen_wPL9 e) =
          zH * ⟨l0, hLK hl0⟩ * zH⁻¹ := Subtype.ext rfl
      rw [hz]
      simp
    rw [← h1]
    exact hact
  have hcomm : (thetaMap_wPL9 e zH) * (thetaMap_wPL9 e ⟨l0, hLK hl0⟩) =
      (thetaMap_wPL9 e ⟨l0, hLK hl0⟩) * (thetaMap_wPL9 e zH) := by
    have h := congrArg (fun y => y * thetaMap_wPL9 e zH) hconj
    simpa [mul_assoc] using h
  rw [← hlEq, ← hzEq]
  exact hcomm

theorem component_le_normalizer_componentsImage_wPL9
    (hK3 : K3) (hK8 : K8Cat)
    (hPSz : CFSG.RankThree.PartTwo.KFacts.KPSz)
    (hSzB : Sz.SzBorel) (hSzO : Sz.SzOutOdd) (hSzF : Sz.SzFix) (c : Ctx82E3 D)
    (hON : ThreeCover (fun Y _ => IsSpor Y .ONan) c.Lbar) (h7 : D.sig = {7})
    {P : Subgroup G} (hP : CFSG.ABGLocalTools.IsSylowOf 3 P D.M)
    (hNZ : Subgroup.normalizer ((zSub P c.L : Subgroup G) : Set G) ≤ D.M)
    {e : G} (hP3 : CFSG.Open.pRank 7 (Subgroup.centralizer ({e} : Set G)) = 1)
    (hZ3 : ∀ J ∈ thetaComponentsAt 3 e, 3 ∣ Nat.card J →
      Nat.card (autThetaQuot (zSub P c.L) J) = 1)
    (he : e ∈ P ⊓ c.L) (he3 : orderOf e = 3) (heZ : e ∉ zSub P c.L)
    {J : Subgroup (componentsQuot e)} {L₀ : Subgroup G}
    (hL₀ : L₀ ∈ thetaComponentsAt 3 e)
    (hJ : (L₀.subgroupOf (thetaCen_wPL9 e)).map (thetaMap_wPL9 e) = J)
    (haut : Nat.card (autThetaQuot (zSub P c.L) L₀) = 1) :
    J ≤ Subgroup.normalizer
      ((((thetaCen_wPL9 e ⊓ CFSG.Open.pCoreOf 2 D.M).subgroupOf (thetaCen_wPL9 e)).map
        (thetaMap_wPL9 e)) : Set (componentsQuot e)) := by
  classical
  let K : Subgroup G := thetaCen_wPL9 e
  let Z : Subgroup G := zSub P c.L
  let W : Subgroup G := K ⊓ CFSG.Open.pCoreOf 2 D.M
  have hZK : Z ≤ K := zSub_le_thetaCen_wPL9 c he
  have hZP : Z ≤ P := by
    intro z hz
    have hz1 : z ∈ P ⊓ c.L := (inf_le_left : Z ≤ P ⊓ c.L) hz
    exact (inf_le_left : P ⊓ c.L ≤ P) hz1
  have hZ3grp : IsPGroup 3 Z := hP.isPGroup.to_le hZP
  haveI : Fact (IsPGroup 3 ↥(Z.subgroupOf K)) :=
    ⟨hZ3grp.comap_subtype⟩
  have hcop : Nat.Coprime 3 (Nat.card ↥(thetaCore_wPL9 e)) :=
    (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mpr
      (solvable_prime_complement_core_characterization (H := K) Nat.prime_three).2.2.1
  have hcent := component_le_centralizer_zSubMap_wPL9 hK3 hK8 hPSz hSzB hSzO hSzF c hON h7 hP hNZ
    hP3 hZ3 he he3 heZ hL₀ hJ haut
  have hcentralizer := centralizer_map_quotient_eq_map_centralizer (G := K) 3
    (Z.subgroupOf K) (thetaCore_wPL9 e) (by infer_instance) hcop
  have hCnorm := centralizer_zSub_le_normalizer_twoCore_wPL9 c hON hP hNZ he
  have hmapnorm : Subgroup.map (thetaMap_wPL9 e)
        (Subgroup.centralizer (Z.subgroupOf K : Subgroup K)) ≤
      Subgroup.normalizer (Subgroup.map (thetaMap_wPL9 e) (W.subgroupOf K)) :=
    (Subgroup.map_mono hCnorm).trans (Subgroup.le_normalizer_map (thetaMap_wPL9 e))
  refine hcent.trans ?_
  rw [hcentralizer]
  exact hmapnorm

theorem componentsStepTwoConfig_holds'
    (hK3 : K3) (hK8 : K8Cat)
    (hPSz : CFSG.RankThree.PartTwo.KFacts.KPSz)
    (hSzB : Sz.SzBorel) (hSzO : Sz.SzOutOdd) (hSzF : Sz.SzFix) (c : Ctx82E3 D)
    (hON : ThreeCover (fun Y _ => IsSpor Y .ONan) c.Lbar) (h7 : D.sig = {7})
    {P : Subgroup G} (hP : CFSG.ABGLocalTools.IsSylowOf 3 P D.M)
    (hNZ : Subgroup.normalizer ((zSub P c.L : Subgroup G) : Set G) ≤ D.M)
    {e : G} (hP3 : CFSG.Open.pRank 7 (Subgroup.centralizer ({e} : Set G)) = 1)
    (hZ3 : ∀ J ∈ thetaComponentsAt 3 e, 3 ∣ Nat.card J →
      Nat.card (autThetaQuot (zSub P c.L) J) = 1)
    (he : e ∈ P ⊓ c.L) (he3 : orderOf e = 3) (heZ : e ∉ zSub P c.L) :
    ComponentsStepTwoConfig (D := D) c P e := by
  classical
  intro J hJ htriv
  obtain ⟨L₀, hL₀, hLmap, haut⟩ := htriv
  have hLmap' : (L₀.subgroupOf (thetaCen_wPL9 e)).map (thetaMap_wPL9 e) = J := by
    simpa [componentsQuot, thetaQuot_wPL9, thetaCore_wPL9, thetaCen_wPL9, thetaMap_wPL9] using hLmap
  have hJN : J ≤ Subgroup.normalizer
      ((componentsImage (D := D) e : Subgroup (componentsQuot e)) :
        Set (componentsQuot e)) := by
    simpa [componentsImage, componentsQuot, thetaQuot_wPL9, thetaCore_wPL9, thetaCen_wPL9,
      thetaMap_wPL9]
      using component_le_normalizer_componentsImage_wPL9 hK3 hK8 hPSz hSzB hSzO hSzF c hON h7
        hP hNZ hP3 hZ3 he he3 heZ hL₀ hLmap' haut
  have hW2 : IsPGroup 2 (componentsImage (D := D) e) := by
    let W : Subgroup G := Subgroup.centralizer ({e} : Set G) ⊓ CFSG.Open.pCoreOf 2 D.M
    have hQ2 : IsPGroup 2 (CFSG.Open.pCoreOf 2 D.M) :=
      CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 D.M
    have hWQ : W ≤ CFSG.Open.pCoreOf 2 D.M := inf_le_right
    have hWQ2 : IsPGroup 2 (W.subgroupOf (CFSG.Open.pCoreOf 2 D.M)) :=
      hQ2.to_subgroup _
    have hW2G : IsPGroup 2 W :=
      hWQ2.of_equiv (Subgroup.subgroupOfEquivOfLe hWQ)
    have hW2H : IsPGroup 2 (W.subgroupOf (Subgroup.centralizer ({e} : Set G))) :=
      hW2G.of_equiv (Subgroup.subgroupOfEquivOfLe
        (inf_le_left : W ≤ Subgroup.centralizer ({e} : Set G))).symm
    let π : ↥(Subgroup.centralizer ({e} : Set G)) →* componentsQuot e :=
      QuotientGroup.mk' (CFSG.RankThree.LocalRank.aschbacherSolvableCore 3
        ↥(Subgroup.centralizer ({e} : Set G)))
    simpa [componentsImage, W, π] using IsPGroup.map hW2H π
  have hcomm : ⁅J, componentsImage (D := D) e⁆ = ⊥ :=
    components_step2_of_le_normalizer hJ hW2 hJN
  have hcomm' : ⁅componentsImage (D := D) e, J⁆ = ⊥ := by
    rw [Subgroup.commutator_comm]
    exact hcomm
  have hWcent : componentsImage (D := D) e ≤ Subgroup.centralizer (J : Set _) :=
    Subgroup.commutator_eq_bot_iff_le_centralizer.mp hcomm'
  exact ⟨hJN, hWcent.trans (Subgroup.centralizer_le_normalizer (J : Set (componentsQuot e)))⟩

end
end CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82E3.ONan
