module

public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82E3.ONanS6.WPH5b
public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82E3.ONanS6.WPS3b
import CFSG.GroupTheory.PGroup.CardCoprime

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82E3.ONan
section
open CFSG.Open
open CFSG.LocalAnalysis.UniquenessCase.UC22 (Data Opp IsSpor IsAlt)
open CFSG.RankThree.PartOne (IsStronglyPEmbedded)
open scoped commutatorElement
variable {G : Type} [Group G] [Finite G] {D : Data G}

theorem eq_bot_of_normal_coprime_three_of_isAlt_six_wPH6
    {Y : Type} [Group Y] [Finite Y] {Z : Subgroup Y} [Z.Normal]
    (hZcard : Nat.card ↥Z = 3) (hAlt : IsAlt (Y ⧸ Z) 6)
    {M : Subgroup Y} (hMnorm : M.Normal) (hMcop : Nat.Coprime 3 (Nat.card ↥M)) :
    M = ⊥ := by
  classical
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨e⟩ := hAlt
  let π : Y →* Y ⧸ Z := QuotientGroup.mk' Z
  haveI hsimple : IsSimpleGroup (Y ⧸ Z) := e.isSimpleGroup
  have hMπnorm : (M.map π).Normal := hMnorm.map π (QuotientGroup.mk'_surjective Z)
  haveI : (M.map π).Normal := hMπnorm
  rcases Subgroup.Normal.eq_bot_or_eq_top (M.map π) with hbot | htop
  · have hMZ : M ≤ Z := by
      have h := (Subgroup.map_eq_bot_iff M).mp hbot
      rwa [QuotientGroup.ker_mk'] at h
    have hdvd : Nat.card ↥M ∣ 3 := hZcard ▸ Subgroup.card_dvd_of_le hMZ
    rcases (Nat.dvd_prime Nat.prime_three).mp hdvd with h1 | h3
    · exact Subgroup.eq_bot_of_card_eq M h1
    · exfalso
      have h3dvd : 3 ∣ Nat.card ↥M := h3 ▸ dvd_rfl
      exact ((Nat.prime_three.coprime_iff_not_dvd).mp hMcop) h3dvd
  · exfalso
    have h3top : 3 ∣ Nat.card ↥(M.map π) := by
      rw [htop, Subgroup.card_top, Nat.card_congr e.toEquiv, nat_card_alternatingGroup,
        Nat.card_fin]
      norm_num
    have hc' : Nat.Coprime 3 (Nat.card ↥(M.map π)) :=
      Nat.Coprime.coprime_dvd_right (Subgroup.card_map_dvd M π) hMcop
    exact ((Nat.prime_three.coprime_iff_not_dvd).mp hc') h3top

theorem Step41ThreeCase_holds
    (hK2 : K2ONanCentralizer) (c : Ctx82E3 D)
    (hON : UCK.ThreeCover (fun Y _ => IsSpor Y .ONan) c.Lbar) (h7 : D.sig = {7})
    {P : Subgroup G} (hP : CFSG.ABGLocalTools.IsSylowOf 3 P D.M)
    {x : G} (hx : x ∈ P ⊓ c.L) (hx3 : orderOf x = 3) (hxZ : x ∉ zSub P c.L) :
    Step41ThreeCase c P x := by
  classical
  letI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  let H : Subgroup G := pH x
  let Dp : Subgroup ↥H := pD x
  let DG : Subgroup G := Dp.map H.subtype
  let I : Subgroup G := pI x c.L
  let N : Subgroup ↥c.L := CFSG.pCore 2 ↥c.L
  let q : ↥c.L →* c.Lbar := QuotientGroup.mk' N
  let xL : ↥c.L := ⟨x, hx.2⟩
  let xb : c.Lbar := q xL
  let C : Subgroup c.Lbar := Subgroup.centralizer ({xb} : Set c.Lbar)
  let J : Subgroup c.Lbar := ⁅C, C⁆
  let T : Subgroup G := I ⊓ (pDK x).map H.subtype
  have hIleL : I ≤ c.L := (CFSG.Quasithin.perfectCore_le _).trans inf_le_right
  have hIleH : I ≤ H := (CFSG.Quasithin.perfectCore_le _).trans inf_le_left
  have hxH : x ∈ H := by
    change x ∈ Subgroup.centralizer ({x} : Set G)
    exact Subgroup.mem_centralizer_singleton_iff.mpr (by simp)
  have hxL3 : orderOf xL = 3 := by
    rw [Subgroup.orderOf_mk, hx3]
  have hN2 : IsPGroup 2 ↥N := CFSG.pCore_isPGroup (p := 2) (G := ↥c.L)
  have hxLnotN : xL ∉ N := by
    intro hxN
    have h3dvd : 3 ∣ Nat.card ↥N := by
      have h := orderOf_dvd_natCard (⟨xL, hxN⟩ : ↥N)
      rwa [Subgroup.orderOf_mk, hxL3] at h
    exact CFSG.GroupTheory.not_dvd_card_of_isPGroup hN2 Nat.prime_three (by norm_num) h3dvd
  have hxb3 : orderOf xb = 3 := by
    have hdvd : orderOf xb ∣ 3 := by
      have h := orderOf_map_dvd q xL
      rwa [hxL3] at h
    rcases (Nat.dvd_prime Nat.prime_three).mp hdvd with h1 | h3
    · exfalso
      have hxb1 : xb = 1 := orderOf_eq_one_iff.mp h1
      exact hxLnotN ((QuotientGroup.eq_one_iff xL).mp hxb1)
    · exact h3
  have hxb_not_center : xb ∉ Subgroup.center c.Lbar := by
    simpa [xb, q, N, xL] using
      image_not_center_of_not_mem_zSub c hON hP hx.1 hx.2 hxZ
  obtain ⟨hCcard, hZleJ, hJcard, hCeq, hAlt⟩ :=
    hK2 c.Lbar hON xb hxb3 hxb_not_center
  let Z : Subgroup c.Lbar := Subgroup.center c.Lbar
  let ZJ : Subgroup ↥J := Z.subgroupOf J
  have hZJcard : Nat.card ↥ZJ = 3 := by
    change Nat.card ↥((Subgroup.center c.Lbar).subgroupOf J) = 3
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hZleJ).toEquiv]
    exact hON.2.1
  have hImgI : (I.subgroupOf c.L).map q = J := by
    simpa [I, N, q, J, C, xL, xb] using
      pI_image_eq_commutator' hK2 c hON hP hx hx3 hxZ
  have hφmem : ∀ i : ↥I, q (Subgroup.inclusion hIleL i) ∈ J := by
    intro i
    rw [← hImgI]
    exact Subgroup.mem_map.mpr
      ⟨Subgroup.inclusion hIleL i, Subgroup.mem_subgroupOf.mpr i.2, rfl⟩
  let φ : ↥I →* ↥J :=
    MonoidHom.codRestrict (q.comp (Subgroup.inclusion hIleL)) J hφmem
  have hφsurj : Function.Surjective φ := by
    intro j
    have hj : (j : c.Lbar) ∈ (I.subgroupOf c.L).map q := by
      rw [hImgI]
      exact j.2
    obtain ⟨iL, hiL, hqiL⟩ := Subgroup.mem_map.mp hj
    refine ⟨⟨iL.1, Subgroup.mem_subgroupOf.mp hiL⟩, ?_⟩
    exact Subtype.ext hqiL
  have hφker : φ.ker = CFSG.pCore 2 ↥I := by
    ext i
    constructor
    · intro hi
      rw [MonoidHom.mem_ker] at hi
      have hq : q (Subgroup.inclusion hIleL i) = 1 := by
        have h := congrArg (fun z : ↥J => (z : c.Lbar)) hi
        simpa [φ] using h
      have hN : Subgroup.inclusion hIleL i ∈ N := (QuotientGroup.eq_one_iff _).mp hq
      have hmem : (i : G) ∈ I ⊓ N.map c.L.subtype :=
        ⟨i.2, Subgroup.mem_map.mpr ⟨Subgroup.inclusion hIleL i, hN, rfl⟩⟩
      have hpc : (i : G) ∈ (CFSG.pCore 2 ↥I).map I.subtype := by
        rw [pCore_two_pI_image' hK2 c hON hP hx hx3 hxZ]
        exact hmem
      obtain ⟨j, hj, hji⟩ := Subgroup.mem_map.mp hpc
      have hij : i = j := Subtype.ext (by simpa using hji.symm)
      exact hij ▸ hj
    · intro hi
      rw [MonoidHom.mem_ker]
      apply Subtype.ext
      show q (Subgroup.inclusion hIleL i) = 1
      have hmem : (i : G) ∈ (CFSG.pCore 2 ↥I).map I.subtype :=
        Subgroup.mem_map.mpr ⟨i, hi, rfl⟩
      rw [pCore_two_pI_image' hK2 c hON hP hx hx3 hxZ] at hmem
      obtain ⟨n, hnN, hni⟩ := Subgroup.mem_map.mp hmem.2
      have hin : (Subgroup.inclusion hIleL i : ↥c.L) = n := Subtype.ext hni.symm
      rw [show q (Subgroup.inclusion hIleL i) = q n from congrArg q hin]
      exact (QuotientGroup.eq_one_iff n).mpr hnN
  change (T.subgroupOf c.L).map q = ⊥
  rw [Subgroup.map_eq_bot_iff]
  intro t ht
  have htG : (t : G) ∈ T := Subgroup.mem_subgroupOf.mp ht
  have htI : (t : G) ∈ I := htG.1
  obtain ⟨k, hk, hkt⟩ := Subgroup.mem_map.mp htG.2
  have hk' : k ∈ Dp ⊔ pK x := hk
  haveI : Dp.Normal := CFSG.pPrimeCore_normal
  obtain ⟨d, hd, z, hz, hdz⟩ := (Subgroup.mem_sup_of_normal_left).mp hk'
  let dG : G := H.subtype d
  let zG : G := H.subtype z
  have hdG : dG ∈ DG := Subgroup.mem_map_of_mem H.subtype hd
  have hzG : zG ∈ Subgroup.zpowers x := Subgroup.mem_subgroupOf.mp hz
  have ht_eq : dG * zG = (t : G) := by
    have h := congrArg H.subtype hdz
    simp only [Subgroup.coe_subtype, map_mul] at h
    exact h.trans hkt
  by_cases hz1 : zG = 1
  ·
    have htDG : (t : G) ∈ DG := by
      rw [← ht_eq, hz1, mul_one]
      exact hdG
    let K : Subgroup ↥I := (pD x).comap (Subgroup.inclusion hIleH)
    have hKmem : ∀ i : ↥I, i ∈ K ↔ (i : G) ∈ DG := by
      intro i
      rw [show K = (pD x).comap (Subgroup.inclusion hIleH) from rfl, Subgroup.mem_comap]
      constructor
      · intro hi
        exact Subgroup.mem_map.mpr ⟨Subgroup.inclusion hIleH i, hi, rfl⟩
      · rintro ⟨d', hd', hdi⟩
        have hEq : Subgroup.inclusion hIleH i = d' := Subtype.ext (by simpa using hdi.symm)
        rwa [hEq]
    have hKn : K.Normal :=
      Subgroup.Normal.comap (CFSG.pPrimeCore_normal (p := 3) (G := ↥H)) (Subgroup.inclusion hIleH)
    have hKcop : Nat.Coprime 3 (Nat.card ↥K) := by
      have hdvd := Subgroup.card_comap_dvd_of_injective (pD x) (Subgroup.inclusion hIleH)
        (Subgroup.inclusion_injective hIleH)
      exact Nat.Coprime.coprime_dvd_right hdvd CFSG.pPrimeCore_coprime_card
    have hKimg : (K.map φ).Normal := hKn.map φ hφsurj
    have hKimgcop : Nat.Coprime 3 (Nat.card ↥(K.map φ)) :=
      Nat.Coprime.coprime_dvd_right (Subgroup.card_map_dvd K φ) hKcop
    have hKimgbot : K.map φ = ⊥ :=
      eq_bot_of_normal_coprime_three_of_isAlt_six_wPH6 (Z := ZJ) hZJcard hAlt hKimg hKimgcop
    have htK : (⟨(t : G), htI⟩ : ↥I) ∈ K := (hKmem _).mpr htDG
    have hker : (⟨(t : G), htI⟩ : ↥I) ∈ φ.ker := by
      rw [MonoidHom.mem_ker]
      have hmem : φ ⟨(t : G), htI⟩ ∈ K.map φ := Subgroup.mem_map_of_mem φ htK
      rw [hKimgbot] at hmem
      exact Subgroup.mem_bot.mp hmem
    rw [hφker] at hker
    rw [MonoidHom.mem_ker]
    have hNmem : (t : G) ∈ N.map c.L.subtype := by
      have hmemI : (t : G) ∈ I ⊓ N.map c.L.subtype := by
        rw [← pCore_two_pI_image' hK2 c hON hP hx hx3 hxZ]
        exact Subgroup.mem_map.mpr ⟨⟨(t : G), htI⟩, hker, rfl⟩
      exact hmemI.2
    obtain ⟨n, hnN, hnt⟩ := Subgroup.mem_map.mp hNmem
    have hin : (t : ↥c.L) = n := Subtype.ext hnt.symm
    rw [show q (t : ↥c.L) = q n from congrArg q hin]
    exact (QuotientGroup.eq_one_iff n).mpr hnN
  ·
    exfalso
    have hdH : dG ∈ H := Subgroup.map_subtype_le _ hdG
    have hcommdx : dG * x = x * dG :=
      Subgroup.mem_centralizer_singleton_iff.mp hdH
    have hcomm : Commute dG zG := by
      obtain ⟨n, hn⟩ := Subgroup.mem_zpowers_iff.mp hzG
      rw [← hn]
      exact (show Commute dG x from hcommdx).zpow_right n
    have hcopD : Nat.Coprime 3 (Nat.card ↥Dp) := CFSG.pPrimeCore_coprime_card
    have hcopDG : Nat.Coprime 3 (Nat.card ↥DG) := by
      rw [show DG = Dp.map H.subtype from rfl,
        Subgroup.card_map_of_injective (K := Dp) H.subtype_injective]
      exact hcopD
    have hcopd : Nat.Coprime 3 (orderOf dG) :=
      Nat.Coprime.coprime_dvd_right (Subgroup.orderOf_dvd_natCard DG hdG) hcopDG
    have hzord : orderOf zG = 3 := by
      have hdvd : orderOf zG ∣ 3 := by
        have h := Subgroup.orderOf_dvd_natCard (Subgroup.zpowers x) hzG
        rwa [Nat.card_zpowers, hx3] at h
      rcases (Nat.dvd_prime Nat.prime_three).mp hdvd with h1 | h3
      · exact absurd (orderOf_eq_one_iff.mp h1) hz1
      · exact h3
    have htpow : (t : G) ^ orderOf dG = zG ^ orderOf dG := by
      rw [← ht_eq, hcomm.mul_pow, pow_orderOf_eq_one, one_mul]
    have hz'ne : zG ^ orderOf dG ≠ 1 := by
      intro h1
      have hdvd : orderOf zG ∣ orderOf dG := orderOf_dvd_of_pow_eq_one h1
      rw [hzord] at hdvd
      exact ((Nat.prime_three.coprime_iff_not_dvd).mp hcopd) hdvd
    have hz'T : zG ^ orderOf dG ∈ T := by
      rw [← htpow]
      exact T.pow_mem htG (orderOf dG)
    have hz'zp : zG ^ orderOf dG ∈ Subgroup.zpowers x :=
      (Subgroup.zpowers x).pow_mem hzG (orderOf dG)
    let S : Subgroup G := Subgroup.zpowers x
    have hS3 : Nat.card ↥S = 3 := by
      rw [show S = Subgroup.zpowers x from rfl, Nat.card_zpowers, hx3]
    have hmem := mem_zpowers_of_prime_card (G := ↥S) (p := 3) (h := hS3)
      (g := ⟨zG ^ orderOf dG, hz'zp⟩) (g' := ⟨x, Subgroup.mem_zpowers x⟩) (by
        intro h1
        exact hz'ne (congrArg Subtype.val h1))
    obtain ⟨m, hm⟩ := Subgroup.mem_zpowers_iff.mp hmem
    have hxzp : x ∈ Subgroup.zpowers (zG ^ orderOf dG) := by
      rw [Subgroup.mem_zpowers_iff]
      exact ⟨m, by simpa using congrArg (fun u : ↥S => (u : G)) hm⟩
    have hxT : x ∈ T := Subgroup.zpowers_le.mpr hz'T hxzp
    have hxI : x ∈ I := hxT.1
    have hxbJ : xb ∈ J := by
      have hmem' : xb ∈ (I.subgroupOf c.L).map q :=
        Subgroup.mem_map_of_mem q (Subgroup.mem_subgroupOf.mpr hxI)
      rwa [hImgI] at hmem'
    have hzC : Subgroup.zpowers xb ≤ Subgroup.centralizer (C : Set c.Lbar) := by
      intro v hv
      rw [Subgroup.mem_centralizer_iff]
      intro w hw
      obtain ⟨n, hn⟩ := Subgroup.mem_zpowers_iff.mp hv
      rw [← hn]
      have hw' : w * xb = xb * w := Subgroup.mem_centralizer_singleton_iff.mp hw
      exact (show Commute w xb from hw').zpow_right n
    have hzJ : Subgroup.zpowers xb ≤ Subgroup.centralizer (J : Set c.Lbar) := by
      intro v hv
      rw [Subgroup.mem_centralizer_iff]
      intro w hw
      exact Subgroup.mem_centralizer_iff.mp (hzC hv) w (Subgroup.commutator_le_self C hw)
    have hznorm : Subgroup.zpowers xb ≤ Subgroup.normalizer (J : Set c.Lbar) :=
      hzJ.trans (Subgroup.centralizer_le_normalizer _)
    have hdisj : Subgroup.zpowers xb ⊓ J = ⊥ := by
      have hcard :=
        CFSG.GroupTheory.CoprimeActionSupport.NormalSubgroupSylowJoin.card_sup_mul_card_inf
          (H := Subgroup.zpowers xb) (K := J) hznorm
      rw [← hCeq, hCcard, hJcard, Nat.card_zpowers, hxb3] at hcard
      have h1 : Nat.card ↥(Subgroup.zpowers xb ⊓ J) = 1 := by omega
      exact Subgroup.eq_bot_of_card_eq _ h1
    have hmem_bot : xb ∈ (⊥ : Subgroup c.Lbar) := by
      rw [← hdisj]
      exact ⟨Subgroup.mem_zpowers xb, hxbJ⟩
    have hxb1 : xb = 1 := Subgroup.mem_bot.mp hmem_bot
    rw [hxb1, orderOf_one] at hxb3
    omega

theorem Step42Surjection_holds
    (hK2 : K2ONanCentralizer) (c : Ctx82E3 D)
    (hON : UCK.ThreeCover (fun Y _ => IsSpor Y .ONan) c.Lbar) (h7 : D.sig = {7})
    {P : Subgroup G} (hP : CFSG.ABGLocalTools.IsSylowOf 3 P D.M)
    {x : G} (hx : x ∈ P ⊓ c.L) (hx3 : orderOf x = 3) (hxZ : x ∉ zSub P c.L) :
    Step42Surjection c hx := by
  classical
  letI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  let H : Subgroup G := pH x
  let I : Subgroup G := pI x c.L
  let N : Subgroup ↥c.L := CFSG.pCore 2 ↥c.L
  let q : ↥c.L →* c.Lbar := QuotientGroup.mk' N
  let qD : ↥H →* pX x := QuotientGroup.mk' (pDK x)
  let xL : ↥c.L := ⟨x, hx.2⟩
  let xb : c.Lbar := q xL
  let C : Subgroup c.Lbar := Subgroup.centralizer ({xb} : Set c.Lbar)
  let J : Subgroup c.Lbar := ⁅C, C⁆
  have hIleL : I ≤ c.L := (CFSG.Quasithin.perfectCore_le _).trans inf_le_right
  have hIleH : I ≤ H := (CFSG.Quasithin.perfectCore_le _).trans inf_le_left
  have hImgI : (I.subgroupOf c.L).map q = J := by
    simpa [I, N, q, J, C, xL, xb] using
      pI_image_eq_commutator' hK2 c hON hP hx hx3 hxZ
  have hφmem : ∀ i : ↥I, q (Subgroup.inclusion hIleL i) ∈ J := by
    intro i
    rw [← hImgI]
    exact Subgroup.mem_map.mpr
      ⟨Subgroup.inclusion hIleL i, Subgroup.mem_subgroupOf.mpr i.2, rfl⟩
  let φ : ↥I →* ↥J :=
    MonoidHom.codRestrict (q.comp (Subgroup.inclusion hIleL)) J hφmem
  have hφsurj : Function.Surjective φ := by
    intro j
    have hj : (j : c.Lbar) ∈ (I.subgroupOf c.L).map q := by
      rw [hImgI]
      exact j.2
    obtain ⟨iL, hiL, hqiL⟩ := Subgroup.mem_map.mp hj
    refine ⟨⟨iL.1, Subgroup.mem_subgroupOf.mp hiL⟩, ?_⟩
    exact Subtype.ext hqiL
  have hφker : φ.ker = CFSG.pCore 2 ↥I := by
    ext i
    constructor
    · intro hi
      rw [MonoidHom.mem_ker] at hi
      have hq : q (Subgroup.inclusion hIleL i) = 1 := by
        have h := congrArg (fun z : ↥J => (z : c.Lbar)) hi
        simpa [φ] using h
      have hN : Subgroup.inclusion hIleL i ∈ N := (QuotientGroup.eq_one_iff _).mp hq
      have hmem : (i : G) ∈ I ⊓ N.map c.L.subtype :=
        ⟨i.2, Subgroup.mem_map.mpr ⟨Subgroup.inclusion hIleL i, hN, rfl⟩⟩
      have hpc : (i : G) ∈ (CFSG.pCore 2 ↥I).map I.subtype := by
        rw [pCore_two_pI_image' hK2 c hON hP hx hx3 hxZ]
        exact hmem
      obtain ⟨j, hj, hji⟩ := Subgroup.mem_map.mp hpc
      have hij : i = j := Subtype.ext (by simpa using hji.symm)
      exact hij ▸ hj
    · intro hi
      rw [MonoidHom.mem_ker]
      apply Subtype.ext
      show q (Subgroup.inclusion hIleL i) = 1
      have hmem : (i : G) ∈ (CFSG.pCore 2 ↥I).map I.subtype :=
        Subgroup.mem_map.mpr ⟨i, hi, rfl⟩
      rw [pCore_two_pI_image' hK2 c hON hP hx hx3 hxZ] at hmem
      obtain ⟨n, hnN, hni⟩ := Subgroup.mem_map.mp hmem.2
      have hin : (Subgroup.inclusion hIleL i : ↥c.L) = n := Subtype.ext hni.symm
      rw [show q (Subgroup.inclusion hIleL i) = q n from congrArg q hin]
      exact (QuotientGroup.eq_one_iff n).mpr hnN
  have hStep : Step41ThreeCase c P x :=
    Step41ThreeCase_holds hK2 c hON h7 hP hx hx3 hxZ
  have hTbot : ((I ⊓ (pDK x).map H.subtype).subgroupOf c.L).map q = ⊥ := by
    simpa [Step41ThreeCase, I, H, q, N] using hStep
  have hψmem : ∀ i : ↥I, qD (Subgroup.inclusion hIleH i) ∈ pIbar x c.L := by
    intro i
    change qD (Subgroup.inclusion hIleH i) ∈
      ((pI x c.L).subgroupOf (pH x)).map (QuotientGroup.mk' (pDK x))
    exact Subgroup.mem_map.mpr
      ⟨Subgroup.inclusion hIleH i, Subgroup.mem_subgroupOf.mpr i.2, rfl⟩
  let ψ : ↥I →* ↥(pIbar x c.L) :=
    MonoidHom.codRestrict (qD.comp (Subgroup.inclusion hIleH)) _ hψmem
  have hψsurj : Function.Surjective ψ := by
    intro y
    obtain ⟨iH, hiH, hqiH⟩ := Subgroup.mem_map.mp y.2
    refine ⟨⟨iH.1, Subgroup.mem_subgroupOf.mp hiH⟩, ?_⟩
    exact Subtype.ext hqiH
  have hψker_le : ψ.ker ≤ φ.ker := by
    intro i hi
    rw [MonoidHom.mem_ker] at hi ⊢
    have hqD : qD (Subgroup.inclusion hIleH i) = 1 := by
      have h := congrArg (fun z : ↥(pIbar x c.L) => (z : pX x)) hi
      simpa [ψ] using h
    have hmemT : (i : G) ∈ I ⊓ (pDK x).map H.subtype := by
      refine ⟨i.2, ?_⟩
      have hmemH : Subgroup.inclusion hIleH i ∈ pDK x := by
        have h := (QuotientGroup.eq_one_iff (N := pDK x)
          (Subgroup.inclusion hIleH i)).mp hqD
        simpa [qD] using h
      exact Subgroup.mem_map.mpr ⟨Subgroup.inclusion hIleH i, hmemH, rfl⟩
    have hmemL : (⟨(i : G), hIleL i.2⟩ : ↥c.L) ∈
        ((I ⊓ (pDK x).map H.subtype).subgroupOf c.L) :=
      Subgroup.mem_subgroupOf.mpr hmemT
    have h1 : q (⟨(i : G), hIleL i.2⟩ : ↥c.L) = 1 := by
      have h := Subgroup.mem_map_of_mem q hmemL
      rw [hTbot] at h
      exact Subgroup.mem_bot.mp h
    have h2 : q (Subgroup.inclusion hIleL i) = 1 := by
      rw [show Subgroup.inclusion hIleL i = ⟨(i : G), hIleL i.2⟩ from rfl]
      exact h1
    exact Subtype.ext h2
  let K : Subgroup ↥I := ψ.ker
  have hKle : K ≤ φ.ker := hψker_le
  let qlift : ↥I ⧸ K →* ↥J := QuotientGroup.lift K φ hKle
  have hqlift_surj : Function.Surjective qlift := by
    intro j
    obtain ⟨i, hi⟩ := hφsurj j
    exact ⟨QuotientGroup.mk i, by simpa [qlift] using hi⟩
  let eRange : ↥I ⧸ K ≃* ↥(ψ.range) := QuotientGroup.quotientKerEquivRange ψ
  have hrange_top : ψ.range = ⊤ := by
    ext y
    exact ⟨fun _ => Subgroup.mem_top y, fun _ => by
      obtain ⟨i, hi⟩ := hψsurj y
      exact ⟨i, hi⟩⟩
  let eTop : ↥(ψ.range) ≃* ↥(pIbar x c.L) :=
    hrange_top ▸ Subgroup.topEquiv
  let e : ↥(pIbar x c.L) ≃* ↥I ⧸ K := (eRange.trans eTop).symm
  refine ⟨qlift.comp e.toMonoidHom, ?_⟩
  intro j
  obtain ⟨x', hx'⟩ := hqlift_surj j
  refine ⟨e.symm x', ?_⟩
  change qlift (e (e.symm x')) = j
  rw [MulEquiv.apply_symm_apply]
  exact hx'

theorem propositionH_step41'''
    (hK2 : K2ONanCentralizer) (c : Ctx82E3 D)
    (hON : UCK.ThreeCover (fun Y _ => IsSpor Y .ONan) c.Lbar) (h7 : D.sig = {7})
    {P : Subgroup G} (hP : CFSG.ABGLocalTools.IsSylowOf 3 P D.M)
    {x : G} (hx : x ∈ P ⊓ c.L) (hx3 : orderOf x = 3) (hxZ : x ∉ zSub P c.L) :
    pI x c.L ⊓ ((pDK x).map (pH x).subtype) ≤
      (CFSG.pCore 2 ↥(pI x c.L)).map (pI x c.L).subtype := by
  exact propositionH_step41'' hK2 c hON h7 hP hx hx3 hxZ
    (Step41ThreeCase_holds hK2 c hON h7 hP hx hx3 hxZ)

end
end CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82E3.ONan
