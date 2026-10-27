module

public import CFSG.GroupTheory.PRankLeOfSylowLe
public import CFSG.LieType.BorelTits.Basic
public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82E3.Context
public import CFSG.RankThree.PartTwo.Sec6.Item612Basic
public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82E3.ONanS6.WPH2
public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82E3.ONanS6.WPL
public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82E3.ONanS6.WPL3
public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82E3.ONanS6.WPR
public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82E3.ONanS6.WPS
public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82E3.ONanS6.WPS2a
public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82E3.ONanS6.WPZ
public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82E3.ONanS6.WPZ2b
public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82E3.ONanS6.WPZs
public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82E3.ONanS6.WS6

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82E3.ONan
section
open CFSG.Open
open CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo.Sec4
open CFSG.RankThree.PartOne (IsStronglyPEmbedded)
open CFSG.LocalAnalysis.UniquenessCase.UC22 (Data IsSpor)
open CFSG.LocalAnalysis.UniquenessCase.UCK (ThreeCover)
open CFSG.ASVolI.ChIJK (IsWeaklyClosedIn)
variable {G : Type} [Group G] [Finite G]
variable {D : Data G}

theorem pRank_three_le_of_onan' (c : Ctx82E3 D)
    (hON : UCK.ThreeCover (fun Y _ => IsSpor Y .ONan) c.Lbar)
    {P : Subgroup G} (hP : CFSG.ABGLocalTools.IsSylowOf 3 P D.M)
    (hNZ : Subgroup.normalizer ((zSub P c.L : Subgroup G) : Set G) ≤ D.M) :
    CFSG.Open.pRank 3 (⊤ : Subgroup G) ≤ 3 := by
  have hPt : CFSG.ABGLocalTools.IsSylowOf 3 P ⊤ :=
    isSylowOf_top_of_normalizer_le hP (normalizer_sylow_le_M_of_onan c hON hP hNZ)
  have hle := CFSG.pRank_le_of_isSylowOf_le Nat.prime_three (le_top : P ≤ ⊤) hPt hP.le
  rw [c.pRank_three_M] at hle
  exact hle

end
end CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82E3.ONan

namespace CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82E3.ONan
section
open CFSG.Open
open CFSG.RankThree CFSG.RankThree.LocalRank
open CFSG.LocalAnalysis.UniquenessCase.UC22 (Data IsSpor)
open CFSG.LocalAnalysis.UniquenessCase.UCK (ThreeCover)
open scoped IsMulCommutative
variable {G : Type} [Group G] [Finite G] {D : Data G}
variable (c : Ctx82E3 D) {P A : Subgroup G} {a : G}

theorem normalizer_thetaComp_of_three_element'
    (hON : UCK.ThreeCover (fun Y _ => IsSpor Y .ONan) c.Lbar) (h7 : D.sig = {7})
    (hP : CFSG.ABGLocalTools.IsSylowOf 3 P D.M)
    (hNZ : Subgroup.normalizer ((zSub P c.L : Subgroup G) : Set G) ≤ D.M)
    (haL : a ∈ P ⊓ c.L) (ha3 : orderOf a = 3)
    (haZ : a ∉ zSub P c.L)
    {J : Subgroup G} (hJ : J ∈ thetaComponentsAt 3 a) (h3 : 3 ∣ Nat.card J)
    {u : G} (hu : u ∈ Subgroup.centralizer ({a} : Set G)) (hu3 : IsPGroup 3 (Subgroup.zpowers u)) :
    u ∈ Subgroup.normalizer (J : Set G) := by
  classical
  have hrankG : CFSG.Open.pRank 3 (⊤ : Subgroup G) ≤ 3 :=
    pRank_three_le_of_onan' c hON hP hNZ
  set C : Subgroup G := Subgroup.centralizer ({a} : Set G) with hC
  obtain ⟨L, hL, hLJ⟩ := hJ
  have hLJ' : L.map C.subtype = J := hLJ
  have haC : a ∈ C := by
    rw [hC, Subgroup.mem_centralizer_singleton_iff]
  have hz_center : (⟨a, haC⟩ : C) ∈ Subgroup.center C := by
    rw [Subgroup.mem_center_iff]
    intro g
    apply Subtype.ext
    exact Subgroup.mem_centralizer_singleton_iff.mp g.2
  have hzo : orderOf (⟨a, haC⟩ : C) = 3 := by
    rw [Subgroup.orderOf_mk]
    exact ha3
  have hcardL : Nat.card L = Nat.card J := by
    rw [← hLJ']
    exact (Subgroup.card_map_of_injective C.subtype_injective).symm
  have h3L : 3 ∣ Nat.card L := by
    rw [hcardL]
    exact h3
  obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp hu3
  have huord : orderOf u = 3 ^ k := by rwa [Nat.card_zpowers] at hk
  have huC_ord : ∃ k : ℕ, orderOf (⟨u, hu⟩ : C) = 3 ^ k := by
    refine ⟨k, ?_⟩
    rw [Subgroup.orderOf_mk]
    exact huord
  have hrankC : CFSG.Open.pRank 3 (⊤ : Subgroup C) ≤ 3 :=
    (CFSG.SectionRank.pRank_top_le_of_injective (p := 3) Nat.prime_three.one_lt C.subtype
      C.subtype_injective).trans hrankG
  have huN := pElement_normalizes_thetaComponent_of_pRank_three Nat.prime_three (by norm_num)
    hz_center hzo hL h3L huC_ord hrankC
  have huNm : L.map (MulAut.conj (⟨u, hu⟩ : C)).toMonoidHom = L := by
    have h := huN
    rw [Subgroup.mem_normalizer_iff_map_conj_eq] at h
    exact h
  have hcomp : ((MulAut.conj u).toMonoidHom).comp C.subtype =
      C.subtype.comp ((MulAut.conj (⟨u, hu⟩ : C)).toMonoidHom) := by
    ext c
    rfl
  have h1 : J.map (MulAut.conj u).toMonoidHom =
      (L.map (MulAut.conj (⟨u, hu⟩ : C)).toMonoidHom).map C.subtype := by
    rw [← hLJ', Subgroup.map_map, Subgroup.map_map, hcomp]
  rw [Subgroup.mem_normalizer_iff_map_conj_eq]
  change Subgroup.map (MulEquiv.toMonoidHom (MulAut.conj u)) J = J
  rw [h1, huNm, hLJ']

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
open scoped commutatorElement Pointwise
variable {G : Type} [Group G] [Finite G]
variable {D : Data G}
variable (c : Ctx82E3 D) {P A : Subgroup G} {a : G}

theorem zSub_le_normalizer_of_threeComp
    (hON : UCK.ThreeCover (fun Y _ => IsSpor Y .ONan) c.Lbar) (h7 : D.sig = {7})
    (hP : CFSG.ABGLocalTools.IsSylowOf 3 P D.M)
    (hNZ : Subgroup.normalizer ((zSub P c.L : Subgroup G) : Set G) ≤ D.M)
    (haL : a ∈ P ⊓ c.L) (ha3 : orderOf a = 3) (haZ : a ∉ zSub P c.L)
    {J : Subgroup G} (hJ : J ∈ thetaComponentsAt 3 a) (h3 : 3 ∣ Nat.card J) :
    zSub P c.L ≤ Subgroup.normalizer (J : Set G) := by
  intro z hzZ
  have hzP : z ∈ P := (inf_le_left.trans inf_le_left : zSub P c.L ≤ P) hzZ
  have hza : z ∈ Subgroup.centralizer ({a} : Set G) := by
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact (Subgroup.mem_centralizer_iff.mp hzZ.2 a haL).symm
  exact normalizer_thetaComp_of_three_element' c hON h7 hP hNZ haL ha3 haZ hJ h3 hza
    (hP.isPGroup.to_le (Subgroup.zpowers_le.mpr hzP))

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
open scoped commutatorElement Pointwise
variable {G : Type} [Group G] [Finite G]
variable {D : Data G}
variable (c : Ctx82E3 D) {P A : Subgroup G} {a : G}

theorem Ia_le_normalizer_of_f9
    (hF9 : F9Input c P a)
    (hON : UCK.ThreeCover (fun Y _ => IsSpor Y .ONan) c.Lbar) (h7 : D.sig = {7})
    (hP : CFSG.ABGLocalTools.IsSylowOf 3 P D.M)
    (hNZ : Subgroup.normalizer ((zSub P c.L : Subgroup G) : Set G) ≤ D.M)
    (haL : a ∈ P ⊓ c.L) (ha3 : orderOf a = 3) (haZ : a ∉ zSub P c.L)
    {J : Subgroup G} (hJ : J ∈ thetaComponentsAt 3 a) (h3 : 3 ∣ Nat.card J) :
    Ia c a ≤ Subgroup.normalizer (J : Set G) := by
  rw [hF9.2.2.2]
  refine (Subgroup.closure_le _).mpr ?_
  rintro x ⟨hxI, hx3⟩
  have hxC : x ∈ Subgroup.centralizer ({a} : Set G) := (Ia_le c a hxI).2
  refine normalizer_thetaComp_of_three_element' c hON h7 hP hNZ haL ha3 haZ hJ h3 hxC ?_
  exact IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hx3]; norm_num)

theorem dvd_1080_of_f9
    (hF9 : F9Input c P a)
    (hON : UCK.ThreeCover (fun Y _ => IsSpor Y .ONan) c.Lbar) (h7 : D.sig = {7})
    (hP : CFSG.ABGLocalTools.IsSylowOf 3 P D.M)
    (hNZ : Subgroup.normalizer ((zSub P c.L : Subgroup G) : Set G) ≤ D.M)
    (haL : a ∈ P ⊓ c.L) (ha3 : orderOf a = 3) (haZ : a ∉ zSub P c.L)
    {J : Subgroup G} (hJ : J ∈ thetaComponentsAt 3 a) (h3 : 3 ∣ Nat.card J)
    {z : G} (hzZ : z ∈ zSub P c.L) (hz3 : orderOf z = 3)
    (hzN : z ∈ Subgroup.normalizer (J : Set G))
    (hSch : CFSG.AGLEmbedding.KFactCatalogSchreier)
    (hπ : thetaQuotMulAut J (J.normalizerMonoidHom ⟨z, hzN⟩) ≠ 1) :
    1080 ∣ Nat.card (J0 J) := by
  classical
  haveI hIperf : Group.IsPerfect ↥(Ia c a) := Ia_perfect c a
  have hIJ : Ia c a ≤ Subgroup.normalizer (J : Set G) :=
    Ia_le_normalizer_of_f9 c hF9 hON h7 hP hNZ haL ha3 haZ hJ h3
  have hzI : z ∈ Ia c a := hF9.2.1 hzZ
  have hinner : (piJ c hIJ).range ≤
      (MulAut.conj : Jtilde J →* MulAut (Jtilde J)).range :=
    piJ_range_le_conj c hIJ hJ ha3 hSch
  have hconjcard : Nat.card (MulAut.conj : Jtilde J →* MulAut (Jtilde J)).range =
      Nat.card (J0 J) := card_conj_range
  suffices h1080 : 1080 ∣ Nat.card (piJ c hIJ).range by
    refine h1080.trans ?_
    rw [← hconjcard]
    exact Subgroup.card_dvd_of_le hinner
  let O : Subgroup ↥(Ia c a) := CFSG.pCore 2 ↥(Ia c a)
  have hO2 : IsPGroup 2 O := CFSG.pCore_isPGroup
  let φ : ↥(Ia c a) →* MulAut (Jtilde J) := piJ c hIJ
  let A : Subgroup (MulAut (Jtilde J)) := φ.range
  let Q : Subgroup A := O.map φ.rangeRestrict
  haveI hQnorm : Q.Normal :=
    (CFSG.pCore_normal (p := 2) (G := ↥(Ia c a))).map φ.rangeRestrict
      φ.rangeRestrict_surjective
  let T := ↥(Ia c a) ⧸ O
  have hTtriple : IsTripleCover T ↥(alternatingGroup (Fin 6)) := hF9.1
  have hTperf : Group.IsPerfect T :=
    Group.IsPerfect.ofSurjective (f := QuotientGroup.mk' O) (QuotientGroup.mk'_surjective O)
  let ψ : ↥(Ia c a) →* A ⧸ Q := (QuotientGroup.mk' Q).comp φ.rangeRestrict
  have hOker : O ≤ ψ.ker := by
    intro x hx
    rw [MonoidHom.mem_ker]
    have hxQ : (φ.rangeRestrict x : A) ∈ Q := Subgroup.mem_map_of_mem φ.rangeRestrict hx
    have hmk : (QuotientGroup.mk (φ.rangeRestrict x) : A ⧸ Q) = 1 :=
      (QuotientGroup.eq_one_iff _).mpr hxQ
    simpa [ψ] using hmk
  let g : T →* A ⧸ Q := QuotientGroup.lift (N := O) ψ hOker
  have hψsurj : Function.Surjective ψ := by
    intro t
    obtain ⟨a, rfl⟩ := QuotientGroup.mk'_surjective Q t
    obtain ⟨x, hx⟩ := φ.rangeRestrict_surjective a
    exact ⟨x, by simp [ψ, hx]⟩
  have hgsurj : Function.Surjective g :=
    QuotientGroup.lift_surjective_of_surjective (N := O) ψ hψsurj hOker
  let zI : ↥(Ia c a) := ⟨z, hzI⟩
  let ζ : T := QuotientGroup.mk zI
  have hζZ : ζ ∈ Subgroup.center T := by
    rw [Subgroup.mem_center_iff]
    intro t
    obtain ⟨y, rfl⟩ := QuotientGroup.mk_surjective t
    have hmem : ⁅y, zI⁆ ∈ O := by
      have hG : ⁅(y : G), z⁆ ∈ CFSG.Open.pCoreOf 2 (Ia c a) :=
        (Subgroup.commutator_le.mp hF9.2.2.1) y y.2 z hzZ
      have hG' : ⁅(y : G), z⁆ ∈ O.map (Ia c a).subtype := by
        rwa [CFSG.Open.pCoreOf] at hG
      obtain ⟨w, hwO, hw⟩ := Subgroup.mem_map.mp hG'
      have hcoe : ((⁅y, zI⁆ : ↥(Ia c a)) : G) = ⁅(y : G), z⁆ :=
        map_commutatorElement (Ia c a).subtype y zI
      have hweq : (⁅y, zI⁆ : ↥(Ia c a)) = w := Subtype.ext (hcoe.trans hw.symm)
      rwa [hweq]
    have h1 : ⁅(QuotientGroup.mk' O) y, (QuotientGroup.mk' O) zI⁆ = 1 :=
      (map_commutatorElement (QuotientGroup.mk' O) y zI).symm.trans
        ((QuotientGroup.eq_one_iff _).mpr hmem)
    exact commutatorElement_eq_one_iff_mul_comm.mp h1
  have hzI3 : orderOf zI = 3 := by
    rw [Subgroup.orderOf_mk]
    exact hz3
  have hζ3 : orderOf ζ = 3 := by
    have hne : ζ ≠ 1 := by
      intro hζ
      have hzO : zI ∈ O := (QuotientGroup.eq_one_iff zI).mp hζ
      have hdvd : orderOf zI ∣ Nat.card O := Subgroup.orderOf_dvd_natCard O hzO
      obtain ⟨n, hn⟩ := IsPGroup.iff_card.mp hO2
      rw [hn, hzI3] at hdvd
      have hcop : Nat.Coprime 3 (2 ^ n) := Nat.Coprime.pow_right n (by norm_num)
      have hone : 3 = 1 := Nat.eq_one_of_dvd_coprimes hcop dvd_rfl hdvd
      norm_num at hone
    have hdvd : orderOf ζ ∣ 3 := by
      apply orderOf_dvd_of_pow_eq_one
      have h3 : zI ^ 3 = 1 := by simpa [hzI3] using pow_orderOf_eq_one zI
      show ((QuotientGroup.mk' O) zI) ^ 3 = 1
      rw [← map_pow, h3, map_one]
    rcases (Nat.dvd_prime Nat.prime_three).mp hdvd with h1 | h3
    · exact absurd (orderOf_eq_one_iff.mp h1) hne
    · exact h3
  have hζB : g ζ ≠ 1 := by
    intro hgζ
    have hψz : ψ zI = 1 := by
      rw [show g ζ = ψ zI from QuotientGroup.lift_mk' (N := O) hOker zI] at hgζ
      exact hgζ
    have hmemQ : (φ.rangeRestrict zI : A) ∈ Q := (QuotientGroup.eq_one_iff _).mp hψz
    have hmap : (O.map φ.rangeRestrict).map A.subtype = O.map φ := by
      rw [Subgroup.map_map, MonoidHom.subtype_comp_rangeRestrict]
    have hmem : φ zI ∈ O.map φ := by
      rw [← hmap]
      exact Subgroup.mem_map_of_mem A.subtype hmemQ
    obtain ⟨w, hwO, hwe⟩ := Subgroup.mem_map.mp hmem
    have hφz3 : orderOf (φ zI) = 3 := orderOf_piJ_apply_z c hIJ hzI hz3 hzN hπ
    have hdvd : orderOf (φ zI) ∣ Nat.card O := by
      have h1 : orderOf (φ zI) ∣ orderOf w := by
        rw [← hwe]
        exact orderOf_map_dvd φ w
      exact h1.trans (Subgroup.orderOf_dvd_natCard O hwO)
    obtain ⟨n, hn⟩ := IsPGroup.iff_card.mp hO2
    rw [hn, hφz3] at hdvd
    have hcop : Nat.Coprime 3 (2 ^ n) := Nat.Coprime.pow_right n (by norm_num)
    have hone : 3 = 1 := Nat.eq_one_of_dvd_coprimes hcop dvd_rfl hdvd
    norm_num at hone
  have hker : g.ker = ⊥ :=
    ker_eq_bot_of_isTripleCover hTperf hTtriple g hgsurj hζZ hζ3 hζB
  have hdvdQ : 1080 ∣ Nat.card (A ⧸ Q) :=
    dvd_1080_of_ker_eq_bot hTtriple g hgsurj hker
  have hdvdA : 1080 ∣ Nat.card A := hdvdQ.trans (Subgroup.card_quotient_dvd_card Q)
  simpa [A, φ] using hdvdA

end
end CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82E3.ONan

namespace CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82E3.ONan
section
open CFSG.Open
open CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo.Sec4
open CFSG.RankThree.PartOne (IsStronglyPEmbedded)
open CFSG.LocalAnalysis.UniquenessCase.UC22 (Data IsSpor)
open CFSG.LocalAnalysis.UniquenessCase.UCK (ThreeCover)
open CFSG.ASVolI.ChIJK (IsWeaklyClosedIn)
variable {G : Type} [Group G] [Finite G]
variable {D : Data G}

theorem weaklyClosed_zSub_of_onan_cover'
    (c : Ctx82E3 D) (hON : UCK.ThreeCover (fun Y _ => IsSpor Y .ONan) c.Lbar)
    (h7 : D.sig = {7})
    {P : Subgroup G} (hP : CFSG.ABGLocalTools.IsSylowOf 3 P D.M)
    (hNZ : Subgroup.normalizer ((zSub P c.L : Subgroup G) : Set G) ≤ D.M) :
    IsWeaklyClosedIn (zSub P c.L) P := by
  intro g hg
  have h := zSub_conj_eq_of_le_of_onan c hON h7 hP hNZ g⁻¹
    (by simpa [CFSG.conjugate] using hg)
  simpa [CFSG.conjugate] using h

theorem F10SevenElement_proved' (c : Ctx82E3 D)
    (hON : UCK.ThreeCover (fun Y _ => IsSpor Y .ONan) c.Lbar) (h7 : D.sig = {7})
    {P : Subgroup G} (hP : CFSG.ABGLocalTools.IsSylowOf 3 P D.M) : ∃ y ∈ D.M, y ∈ Subgroup.centralizer ((P ⊓ c.L : Subgroup G) : Set G) ∧ orderOf y = 7 := by
  obtain ⟨y, hyM, hy7, hycent⟩ :=
    exists_seven_mem_centralizer_inf_L_of_onan c hON (by rw [h7]; simp) hP
  exact ⟨y, hyM,
    Subgroup.mem_centralizer_iff.mpr (fun q hq => (hycent q hq).symm), hy7⟩

end
end CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82E3.ONan
