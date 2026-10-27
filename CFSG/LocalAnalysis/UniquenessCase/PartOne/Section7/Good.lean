module

public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section7.KInputs
public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section7.LayerBasic
import CFSG.LocalAnalysis.GLTheoremB.ComponentTools
import CFSG.LocalAnalysis.GLTheoremB.SchreierTools
import CFSG.GroupTheory.PCore.PrimeSetCore
import CFSG.LocalAnalysis.AGLEmbedding.OneSmallGEVNormalThreeInner

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartOne.Section7

open CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82
open CFSG.RankThree.PartOne (IsStronglyPEmbedded)

variable {G : Type} [Group G] [Finite G]

namespace Sec7Core4

theorem coverActsTriviallyOnSmall_of_stronglyEmbeddedFive (k : Sec7Core4 G) (h5 : 5 ≤ k.p)
    {H : Subgroup G} (hH : Config k H) (hSE : StronglyEmbeddedFive) :
    CoverActsTriviallyOnSmall k.p
      ↥(CFSG.generalizedFitting (↥H ⧸ CFSG.pPrimeCore k.p ↥H)) := by
  have hp : k.p.Prime := k.prime
  haveI : Fact k.p.Prime := ⟨hp⟩
  have hKH : CFSG.Open.IsKGroup ↥H :=
    CFSG.LocalAnalysis.GLTheoremB.isKGroup_of_isKProper k.standing.kProper hH.ne_top
  have hKQ : CFSG.Open.IsKGroup (↥H ⧸ CFSG.pPrimeCore k.p ↥H) :=
    CFSG.LocalAnalysis.GLTheoremB.isKGroup_quotient' hKH (CFSG.pPrimeCore k.p ↥H)
  have hO : CFSG.pPrimeCore k.p (↥H ⧸ CFSG.pPrimeCore k.p ↥H) = ⊥ :=
    CFSG.pPrimeCore_quotient_eq_bot hp
  have hrank : 2 ≤ CFSG.Open.pRank k.p (⊤ : Subgroup (↥H ⧸ CFSG.pPrimeCore k.p ↥H)) :=
    k.two_le_pRank_quotient_pPrimeCore hH
  have hN : IsStronglyPEmbedded k.p
      (((H ⊓ k.M).subgroupOf H).map (QuotientGroup.mk' (CFSG.pPrimeCore k.p ↥H))) :=
    k.isStronglyPEmbedded_map_quotient_pPrimeCore hH
  exact (hSE k.p hp h5 _ hKQ hO hrank _ hN).1

theorem exists_twoLocal_four_le_threeRank_of_coverHasLargeTwoLocal (k : Sec7Core4 G)
    {H : Subgroup G} (hH : Config k H) (h75 : Step75 k)
    (hbad : CoverHasLargeTwoLocal ↥(CFSG.generalizedFitting (↥H ⧸ CFSG.pPrimeCore k.p ↥H))) :
    ∃ N : Subgroup G, CFSG.Open.IsTwoLocal N ∧ 4 ≤ CFSG.Open.pRank 3 N := by
  have hp : k.p.Prime := k.prime
  haveI : Fact k.p.Prime := ⟨hp⟩
  let K₀ : Subgroup ↥H := CFSG.pPrimeCore k.p ↥H
  let π : ↥H →* (↥H ⧸ K₀) := QuotientGroup.mk' K₀
  let Lbar : Subgroup (↥H ⧸ K₀) := CFSG.generalizedFitting (↥H ⧸ K₀)
  let J : Subgroup G := layerLift k.p H
  let KG : Subgroup G := K₀.map H.subtype
  have hJH : J ≤ H := layerLift_le k.p H
  have hJperf : Group.IsPerfect ↥J :=
    Subgroup.isPerfect_iff.mpr (commutator_layerLift k.p H)
  have hsimple := k.isSimpleGroup_generalizedFitting_quotient hH
  haveI : IsSimpleGroup ↥Lbar := hsimple.1
  have hLbarperf : ⁅Lbar, Lbar⁆ = Lbar :=
    Subgroup.isPerfect_iff.mp
      (CFSG.LocalCores.isQuasisimple_of_isSimpleGroup hsimple.2.1).1.1
  have hmap : (J.subgroupOf H).map π = Lbar := map_layerLift_eq k.p H hLbarperf
  let ι : ↥J →* ↥H := Subgroup.inclusion hJH
  let φ₀ : ↥J →* (↥H ⧸ K₀) := π.comp ι
  have hφ₀mem : ∀ x : ↥J, φ₀ x ∈ Lbar := by
    intro x
    have hx : ι x ∈ J.subgroupOf H := Subgroup.mem_subgroupOf.mpr x.2
    have hmem : π (ι x) ∈ (J.subgroupOf H).map π := Subgroup.mem_map_of_mem π hx
    rwa [hmap] at hmem
  let φ : ↥J →* ↥Lbar := φ₀.codRestrict Lbar hφ₀mem
  have hφsurj : Function.Surjective φ := by
    intro y
    have hy : (y : ↥H ⧸ K₀) ∈ (J.subgroupOf H).map π := by
      rw [hmap]
      exact y.2
    obtain ⟨h, hh, hπh⟩ := Subgroup.mem_map.mp hy
    have hhJ : (h : G) ∈ J := Subgroup.mem_subgroupOf.mp hh
    refine ⟨⟨(h : G), hhJ⟩, ?_⟩
    apply Subtype.ext
    have hι : ι ⟨(h : G), hhJ⟩ = h := Subtype.ext rfl
    show π (ι ⟨(h : G), hhJ⟩) = (y : ↥H ⧸ K₀)
    rw [hι]
    exact hπh
  have hφker_center : φ.ker ≤ Subgroup.center ↥J := by
    intro x hx
    have hxπ : π (ι x) = 1 := congrArg Subtype.val (MonoidHom.mem_ker.mp hx)
    have hxK₀ : ι x ∈ K₀ := by
      rw [← QuotientGroup.ker_mk' K₀]
      exact MonoidHom.mem_ker.mpr hxπ
    have hxKG : (x : G) ∈ KG := Subgroup.mem_map_of_mem H.subtype hxK₀
    have hcommKG : KG ≤ Subgroup.centralizer (J : Set G) := by
      refine (Subgroup.commutator_eq_bot_iff_le_centralizer
        (H₁ := KG) (H₂ := J)).mp ?_
      simpa [Subgroup.commutator_comm] using h75 H hH
    rw [Subgroup.mem_center_iff]
    intro y
    apply Subtype.ext
    exact Subgroup.mem_centralizer_iff.mp (hcommKG hxKG) (y : G) y.2
  have hφker_odd : Odd (Nat.card φ.ker) := by
    have hKGodd : Odd (Nat.card KG) := by
      rw [show Nat.card KG = Nat.card K₀ from
        Subgroup.card_map_of_injective H.subtype_injective]
      exact k.odd_card_pPrimeCore_of_not_le hH.not_le hH.two_le_pRank
    have hle : φ.ker.map J.subtype ≤ KG := by
      rintro _ ⟨x, hx, rfl⟩
      have hxπ : π (ι x) = 1 := congrArg Subtype.val (MonoidHom.mem_ker.mp hx)
      have hxK₀ : ι x ∈ K₀ := by
        rw [← QuotientGroup.ker_mk' K₀]
        exact MonoidHom.mem_ker.mpr hxπ
      exact Subgroup.mem_map_of_mem H.subtype hxK₀
    rw [← Subgroup.card_map_of_injective J.subtype_injective]
    exact Odd.of_dvd_nat hKGodd (Subgroup.card_dvd_of_le hle)
  obtain ⟨U, hUne, hU2, hU4⟩ := hbad ↥J hJperf φ hφsurj hφker_center hφker_odd
  let UG : Subgroup G := U.map J.subtype
  have hUGne : UG ≠ ⊥ := by
    rintro h
    exact hUne ((Subgroup.map_eq_bot_iff_of_injective U J.subtype_injective).mp h)
  have hUG2 : IsPGroup 2 UG := hU2.map J.subtype
  have hloc : CFSG.Open.IsTwoLocal (Subgroup.normalizer (UG : Set G)) :=
    ⟨UG, hUGne, hUG2, rfl⟩
  have hle : (Subgroup.normalizer (U : Set ↥J)).map J.subtype ≤
      Subgroup.normalizer (UG : Set G) := Subgroup.le_normalizer_map J.subtype
  have h4G : 4 ≤ CFSG.Open.pRank 3 (Subgroup.normalizer (UG : Set G)) :=
    hU4.trans ((CFSG.SectionRank.pRank_le_map (p := 3) (by norm_num) J.subtype
      J.subtype_injective _).trans
      (CFSG.SectionRank.pRank_mono (p := 3) (by norm_num) hle))
  exact ⟨_, hloc, h4G⟩

theorem not_coverHasLargeTwoLocal (k : Sec7Core4 G) (h3 : 3 ∉ CFSG.Open.uniqueFourBeta G)
    {H : Subgroup G} (hH : Config k H) (h75 : Step75 k) :
    ¬ CoverHasLargeTwoLocal ↥(CFSG.generalizedFitting (↥H ⧸ CFSG.pPrimeCore k.p ↥H)) := by
  intro hbad
  obtain ⟨N, hloc, h4G⟩ :=
    k.exists_twoLocal_four_le_threeRank_of_coverHasLargeTwoLocal hH h75 hbad
  have h3dvdG : 3 ∣ Nat.card G := by
    have h1 : 3 ^ 4 ∣ Nat.card N :=
      (Nat.pow_dvd_pow 3 h4G).trans
        (CFSG.RankThreeEvenClassification.Helpers.prime_power_pRank_dvd_card 3
          Nat.prime_three _)
    exact (dvd_pow_self 3 (by norm_num : (4 : ℕ) ≠ 0)).trans
      (h1.trans (Subgroup.card_subgroup_dvd_card _))
  have h4rank : 4 ≤ CFSG.Open.uniqueFourTwoLocalRank 3 G := by
    change 4 ≤ CFSG.Open.twoLocalPrimeRank 3 G
    exact h4G.trans (le_csSup
      (CFSG.PreuniquenessRankFour.Helpers.twoLocalRank_bddAbove 3 Nat.prime_three)
      ⟨_, hloc, rfl⟩)
  exact h3 ⟨Nat.prime_three, by norm_num, h3dvdG, h4rank⟩

@[expose] def KIDExcluded (k : Sec7Core4 G) : Prop :=
  ∀ H : Subgroup G, Config k H → Step75 k →
    ¬ CoverHasLargeTwoLocal ↥(CFSG.generalizedFitting (↥H ⧸ CFSG.pPrimeCore k.p ↥H))

theorem kIDExcluded_of_not_mem_beta (k : Sec7Core4 G) (h3 : 3 ∉ CFSG.Open.uniqueFourBeta G) :
    KIDExcluded k :=
  fun _ hH h75 => k.not_coverHasLargeTwoLocal h3 hH h75

theorem kIDExcluded_of_evenRank_le_three (k : Sec7Core4 G) (he : CFSG.Open.evenRank G ≤ 3) :
    KIDExcluded k := by
  intro H hH h75 hbad
  obtain ⟨N, hloc, h4⟩ :=
    k.exists_twoLocal_four_le_threeRank_of_coverHasLargeTwoLocal hH h75 hbad
  have hle := CFSG.RankThreeEvenClassification.Helpers.pRank_le_evenRank 3 Nat.prime_three
    (by norm_num) N hloc
  omega

theorem good_of_stronglyEmbeddedFive_of_kIDExcluded (k : Sec7Core4 G) (h5 : 5 ≤ k.p)
    (hno : KIDExcluded k) {H : Subgroup G}
    (hH : Config k H) (hSE : StronglyEmbeddedFive) (h75 : Step75 k) :
    CFSG.pPrimeCore k.p
        ↥(((H ⊓ k.M).subgroupOf H).map (QuotientGroup.mk' (CFSG.pPrimeCore k.p ↥H))) = ⊥ ∧
      CentralizerHasPElementOutside k.p
        (((H ⊓ k.M).subgroupOf H).map (QuotientGroup.mk' (CFSG.pPrimeCore k.p ↥H))) := by
  have hp : k.p.Prime := k.prime
  haveI : Fact k.p.Prime := ⟨hp⟩
  let K₀ : Subgroup ↥H := CFSG.pPrimeCore k.p ↥H
  let π : ↥H →* (↥H ⧸ K₀) := QuotientGroup.mk' K₀
  let Nbar : Subgroup (↥H ⧸ K₀) := ((H ⊓ k.M).subgroupOf H).map π
  have hKH : CFSG.Open.IsKGroup ↥H :=
    CFSG.LocalAnalysis.GLTheoremB.isKGroup_of_isKProper k.standing.kProper hH.ne_top
  have hKQ : CFSG.Open.IsKGroup (↥H ⧸ K₀) :=
    CFSG.LocalAnalysis.GLTheoremB.isKGroup_quotient' hKH K₀
  have hO : CFSG.pPrimeCore k.p (↥H ⧸ K₀) = ⊥ := CFSG.pPrimeCore_quotient_eq_bot hp
  have hrank : 2 ≤ CFSG.Open.pRank k.p (⊤ : Subgroup (↥H ⧸ K₀)) :=
    k.two_le_pRank_quotient_pPrimeCore hH
  have hN : IsStronglyPEmbedded k.p Nbar :=
    k.isStronglyPEmbedded_map_quotient_pPrimeCore hH
  have hbr := hSE k.p hp h5 (↥H ⧸ K₀) hKQ hO hrank Nbar hN
  rcases hbr.2 with hgood | hbad
  · exact hgood
  · exact absurd hbad (hno H hH h75)

theorem step76C_of_centralizerHasPElementOutside (k : Sec7Core4 G)
    (hC : ∀ H : Subgroup G, Config k H →
      CentralizerHasPElementOutside k.p
        (((H ⊓ k.M).subgroupOf H).map (QuotientGroup.mk' (CFSG.pPrimeCore k.p ↥H)))) :
    Step76C k := by
  intro H hH x y hx hy hxp hxK hyp hy2 hyp' hyK hxy
  have hp : k.p.Prime := k.prime
  haveI : Fact k.p.Prime := ⟨hp⟩
  let K₀ : Subgroup ↥H := CFSG.pPrimeCore k.p ↥H
  let π : ↥H →* (↥H ⧸ K₀) := QuotientGroup.mk' K₀
  let Nbar : Subgroup (↥H ⧸ K₀) := ((H ⊓ k.M).subgroupOf H).map π
  let Lbar : Subgroup (↥H ⧸ K₀) := CFSG.generalizedFitting (↥H ⧸ K₀)
  let J : Subgroup G := layerLift k.p H
  let KG : Subgroup G := K₀.map H.subtype
  let xh : ↥H := ⟨x, hx.1⟩
  let yh : ↥H := ⟨y, hy.1⟩
  let xbar : (↥H ⧸ K₀) := π xh
  let ybar : (↥H ⧸ K₀) := π yh
  have hxbarN : xbar ∈ Nbar :=
    Subgroup.mem_map_of_mem π (Subgroup.mem_subgroupOf.mpr hx)
  have hybarN : ybar ∈ Nbar :=
    Subgroup.mem_map_of_mem π (Subgroup.mem_subgroupOf.mpr hy)
  have hxbar_ne : xbar ≠ 1 := by
    intro h
    have hker : xh ∈ π.ker := MonoidHom.mem_ker.mpr (by simpa [xbar] using h)
    rw [QuotientGroup.ker_mk'] at hker
    exact hxK (Subgroup.mem_map_of_mem H.subtype hker)
  have hybar_ne : ybar ≠ 1 := by
    intro h
    have hker : yh ∈ π.ker := MonoidHom.mem_ker.mpr (by simpa [ybar] using h)
    rw [QuotientGroup.ker_mk'] at hker
    exact hyK (Subgroup.mem_map_of_mem H.subtype hker)
  have hxpbar : IsPGroup k.p (Subgroup.zpowers xbar) := by
    obtain ⟨n, hn⟩ := IsPGroup.iff_card.mp hxp
    have hxord : orderOf x = k.p ^ n := by rw [← Nat.card_zpowers, hn]
    have hdvd : orderOf xbar ∣ k.p ^ n := by
      have h1 : orderOf xbar ∣ orderOf x := by
        have h2 : orderOf xbar ∣ orderOf xh := orderOf_map_dvd π xh
        have h3 : orderOf xh = orderOf x := (Subgroup.orderOf_coe xh).symm
        rwa [h3] at h2
      rwa [hxord] at h1
    refine IsPGroup.of_card_dvd_pow (n := n) ?_
    rwa [Nat.card_zpowers]
  have horder_ybar : orderOf ybar = orderOf y := by
    have hdvd : orderOf ybar ∣ orderOf y := by
      have h1 : orderOf ybar ∣ orderOf yh := orderOf_map_dvd π yh
      have h3 : orderOf yh = orderOf y := (Subgroup.orderOf_coe yh).symm
      rwa [h3] at h1
    rcases (Nat.dvd_prime hyp).mp hdvd with h1 | h1
    · exact absurd (orderOf_eq_one_iff.mp h1) hybar_ne
    · exact h1
  have hypbar : (orderOf ybar).Prime := horder_ybar ▸ hyp
  have hybar2 : orderOf ybar ≠ 2 := by rw [horder_ybar]; exact hy2
  have hybarp : orderOf ybar ≠ k.p := by rw [horder_ybar]; exact hyp'
  have hxybar : xbar * ybar = ybar * xbar := by
    have hxh_mul : xh * yh = (⟨x * y, H.mul_mem hx.1 hy.1⟩ : ↥H) := Subtype.ext rfl
    have hyh_mul : yh * xh = (⟨y * x, H.mul_mem hy.1 hx.1⟩ : ↥H) := Subtype.ext rfl
    have hval : (⟨x * y, H.mul_mem hx.1 hy.1⟩ : ↥H) = ⟨y * x, H.mul_mem hy.1 hx.1⟩ :=
      Subtype.ext hxy
    calc xbar * ybar = π (xh * yh) := (map_mul π xh yh).symm
      _ = π ⟨x * y, H.mul_mem hx.1 hy.1⟩ := by rw [hxh_mul]
      _ = π ⟨y * x, H.mul_mem hy.1 hx.1⟩ := by rw [hval]
      _ = π (yh * xh) := by rw [hyh_mul]
      _ = ybar * xbar := map_mul π yh xh
  obtain ⟨cc, hccL, hccy, hccp, hccN⟩ :=
    hC H hH xbar ybar hxbarN hybarN hxbar_ne hxpbar hypbar hybar2 hybarp hxybar
  have hsimple := k.isSimpleGroup_generalizedFitting_quotient hH
  haveI : IsSimpleGroup ↥Lbar := hsimple.1
  have hLbarperf : ⁅Lbar, Lbar⁆ = Lbar :=
    Subgroup.isPerfect_iff.mp
      (CFSG.LocalCores.isQuasisimple_of_isSimpleGroup hsimple.2.1).1.1
  have hmap : (J.subgroupOf H).map π = Lbar := map_layerLift_eq k.p H hLbarperf
  have hccL' : cc ∈ (J.subgroupOf H).map π := by rw [hmap]; exact hccL
  obtain ⟨h, hh, hπh⟩ := Subgroup.mem_map.mp hccL'
  have hhJ : (h : G) ∈ J := Subgroup.mem_subgroupOf.mp hh
  let ι : ↥J →* ↥H := Subgroup.inclusion (layerLift_le k.p H)
  let ψ : ↥J →* (↥H ⧸ K₀) := π.comp ι
  let xj : ↥J := ⟨(h : G), hhJ⟩
  have hψxj : ψ xj = cc := by
    have hι : ι xj = h := Subtype.ext rfl
    show π (ι xj) = cc
    rw [hι]
    exact hπh
  obtain ⟨n, e, hpn, hfix⟩ := CFSG.AGLEmbedding.exists_pPart_pow hp xj
  let jJ : ↥J := xj ^ n
  let j : G := (jJ : G)
  have hccorder : cc ^ orderOf xj = 1 := by
    have hdvd : orderOf cc ∣ orderOf xj := by
      have h := orderOf_map_dvd ψ xj
      rwa [hψxj] at h
    exact (orderOf_dvd_iff_pow_eq_one).mp hdvd
  have hccpow : ∃ m : ℕ, cc ^ k.p ^ m = 1 := by
    obtain ⟨n, hn⟩ := IsPGroup.iff_card.mp hccp
    have hcord : orderOf cc = k.p ^ n := by rw [← Nat.card_zpowers, hn]
    exact ⟨n, by rw [← hcord]; exact pow_orderOf_eq_one cc⟩
  have hψj : ψ jJ = cc := by
    calc ψ jJ = ψ (xj ^ n) := rfl
      _ = (ψ xj) ^ n := map_pow ψ xj n
      _ = cc ^ n := by rw [hψxj]
      _ = cc := hfix cc hccorder hccpow
  have hjJ : j ∈ J := jJ.2
  have hjH : j ∈ H := layerLift_le k.p H hjJ
  have hjpow_rel : j ^ k.p ^ e = 1 := by
    have h := congrArg J.subtype hpn
    rw [map_pow, map_one] at h
    exact h
  have hjpow : IsPGroup k.p (Subgroup.zpowers j) := by
    refine IsPGroup.of_card_dvd_pow (n := e) ?_
    rw [Nat.card_zpowers]
    exact orderOf_dvd_of_pow_eq_one hjpow_rel
  have hπι : π (ι jJ) = cc := hψj
  have hπj : π (⟨j, hjH⟩ : ↥H) = cc := by
    rwa [show ι jJ = ⟨j, hjH⟩ from Subtype.ext rfl] at hπι
  have hjnotM : j ∉ k.M := by
    intro hjM
    have hmemN : π (⟨j, hjH⟩ : ↥H) ∈ Nbar :=
      Subgroup.mem_map_of_mem π (Subgroup.mem_subgroupOf.mpr ⟨hjH, hjM⟩)
    rw [hπj] at hmemN
    exact hccN hmemN
  have hcommut : j * y * j⁻¹ * y⁻¹ ∈ KG := by
    have hmemH : j * y * j⁻¹ * y⁻¹ ∈ H :=
      H.mul_mem (H.mul_mem (H.mul_mem hjH hy.1) (H.inv_mem hjH)) (H.inv_mem hy.1)
    have hπcomm : π (⟨j * y * j⁻¹ * y⁻¹, hmemH⟩ : ↥H) = 1 := by
      have hmul : (⟨j * y * j⁻¹ * y⁻¹, hmemH⟩ : ↥H) =
          ι jJ * yh * (ι jJ)⁻¹ * yh⁻¹ := Subtype.ext rfl
      rw [hmul, map_mul, map_mul, map_inv, map_mul, map_inv, hπι, show π yh = ybar from rfl,
        hccy]
      group
    exact Subgroup.mem_map_of_mem H.subtype
      (show (⟨j * y * j⁻¹ * y⁻¹, hmemH⟩ : ↥H) ∈ K₀ from by
        rw [← QuotientGroup.ker_mk' K₀]
        exact MonoidHom.mem_ker.mpr hπcomm)
  exact ⟨j, hjJ, hjpow, hjnotM, hcommut⟩

end Sec7Core4

end CFSG.LocalAnalysis.UniquenessCase.PartOne.Section7
