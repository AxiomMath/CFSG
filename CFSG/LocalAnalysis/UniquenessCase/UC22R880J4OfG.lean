module

public import CFSG.LocalAnalysis.UniquenessCase.UC22R880J4Facts
public import CFSG.LocalAnalysis.UniquenessCase.UC22R880J4G
public import CFSG.LocalAnalysis.UniquenessCase.UC6S846e
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.R76Sig
import CFSG.GroupTheory.PerfectSylowInversion
import CFSG.GroupTheory.PRankMapOfKerPrimeNotDvd
import CFSG.HardMathSupport.Solomon.Proving.GLBCoreNormalizer
import CFSG.LocalAnalysis.EvenSporadicStandard.J4Std.Layer0J4
import CFSG.LocalAnalysis.StronglyEmbedded.GammaOne
import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.K33PartialRanks
import CFSG.LocalAnalysis.UniquenessCase.UC22P20d
import CFSG.Quasithin.Vol2.Ch11SecO8HB
public import CFSG.GroupTheory.PGroup.ElemAbelianSq
public import CFSG.LocalAnalysis.UniquenessCase.UCFront08J4
import CFSG.LocalAnalysis.UniquenessCase.UC22OddPRank
import CFSG.LocalAnalysis.UniquenessCase.UC6S846g

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22.F08

open CFSG.Open Subgroup
open CFSG.RankThree.PartOne (IsStronglyPEmbedded)

private theorem orderOf_mk_eq_of_isPGroup_two {X : Type} [Group X] {N : Subgroup X} [N.Normal]
    (hN : IsPGroup 2 N) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) {x : X} (hx : orderOf x = p) :
    orderOf (QuotientGroup.mk x : X ⧸ N) = p := by
  have := Fact.mk hp
  have hxp : x ^ p = 1 := hx ▸ pow_orderOf_eq_one x
  refine orderOf_eq_prime (by rw [← QuotientGroup.mk_pow, hxp, QuotientGroup.mk_one]) ?_
  intro h1
  obtain ⟨n, hn⟩ := hN ⟨x, (QuotientGroup.eq_one_iff x).1 h1⟩
  have h2 : x ^ 2 ^ n = 1 := by simpa using congrArg Subtype.val hn
  have h3 : p ∣ 2 ^ n := hx ▸ orderOf_dvd_of_pow_eq_one h2
  exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).1 (hp.dvd_of_dvd_pow h3))

private theorem le_normalizer_of_isSpor_J4 {G : Type} [Group G] [Finite G]
    {D : Data G}
    (hSg : UC6S846.SigmaStd D) {L : Subgroup G} (hL : L ∈ calC D.M) (hJ4 : IsSpor (Bar2 L) .J4)
    (h3 : 3 ∉ D.sig) : D.M ≤ normalizer (L : Set G) := by
  by_contra hnN
  have hL3 : CFSG.Open.pRank 3 L = 2 :=
    (pRank_bar2_eq_of_odd (Y := L) Nat.prime_three (by norm_num)).symm.trans
      (PartOne.Section8.pRank_three_eq_two_of_isSpor_J4 hJ4)
  obtain ⟨E, hEL, hEel, hEcard⟩ := CFSG.SectionRank.exists_pRank (p := 3) (by norm_num) L
  have hZ : ¬ 3 ∣ Nat.card (center (Bar2 L)) := by
    rw [CFSG.EvenSporadicStandard.J4Std.center_eq_bot_of_isSporadic hJ4, Subgroup.card_bot]
    norm_num
  have h4 := UC6S846.calCRankTwice D.M L hL hnN 3 Nat.prime_three (by norm_num) hZ E hEL hEel 2
    (by rw [hEcard, hL3])
  exact h3 (hSg.four_mem 3 Nat.prime_three (by norm_num) (by omega))

private theorem exists_orderOf_eleven_mk_mem_centralizer {G : Type} [Group G] [Finite G]
    {M L : Subgroup G} (hLM : L ≤ M) (hN : M ≤ normalizer (L : Set G))
    (hB : ∀ B : Subgroup (MulAut ↥((L.subgroupOf M).map (QuotientGroup.mk' (CFSG.pCore 2 ↥M)))),
      IsElemAbelian 11 B → Nat.card B ≤ 11 ^ 2)
    (h3 : 3 ≤ CFSG.Open.pRank 11 M) :
    ∃ f : ↥M, orderOf f = 11 ∧ QuotientGroup.mk' (CFSG.pCore 2 ↥M) f ∈
      centralizer (((L.subgroupOf M).map (QuotientGroup.mk' (CFSG.pCore 2 ↥M)) :
        Subgroup (Bar2 M)) : Set (Bar2 M)) := by
  have : Fact (Nat.Prime 11) := ⟨by norm_num⟩
  set π : ↥M →* Bar2 M := QuotientGroup.mk' (CFSG.pCore 2 ↥M)
  set C : Subgroup (Bar2 M) := (L.subgroupOf M).map π
  have hLn : (L.subgroupOf M).Normal := (Subgroup.normal_subgroupOf_iff_le_normalizer hLM).2 hN
  have hCn : C.Normal := hLn.map π (QuotientGroup.mk'_surjective _)
  let θ : ↥M →* MulAut ↥C := MulAut.conjNormal.comp π
  obtain ⟨R, hRM, hRel, hRcard⟩ := CFSG.SectionRank.exists_pRank (p := 11) (by norm_num) M
  have hR'card : Nat.card (R.subgroupOf M) = 11 ^ CFSG.Open.pRank 11 M :=
    (Nat.card_congr (Subgroup.subgroupOfEquivOfLe hRM).toEquiv).trans hRcard
  have hR'el : IsElemAbelian 11 (R.subgroupOf M) := hRel.subgroupOf M
  have hBθ := hB ((R.subgroupOf M).map θ) (hR'el.map θ)
  have h := Subgroup.relIndex_mul_card θ.ker (R.subgroupOf M)
  rw [Subgroup.relIndex_ker] at h
  have hne : θ.ker ⊓ R.subgroupOf M ≠ ⊥ := by
    intro hbot
    rw [hbot, Subgroup.card_bot, mul_one, hR'card] at h
    rw [h] at hBθ
    have h1 : 11 ^ 3 ≤ 11 ^ CFSG.Open.pRank 11 M := Nat.pow_le_pow_right (by norm_num) h3
    have h2 := h1.trans hBθ
    norm_num at h2
  obtain ⟨f, hf, hf1⟩ := (Subgroup.bot_or_exists_ne_one _).resolve_left hne
  refine ⟨f, orderOf_eq_prime (hR'el.2 f hf.2) hf1, ?_⟩
  refine Subgroup.mem_centralizer_iff.mpr fun b hb => ?_
  have h1 : ((θ f ⟨b, hb⟩ : ↥C) : Bar2 M) = b := by
    rw [(MonoidHom.mem_ker.mp hf.1 : θ f = 1)]
    rfl
  have h2 : π f * b * (π f)⁻¹ = b := h1
  exact (mul_inv_eq_iff_eq_mul.mp h2).symm

private theorem exists_conj_centralizer_of_mk_mem_centralizer {G : Type} [Group G] [Finite G]
    {M L Q : Subgroup G} (hLM : L ≤ M) (hQL : Q ≤ L) (hQ : IsPGroup 3 Q) {f : ↥M}
    (hf : orderOf f = 11)
    (hfC : QuotientGroup.mk' (CFSG.pCore 2 ↥M) f ∈ centralizer
      (((L.subgroupOf M).map (QuotientGroup.mk' (CFSG.pCore 2 ↥M)) : Subgroup (Bar2 M)) :
        Set (Bar2 M))) :
    ∃ f₁ : ↥M, orderOf f₁ = 11 ∧
      QuotientGroup.mk' (CFSG.pCore 2 ↥M) f₁ = QuotientGroup.mk' (CFSG.pCore 2 ↥M) f ∧
      ∀ q ∈ Q, (f₁ : G) * q = q * f₁ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hPn : (CFSG.pCore 2 ↥M).Normal := CFSG.pCore_normal
  set π : ↥M →* Bar2 M := QuotientGroup.mk' (CFSG.pCore 2 ↥M)
  have hQ' : IsPGroup 3 (Q.subgroupOf M) := hQ.comap_subtype
  have hQodd : Odd (Nat.card (Q.subgroupOf M)) := by
    obtain ⟨k, hk⟩ := hQ'.exists_card_eq
    rw [hk]
    exact Odd.pow ⟨1, rfl⟩
  have hFodd : Odd (Nat.card (zpowers f)) := by
    rw [Nat.card_zpowers, hf]
    exact ⟨5, rfl⟩
  have hNP : normalizer ((CFSG.pCore 2 ↥M : Subgroup ↥M) : Set ↥M) = ⊤ :=
    Subgroup.normalizer_eq_top_iff.2 hPn
  have hDX : ∀ d ∈ Q.subgroupOf M, ∀ x ∈ zpowers f, d * x * d⁻¹ * x⁻¹ ∈ CFSG.pCore 2 ↥M := by
    intro d hd x hx
    have hdC : π d ∈ (L.subgroupOf M).map π :=
      Subgroup.mem_map_of_mem π (Subgroup.subgroupOf_mono M hQL hd)
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hx
    have hxC : π (f ^ k) ∈ centralizer (((L.subgroupOf M).map π : Subgroup (Bar2 M)) :
        Set (Bar2 M)) := by
      rw [map_zpow]
      exact zpow_mem hfC k
    have hcomm : π d * π (f ^ k) = π (f ^ k) * π d := Subgroup.mem_centralizer_iff.mp hxC _ hdC
    rw [← QuotientGroup.eq_one_iff]
    change π (d * f ^ k * d⁻¹ * (f ^ k)⁻¹) = 1
    rw [map_mul, map_mul, map_mul, map_inv, map_inv, hcomm]
    group
  obtain ⟨u, huP, hcent⟩ := CFSG.Quasithin.Vol2.Ch11.SecD.O8H.exists_conj_centralized
    (CFSG.pCore_isPGroup (p := 2) (G := ↥M)) hQodd hFodd (by rw [hNP]; exact le_top)
    (by rw [hNP]; exact le_top) hDX
  have hπu : π u = 1 := (QuotientGroup.eq_one_iff u).2 huP
  refine ⟨MulAut.conj u⁻¹ f, (MulEquiv.orderOf_eq _ f).trans hf, ?_, ?_⟩
  · rw [MulAut.conj_apply]
    simp only [inv_inv, map_mul, map_inv, hπu, inv_one, one_mul, mul_one]
  · intro q hq
    have hqM : q ∈ M := hLM (hQL hq)
    have hq' : (⟨q, hqM⟩ : ↥M) ∈ Q.subgroupOf M := hq
    have hmem : u * ⟨q, hqM⟩ * u⁻¹ ∈ (Q.subgroupOf M).map (MulAut.conj u).toMonoidHom :=
      ⟨⟨q, hqM⟩, hq', rfl⟩
    have h1 : (u * ⟨q, hqM⟩ * u⁻¹) * f = f * (u * ⟨q, hqM⟩ * u⁻¹) :=
      Subgroup.mem_centralizer_iff.mp (hcent (Subgroup.mem_zpowers f)) _ hmem
    have h2 : MulAut.conj u⁻¹ f * ⟨q, hqM⟩ = ⟨q, hqM⟩ * MulAut.conj u⁻¹ f := by
      rw [MulAut.conj_apply, inv_inv]
      calc u⁻¹ * f * u * ⟨q, hqM⟩ = u⁻¹ * (f * (u * ⟨q, hqM⟩ * u⁻¹)) * u := by group
        _ = u⁻¹ * ((u * ⟨q, hqM⟩ * u⁻¹) * f) * u := by rw [h1]
        _ = ⟨q, hqM⟩ * (u⁻¹ * f * u) := by group
    have h3 := congrArg Subtype.val h2
    rwa [Subgroup.coe_mul, Subgroup.coe_mul] at h3

private theorem one_lt_pRank_eleven_normalizer_of_commute {G : Type} [Group G] [Finite G]
    {M L Y : Subgroup G} (hLM : L ≤ M) (hsub : IsSubnormal L M) (hZ : center (Bar2 L) = ⊥)
    (hw : ∀ x : Bar2 L, orderOf x = 3 → ∃ w : Bar2 L, orderOf w = 11 ∧ Commute x w)
    (hYL : Y ≤ L) (hY : Nat.card Y = 3) {f₁ : ↥M} (hf₁ : orderOf f₁ = 11)
    (hf₁C : QuotientGroup.mk' (CFSG.pCore 2 ↥M) f₁ ∈ centralizer
      (((L.subgroupOf M).map (QuotientGroup.mk' (CFSG.pCore 2 ↥M)) : Subgroup (Bar2 M)) :
        Set (Bar2 M)))
    (hf₁Y : (f₁ : G) ∈ normalizer (Y : Set G)) :
    1 < CFSG.Open.pRank 11 (M ⊓ normalizer (Y : Set G)) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have : Fact (Nat.Prime 11) := ⟨by norm_num⟩
  have hPLn : (CFSG.pCore 2 ↥L).Normal := CFSG.pCore_normal
  have hPMn : (CFSG.pCore 2 ↥M).Normal := CFSG.pCore_normal
  set π : ↥M →* Bar2 M := QuotientGroup.mk' (CFSG.pCore 2 ↥M) with hπ
  set C : Subgroup (Bar2 M) := (L.subgroupOf M).map π
  obtain ⟨e, he⟩ := uc22p20d_bar2Equiv hLM hsub
  have : Nontrivial Y := Finite.one_lt_card_iff_nontrivial.mp (by rw [hY]; norm_num)
  obtain ⟨⟨y, hyY⟩, hy1⟩ := exists_ne (1 : Y)
  have hy1' : y ≠ 1 := fun h => hy1 (Subtype.ext h)
  have hyord : orderOf y = 3 := by
    have hdvd : orderOf y ∣ 3 := by
      rw [← Subgroup.orderOf_mk y hyY, ← hY]
      exact orderOf_dvd_natCard _
    rcases (Nat.dvd_prime Nat.prime_three).mp hdvd with h | h
    · exact absurd (orderOf_eq_one_iff.mp h) hy1'
    · exact h
  have hYz : Y = zpowers y :=
    (Subgroup.eq_of_le_of_card_ge (zpowers_le.mpr hyY)
      (by rw [hY, Nat.card_zpowers, hyord])).symm
  have hybar : orderOf (QuotientGroup.mk (⟨y, hYL hyY⟩ : ↥L) : Bar2 L) = 3 :=
    orderOf_mk_eq_of_isPGroup_two (N := CFSG.pCore 2 ↥L) CFSG.pCore_isPGroup Nat.prime_three
      (by norm_num) ((Subgroup.orderOf_mk y (hYL hyY)).trans hyord)
  obtain ⟨w, hw11, hwc⟩ := hw _ hybar
  have hN3 : ¬ 3 ∣ Nat.card (CFSG.pCore 2 ↥L) := by
    obtain ⟨k, hk⟩ := (CFSG.pCore_isPGroup (p := 2) (G := ↥L)).exists_card_eq
    rw [hk]
    intro hd
    exact absurd (Nat.prime_three.dvd_of_dvd_pow hd) (by norm_num)
  have hYp : IsPGroup 3 Y := IsPGroup.of_card (n := 1) (by rw [hY, pow_one])
  have hA : IsPGroup 3 (Y.subgroupOf L) := hYp.comap_subtype
  have hwN : w ∈ normalizer (((Y.subgroupOf L).map (QuotientGroup.mk' (CFSG.pCore 2 ↥L)) :
      Subgroup (Bar2 L)) : Set (Bar2 L)) := by
    refine Subgroup.centralizer_le_normalizer _ (Subgroup.mem_centralizer_iff.mpr ?_)
    rintro _ ⟨z, hz, rfl⟩
    have hzY : (z : G) ∈ zpowers y := by
      rw [← hYz]
      exact hz
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hzY
    have hz' : z = (⟨y, hYL hyY⟩ : ↥L) ^ k := Subtype.ext (by rw [Subgroup.coe_zpow]; exact hk.symm)
    rw [hz', map_zpow]
    exact (hwc.zpow_left k).eq
  obtain ⟨s, hsN, hsw⟩ := CFSG.GroupTheory.exists_mem_normalizer_mk'_eq (CFSG.pCore 2 ↥L) hN3 hA hwN
  have hsY : (s : G) ∈ normalizer (Y : Set G) := by
    have hs : s ∈ (normalizer (Y : Set G)).subgroupOf L := by
      rw [Subgroup.subgroupOf_normalizer_eq hYL]
      exact hsN
    exact hs
  set sM : ↥M := Subgroup.inclusion hLM s
  have heb : ((e w : ↥C) : Bar2 M) = π sM := by
    rw [← hsw]
    exact he s
  have hbC : π sM ∈ C := by
    rw [← heb]
    exact (e w).2
  have hb11 : orderOf (π sM) = 11 := by
    rw [← heb, Subgroup.orderOf_coe, MulEquiv.orderOf_eq, hw11]
  have ha11 : orderOf (π f₁) = 11 :=
    orderOf_mk_eq_of_isPGroup_two (N := CFSG.pCore 2 ↥M) CFSG.pCore_isPGroup (by norm_num)
      (by norm_num) hf₁
  have hab : Commute (π f₁) (π sM) := (Subgroup.mem_centralizer_iff.mp hf₁C _ hbC).symm
  have hbX : π sM ∉ zpowers (π f₁) := by
    intro hb
    have hbcent : π sM ∈ centralizer (C : Set (Bar2 M)) := zpowers_le.mpr hf₁C hb
    have hwZ : w ∈ center (Bar2 L) := by
      refine Subgroup.mem_center_iff.mpr fun g => e.injective ?_
      apply Subtype.ext
      rw [map_mul, map_mul, Subgroup.coe_mul, Subgroup.coe_mul, heb]
      exact Subgroup.mem_centralizer_iff.mp hbcent _ (e g).2
    rw [hZ, Subgroup.mem_bot] at hwZ
    rw [hwZ, orderOf_one] at hw11
    exact absurd hw11 (by norm_num)
  obtain ⟨hel, hcard⟩ := CFSG.GroupTheory.isElemAbelian_sup_zpowers_of_commute
    (X := zpowers (π f₁)) (by rw [Nat.card_zpowers, ha11]) hb11 hbX
    (fun a ha => by
      obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp ha
      exact (hab.zpow_left k).eq)
  have hle : zpowers (π f₁) ⊔ zpowers (π sM) ≤ ((M ⊓ normalizer (Y : Set G)).subgroupOf M).map π :=
    sup_le (zpowers_le.mpr (Subgroup.mem_map_of_mem π (Subgroup.mem_subgroupOf.mpr ⟨f₁.2, hf₁Y⟩)))
      (zpowers_le.mpr (Subgroup.mem_map_of_mem π (Subgroup.mem_subgroupOf.mpr ⟨sM.2, hsY⟩)))
  have h2 := CFSG.SectionRank.le_pRank (p := 11) (by norm_num) hle hel hcard
  have hker : ¬ 11 ∣ Nat.card ↥(MonoidHom.ker π) := by
    rw [hπ, QuotientGroup.ker_mk']
    obtain ⟨k, hk⟩ := (CFSG.pCore_isPGroup (p := 2) (G := ↥M)).exists_card_eq
    rw [hk]
    intro hd
    exact absurd ((Nat.prime_dvd_prime_iff_eq (by norm_num) Nat.prime_two).1
      ((by norm_num : Nat.Prime 11).dvd_of_dvd_pow hd)) (by norm_num)
  rw [CFSG.pRank_map_eq_of_not_dvd_card_ker π (QuotientGroup.mk'_surjective _) (by norm_num) hker]
    at h2
  have h3 := CFSG.SectionRank.pRank_le_map (p := 11) (by norm_num) M.subtype M.subtype_injective
    ((M ⊓ normalizer (Y : Set G)).subgroupOf M)
  rw [Subgroup.subgroupOf_map_subtype] at h3
  have h4 := CFSG.SectionRank.pRank_mono (p := 11) (by norm_num)
    (inf_le_left : (M ⊓ normalizer (Y : Set G)) ⊓ M ≤ M ⊓ normalizer (Y : Set G))
  exact lt_of_lt_of_le (by norm_num) (h2.trans (h3.trans h4))

theorem r880J4_of_r880J4G {G : Type} [Group G] [Finite G]
    {D : Data G}
    (hSg : UC6S846.SigmaStd D) (h76 : F07.R76Sig D) (h : R880J4G D) : R880J4 D := by
  intro L hL hJ4 hSE hsig
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have : Fact (Nat.Prime 11) := ⟨by norm_num⟩
  have h11 : 11 ∈ D.sig := by
    rw [hsig]
    exact Set.mem_singleton 11
  have h3 : 3 ∉ D.sig := by
    rw [hsig]
    norm_num
  have hLM : L ≤ D.M := hL.1.le
  have hN := le_normalizer_of_isSpor_J4 hSg hL hJ4 h3
  have hsp : IsStronglyPEmbedded 11 D.M :=
    UC6S846.sp_of_mem_sig hSg (UC6S846.not_solvable_of_mem_calC hL) h11
  have hZ : center (Bar2 L) = ⊥ :=
    CFSG.EvenSporadicStandard.J4Std.center_eq_bot_of_isSporadic hJ4
  obtain ⟨e, -⟩ := uc22p20d_bar2Equiv hLM hL.1
  have hCJ : IsSpor ↥((L.subgroupOf D.M).map (QuotientGroup.mk' (CFSG.pCore 2 ↥D.M))) .J4 := by
    obtain ⟨j⟩ := hJ4
    exact ⟨e.symm.trans j⟩
  obtain ⟨f, hf, hfC⟩ := exists_orderOf_eleven_mk_mem_centralizer hLM hN
    (fun B hB => card_le_of_isSpor_J4_of_isElemAbelian hCJ B hB) (hSg.three_le 11 h11)
  have hL3 : CFSG.Open.pRank 3 L = 2 :=
    (pRank_bar2_eq_of_odd (Y := L) Nat.prime_three (by norm_num)).symm.trans
      (PartOne.Section8.pRank_three_eq_two_of_isSpor_J4 hJ4)
  obtain ⟨E₀, hE₀L, hE₀el, hE₀card⟩ := CFSG.SectionRank.exists_pRank (p := 3) (by norm_num) L
  obtain ⟨S, hS⟩ := (hE₀el.isPGroup.comap_subtype : IsPGroup 3 (E₀.subgroupOf L)).exists_le_sylow
  obtain ⟨Q, hQdef⟩ : ∃ Q : Subgroup G, Q = (S : Subgroup ↥L).map L.subtype := ⟨_, rfl⟩
  have hQ : CFSG.ABGLocalTools.IsSylowOf 3 Q L := ⟨S, hQdef.symm⟩
  have hQL : Q ≤ L := by
    rw [hQdef]
    exact Subgroup.map_subtype_le _
  have hQp : IsPGroup 3 Q := by
    rw [hQdef]
    exact S.isPGroup'.map _
  have hE₀Q : E₀ ≤ Q := by
    rw [hQdef]
    exact fun x hx => ⟨⟨x, hE₀L hx⟩, hS (Subgroup.mem_subgroupOf.2 hx), rfl⟩
  have hQ2 : 2 ≤ CFSG.Open.pRank 3 Q :=
    CFSG.SectionRank.le_pRank (by norm_num) hE₀Q hE₀el (by rw [hE₀card, hL3])
  obtain ⟨f₁, hf₁, hf₁π, hf₁Q⟩ :=
    exists_conj_centralizer_of_mk_mem_centralizer hLM hQL hQp hf hfC
  have hf₁C : QuotientGroup.mk' (CFSG.pCore 2 ↥D.M) f₁ ∈ centralizer
      (((L.subgroupOf D.M).map (QuotientGroup.mk' (CFSG.pCore 2 ↥D.M)) :
        Subgroup (Bar2 D.M)) : Set (Bar2 D.M)) := by
    rw [hf₁π]
    exact hfC
  have hz11 : Nat.card (zpowers (f₁ : G)) = 11 := by
    rw [Nat.card_zpowers, Subgroup.orderOf_coe, hf₁]
  have hzQ : zpowers (f₁ : G) ≤ centralizer (Q : Set G) :=
    zpowers_le.mpr (Subgroup.mem_centralizer_iff.mpr fun q hq => (hf₁Q q hq).symm)
  have hX : ∀ X : Subgroup G, X ≤ Q → Nat.card X = 3 →
      normalizer (X : Set G) ≤ D.M ∧ 11 ∣ Nat.card (normalizer (X : Set G)) := by
    intro X hXQ hXcard
    obtain ⟨E, hXE, hEQ, hEel, hEcard⟩ :=
      CFSG.GroupTheory.exists_isElemAbelian_card_sq_of_le_of_card_prime hQp hQ2 hXQ hXcard
    have hzE : zpowers (f₁ : G) ≤ centralizer (E : Set G) :=
      hzQ.trans (Subgroup.centralizer_le hEQ)
    have hΓ : rankThreeGamma 1 3 E ≤ D.M := by
      refine h76 11 h11 (by norm_num) hsp 3 Nat.prime_three E (hEQ.trans (hQL.trans hLM)) hEel
        hEcard ?_ ?_
      · have := CFSG.SectionRank.le_pRank (p := 11) (by norm_num)
          (le_inf (zpowers_le.mpr f₁.2) hzE) (CFSG.GroupTheory.isElemAbelian_of_card_prime hz11)
          (k := 1) (by rw [hz11, pow_one])
        exact Nat.lt_of_lt_of_le Nat.zero_lt_one this
      · intro Y hYE hYcard
        exact one_lt_pRank_eleven_normalizer_of_commute hLM hL.1 hZ
          (fun x hx => exists_orderOf_eleven_commute_of_isSpor_J4 hJ4 x hx)
          ((hYE.trans hEQ).trans hQL) hYcard hf₁ hf₁C
          (Subgroup.centralizer_le_normalizer _
            ((hzQ.trans (Subgroup.centralizer_le (hYE.trans hEQ))) (Subgroup.mem_zpowers _)))
    refine ⟨(CFSG.HardMathSupport.Solomon.Proving.normalizer_le_glbCore (p := 3) (k := 1) hXE
      ?_).trans hΓ, ?_⟩
    · exact CFSG.SectionRank.le_pRank (p := 3) (by norm_num) le_rfl
        (CFSG.GroupTheory.isElemAbelian_of_card_prime hXcard) (by rw [hXcard, pow_one])
    · have hle : zpowers (f₁ : G) ≤ normalizer (X : Set G) :=
        (hzQ.trans (Subgroup.centralizer_le hXQ)).trans (Subgroup.centralizer_le_normalizer _)
      rw [← hz11]
      exact Subgroup.card_dvd_of_le hle
  exact h L hL hJ4 hSE hsig Q hQ (hsp.rankThreeGamma_one_le hQp hX)

end CFSG.LocalAnalysis.UniquenessCase.UC22.F08
