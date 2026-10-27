module

public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section7.KInputs
public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section7.LayerBasic
import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section7.RankBound
import CFSG.GroupTheory.PGroup.FrattiniQuotientRankBound
import CFSG.GroupTheory.PerfectGeneration
import CFSG.GroupTheory.FrattiniQuotient
import CFSG.FeitThompson.OddOrderTheorem
import CFSG.RankThree.PartTwo.Sec21.StronglyEmbedded
import CFSG.RankThree.PartTwo.Sec5.Bender.Core
import CFSG.GroupTheory.CentralizeSolvableOfPCores

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartOne.Section7

open CFSG.Open
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G]

namespace Sec7Core4

theorem commutator_layerLift_pCoreOf_eq_bot (k : Sec7Core4 G) {H : Subgroup G}
    (hH : Config k H)
    (hB : CoverActsTriviallyOnSmall k.p
      ↥(CFSG.generalizedFitting (↥H ⧸ CFSG.pPrimeCore k.p ↥H)))
    {q : ℕ} (hq : q.Prime) :
    ⁅layerLift k.p H, CFSG.Open.pCoreOf q ((CFSG.pPrimeCore k.p ↥H).map H.subtype)⁆ = ⊥ := by
  classical
  have hp : k.p.Prime := k.prime
  haveI : Fact k.p.Prime := ⟨hp⟩
  haveI : Fact q.Prime := ⟨hq⟩
  let K₀ : Subgroup ↥H := CFSG.pPrimeCore k.p ↥H
  let K : Subgroup G := K₀.map H.subtype
  let J : Subgroup G := layerLift k.p H
  let R : Subgroup G := CFSG.Open.pCoreOf q K
  have hRK : R ≤ K := CFSG.LieType.BorelTits.pCoreOf_le q K
  have hKcard : Nat.card K = Nat.card ↥K₀ :=
    Subgroup.card_map_of_injective H.subtype_injective
  have hKodd : Odd (Nat.card K) := by
    rw [hKcard]
    exact k.odd_card_pPrimeCore_of_not_le hH.not_le hH.two_le_pRank
  have hKcop : Nat.Coprime k.p (Nat.card K) := by
    rw [hKcard]
    exact CFSG.pPrimeCore_coprime_card
  have hHK : H ≤ Subgroup.normalizer (K : Set G) :=
    CFSG.ABGLocalTools.le_normalizer_map_subtype H K₀
  have hHR : H ≤ Subgroup.normalizer (R : Set G) :=
    hHK.trans (CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf q K)
  have hJR : J ≤ Subgroup.normalizer (R : Set G) := (layerLift_le k.p H).trans hHR
  by_cases hRne : R = ⊥
  · change ⁅J, R⁆ = ⊥
    rw [hRne, Subgroup.commutator_bot_right]
  have hRq : IsPGroup q R := CFSG.LieType.BorelTits.pCoreOf_isPGroup q K
  have hq2 : q ≠ 2 := by
    intro hqeq
    haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    have h2R : 2 ∣ Nat.card R := by
      rw [← hqeq]
      exact CFSG.RankThree.PartTwo.Sec21.dvd_card_of_isPGroup_ne_bot hRq hRne
    have h2K : 2 ∣ Nat.card K := h2R.trans (Subgroup.card_dvd_of_le hRK)
    exact Nat.not_even_iff_odd.mpr hKodd (even_iff_two_dvd.mpr h2K)
  have hqp : q ≠ k.p := by
    intro hqeq
    have hpR : k.p ∣ Nat.card R := by
      rw [← hqeq]
      exact CFSG.RankThree.PartTwo.Sec21.dvd_card_of_isPGroup_ne_bot hRq hRne
    have hpK : k.p ∣ Nat.card K := hpR.trans (Subgroup.card_dvd_of_le hRK)
    exact (hp.coprime_iff_not_dvd).mp hKcop hpK
  obtain ⟨D, hDR, hDN, hDexp, hDcl, hDfaith⟩ :=
    CFSG.RankThree.PartTwo.Sec5.Bender.exists_critical_faithful (p := q) hq2 hRq hRne
  have hJND : J ≤ Subgroup.normalizer (D : Set G) := fun j hj => hDN j (hJR hj)
  have hDq : IsPGroup q ↥D := hRq.to_le hDR
  have hDexp' : ∀ x : ↥D, x ^ q = 1 :=
    fun x => Subtype.ext (by simpa using hDexp (x : G) x.2)
  have hDrank : CFSG.Open.pRank q (⊤ : Subgroup ↥D) ≤ 3 := by
    rw [← CFSG.SectionRank.pRank_eq_pRank_top_subgroup (p := q) D]
    exact ((CFSG.SectionRank.pRank_mono hq.one_lt hDR).trans
      (CFSG.SectionRank.pRank_mono hq.one_lt hRK)).trans (k.pRank_pPrimeCore_le_three hH hq)
  have hDcl' : ⁅⁅(⊤ : Subgroup ↥D), (⊤ : Subgroup ↥D)⁆, (⊤ : Subgroup ↥D)⁆ = ⊥ := by
    rw [Subgroup.commutator_top_right_eq_bot_iff_le_center, Subgroup.commutator_le]
    intro a _ b _
    rw [Subgroup.mem_center_iff]
    intro g
    apply Subtype.ext
    have hmem : ⁅(a : G), (b : G)⁆ ∈ Subgroup.centralizer (D : Set G) :=
      hDcl (Subgroup.commutator_mem_commutator (H₁ := D) (H₂ := R) a.2 (hDR b.2))
    have hcommc := (Subgroup.mem_centralizer_iff.mp hmem) (g : G) g.2
    have hcoe : ((⁅a, b⁆ : ↥D) : G) = ⁅(a : G), (b : G)⁆ := map_commutatorElement D.subtype a b
    simpa only [Subgroup.coe_mul, hcoe] using hcommc
  have hVdata := CFSG.GroupTheory.frattini_elementary_quotient (p := q) hDq
  have hVcomm : ∀ a b : ↥D ⧸ frattini ↥D, a * b = b * a :=
    fun a b => hVdata.2.1.is_comm.comm a b
  have hVexp : ∀ v : ↥D ⧸ frattini ↥D, v ^ q = 1 := hVdata.2.2.1
  have hVcard : Nat.card (↥D ⧸ frattini ↥D) ≤ q ^ 4 :=
    CFSG.GroupTheory.card_quotient_frattini_le_pow_four hDq hDexp' hDcl' hDrank
  let conjD : ↥J →* MulAut ↥D :=
    D.normalizerMonoidHom.comp (Subgroup.inclusion hJND)
  let ρ : ↥J →* MulAut (↥D ⧸ frattini ↥D) :=
    (CFSG.OrderReductions.FrattiniAutomorphisms.quotientAutomorphism (frattini ↥D)).comp conjD
  let π : ↥H →* (↥H ⧸ K₀) := QuotientGroup.mk' K₀
  let Lbar : Subgroup (↥H ⧸ K₀) := CFSG.generalizedFitting (↥H ⧸ K₀)
  have hsimple := k.isSimpleGroup_generalizedFitting_quotient hH
  haveI : IsSimpleGroup ↥Lbar := hsimple.1
  have hLperf : ⁅Lbar, Lbar⁆ = Lbar :=
    Subgroup.isPerfect_iff.mp
      (CFSG.LocalCores.isQuasisimple_of_isSimpleGroup hsimple.2.1).1.1
  have hmapJ : (J.subgroupOf H).map π = Lbar := map_layerLift_eq k.p H hLperf
  let φ0 : ↥J →* (↥H ⧸ K₀) := π.comp (Subgroup.inclusion (layerLift_le k.p H))
  have hφ0mem : ∀ x : ↥J, φ0 x ∈ Lbar := by
    intro x
    have hx : Subgroup.inclusion (layerLift_le k.p H) x ∈ J.subgroupOf H := by
      rw [Subgroup.mem_subgroupOf]
      exact x.2
    have hmem : π (Subgroup.inclusion (layerLift_le k.p H) x) ∈ (J.subgroupOf H).map π :=
      Subgroup.mem_map_of_mem π hx
    rw [hmapJ] at hmem
    simpa [φ0] using hmem
  let φ : ↥J →* ↥Lbar := φ0.codRestrict Lbar hφ0mem
  have hφsurj : Function.Surjective φ := by
    intro y
    have hy : (y : ↥H ⧸ K₀) ∈ (J.subgroupOf H).map π := by
      rw [hmapJ]
      exact y.2
    obtain ⟨h, hh, hhval⟩ := Subgroup.mem_map.mp hy
    have hmemJ : (h : G) ∈ J := Subgroup.mem_subgroupOf.mp hh
    refine ⟨⟨(h : G), hmemJ⟩, ?_⟩
    apply Subtype.ext
    change π (Subgroup.inclusion (layerLift_le k.p H) ⟨(h : G), hmemJ⟩) = (y : ↥H ⧸ K₀)
    rw [show Subgroup.inclusion (layerLift_le k.p H) ⟨(h : G), hmemJ⟩ = h from Subtype.ext rfl]
    exact hhval
  have hker_mem : ∀ x : ↥J, φ x = 1 →
      Subgroup.inclusion (layerLift_le k.p H) x ∈ K₀ := by
    intro x hx
    have hx' : φ0 x = 1 := by
      have := congrArg Subtype.val hx
      simpa [φ] using this
    have hx'' : π (Subgroup.inclusion (layerLift_le k.p H) x) = 1 := by
      simpa [φ0] using hx'
    exact (QuotientGroup.eq_one_iff _).mp hx''
  let ψ0 : φ.ker →* ↥H := (Subgroup.inclusion (layerLift_le k.p H)).comp φ.ker.subtype
  have hψ0mem : ∀ x : φ.ker, ψ0 x ∈ K₀ :=
    fun x => hker_mem x.1 (MonoidHom.mem_ker.mp x.2)
  let ψ : φ.ker →* ↥K₀ := ψ0.codRestrict K₀ hψ0mem
  have hψinj : Function.Injective ψ := by
    intro x y hxy
    have h0 : ψ0 x = ψ0 y := congrArg Subtype.val hxy
    have h1 : Subgroup.inclusion (layerLift_le k.p H) (φ.ker.subtype x) =
        Subgroup.inclusion (layerLift_le k.p H) (φ.ker.subtype y) := by
      simpa [ψ0] using h0
    exact Subtype.ext (Subgroup.inclusion_injective (layerLift_le k.p H) h1)
  have hK₀odd : Odd (Nat.card ↥K₀) :=
    k.odd_card_pPrimeCore_of_not_le hH.not_le hH.two_le_pRank
  have hK₀solv : Group.IsSolvable ↥K₀ := CFSG.FeitThompson.isSolvable_of_odd_natCard ↥K₀ hK₀odd
  have hksolv : Group.IsSolvable φ.ker := by
    haveI : Group.IsSolvable ↥K₀ := hK₀solv
    exact Group.isSolvable_of_isSolvable_injective (f := ψ) hψinj
  have hker_dvd : Nat.card φ.ker ∣ Nat.card ↥K₀ :=
    Subgroup.card_dvd_of_injective ψ hψinj
  have hK₀cop : Nat.Coprime k.p (Nat.card ↥K₀) := CFSG.pPrimeCore_coprime_card
  have hcop2 : Nat.Coprime (Nat.card φ.ker) 2 :=
    (Nat.Coprime.coprime_dvd_right hker_dvd (Nat.coprime_two_left.mpr hK₀odd)).symm
  have hcopp : Nat.Coprime (Nat.card φ.ker) k.p :=
    (Nat.Coprime.coprime_dvd_right hker_dvd hK₀cop).symm
  have hcop : Nat.Coprime (Nat.card φ.ker) (2 * k.p) := hcop2.mul_right hcopp
  have hJperfect : Group.IsPerfect ↥J :=
    Subgroup.isPerfect_iff.mpr (commutator_layerLift k.p H)
  unfold CoverActsTriviallyOnSmall at hB
  have hρ : ρ = 1 :=
    hB ↥J hJperfect φ hφsurj hcop hksolv q hq hq2 hqp
      (↥D ⧸ frattini ↥D) hVcomm hVexp hVcard ρ
  have hstep5 : ∀ j : ↥J, ¬ q ∣ orderOf j →
      (j : G) ∈ Subgroup.centralizer (R : Set G) := by
    intro j hjq
    have hρj : ρ j = 1 := by rw [hρ]; rfl
    have hquot1 : (CFSG.OrderReductions.FrattiniAutomorphisms.quotientAutomorphism
        (frattini ↥D)) (conjD j) = 1 := by
      simpa [ρ] using hρj
    have hmemker : conjD j ∈ (CFSG.OrderReductions.FrattiniAutomorphisms.quotientAutomorphism
        (frattini ↥D)).ker := MonoidHom.mem_ker.mpr hquot1
    have hqker : IsPGroup q ((CFSG.OrderReductions.FrattiniAutomorphisms.quotientAutomorphism
        (frattini ↥D)).ker) :=
      (CFSG.GroupTheory.frattini_automorphism_kernel hDq).2
    obtain ⟨k, hk⟩ := IsPGroup.iff_orderOf.mp hqker ⟨conjD j, hmemker⟩
    have hord_eq : orderOf (conjD j) = q ^ k := by
      rw [← hk]
      exact (Subgroup.orderOf_mk (conjD j) hmemker).symm
    have hdvd : orderOf (conjD j) ∣ orderOf j := orderOf_map_dvd conjD j
    have hk0 : k = 0 := by
      by_contra hkne
      have hqk : q ∣ orderOf (conjD j) := by
        rw [hord_eq]
        exact dvd_pow_self q hkne
      exact hjq (hqk.trans hdvd)
    have hconj1 : conjD j = 1 := by
      apply orderOf_eq_one_iff.mp
      rw [hord_eq, hk0, pow_zero]
    have hconj1' : D.normalizerMonoidHom ⟨(j : G), hJND j.2⟩ = 1 := by
      rw [show (⟨(j : G), hJND j.2⟩ : Subgroup.normalizer (D : Set G)) =
        Subgroup.inclusion hJND j from Subtype.ext rfl]
      simpa [conjD] using hconj1
    have hmem : (⟨(j : G), hJND j.2⟩ : Subgroup.normalizer (D : Set G)) ∈
        D.normalizerMonoidHom.ker := MonoidHom.mem_ker.mpr hconj1'
    rw [Subgroup.normalizerMonoidHom_ker, Subgroup.mem_subgroupOf] at hmem
    have hordj : orderOf (j : G) = orderOf j :=
      (Subgroup.orderOf_mk (j : G) j.2).symm
    have hnotdvd : ¬ q ∣ Nat.card (Subgroup.zpowers (j : G)) := by
      rw [Nat.card_zpowers, hordj]
      exact hjq
    exact hDfaith (Subgroup.zpowers (j : G)) hnotdvd
      (Subgroup.zpowers_le.mpr (hJR j.2))
      (Subgroup.zpowers_le.mpr hmem) (Subgroup.mem_zpowers (j : G))
  let CJ : Subgroup G := J ⊓ Subgroup.centralizer (R : Set G)
  have hJC : J ≤ Subgroup.normalizer (CJ : Set G) := by
    have key : ∀ g ∈ J, ∀ c ∈ CJ, g * c * g⁻¹ ∈ CJ := by
      intro g hg c hc
      obtain ⟨hcJ, hcC⟩ := Subgroup.mem_inf.mp hc
      refine Subgroup.mem_inf.mpr ⟨J.mul_mem (J.mul_mem hg hcJ) (J.inv_mem hg), ?_⟩
      rw [Subgroup.mem_centralizer_iff] at hcC ⊢
      intro r hr
      have hgr : g⁻¹ * r * g ∈ R := by
        have h := (Subgroup.mem_normalizer_iff.mp (hJR (J.inv_mem hg)) r).mp hr
        simpa using h
      have hc' := hcC (g⁻¹ * r * g) hgr
      calc r * (g * c * g⁻¹) = g * (g⁻¹ * r * g) * c * g⁻¹ := by group
        _ = g * ((g⁻¹ * r * g) * c) * g⁻¹ := by group
        _ = g * (c * (g⁻¹ * r * g)) * g⁻¹ := by rw [hc']
        _ = (g * c * g⁻¹) * r := by group
    intro g hg
    rw [Subgroup.mem_normalizer_iff]
    intro c
    constructor
    · intro hc
      exact key g hg c hc
    · intro hc
      have hc' := key g⁻¹ (J.inv_mem hg) (g * c * g⁻¹) hc
      have heq : g⁻¹ * (g * c * g⁻¹) * (g⁻¹)⁻¹ = c := by group
      rwa [heq] at hc'
  let C : Subgroup ↥J := CJ.subgroupOf J
  haveI : C.Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer (show CJ ≤ J from inf_le_left)).mpr hJC
  have hC : ∀ x : ↥J, ¬ q ∣ orderOf x → x ∈ C := by
    intro x hx
    have hxJ : (x : G) ∈ J := x.2
    have hxR : (x : G) ∈ Subgroup.centralizer (R : Set G) := hstep5 x hx
    exact Subgroup.mem_subgroupOf.mpr (Subgroup.mem_inf.mpr ⟨hxJ, hxR⟩)
  have hCtop : C = ⊤ :=
    CFSG.GroupTheory.eq_top_of_isPerfect_of_forall_not_dvd_orderOf_mem hq hJperfect hC
  have hJcentR : J ≤ Subgroup.centralizer (R : Set G) := by
    intro j hj
    have hjC : (⟨j, hj⟩ : ↥J) ∈ C := by
      rw [hCtop]
      exact Subgroup.mem_top _
    exact (Subgroup.mem_subgroupOf.mp hjC).2
  exact Subgroup.commutator_eq_bot_iff_le_centralizer.mpr hJcentR

theorem step75_of_coverActsTriviallyOnSmall (k : Sec7Core4 G)
    (hB : ∀ H : Subgroup G, Config k H →
      CoverActsTriviallyOnSmall k.p
        ↥(CFSG.generalizedFitting (↥H ⧸ CFSG.pPrimeCore k.p ↥H))) :
    Step75 k := by
  intro H hH
  have hp : k.p.Prime := k.prime
  haveI : Fact k.p.Prime := ⟨hp⟩
  let K₀ : Subgroup ↥H := CFSG.pPrimeCore k.p ↥H
  let K : Subgroup G := K₀.map H.subtype
  have hKcard : Nat.card K = Nat.card ↥K₀ :=
    Subgroup.card_map_of_injective H.subtype_injective
  have hKodd : Odd (Nat.card K) := by
    rw [hKcard]
    exact k.odd_card_pPrimeCore_of_not_le hH.not_le hH.two_le_pRank
  have hKsolv : Group.IsSolvable ↥K := CFSG.FeitThompson.isSolvable_of_odd_natCard ↥K hKodd
  have hJK : layerLift k.p H ≤ Subgroup.normalizer (K : Set G) :=
    (layerLift_le k.p H).trans (CFSG.ABGLocalTools.le_normalizer_map_subtype H K₀)
  exact CFSG.GroupTheory.commutator_eq_bot_of_forall_pCoreOf hKsolv
    (commutator_layerLift k.p H) hJK
    (fun q hq => commutator_layerLift_pCoreOf_eq_bot k hH (hB H hH) hq)

end Sec7Core4

end CFSG.LocalAnalysis.UniquenessCase.PartOne.Section7
