module

public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.BGsection16.theorem_16_B
import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.PFsection2.PFsection2_1
import Mathlib.GroupTheory.Schreier
import Mathlib.Order.Preorder.Finite

namespace CFSG
end CFSG
open CFSG

open scoped Pointwise

/-! # Theorem 16 c from BG Section 16 -/

section MainResults

variable {G : Type*} [Group G] [Finite G] [IsMinCE G]
omit [Finite G] [IsMinCE G] in
private theorem CFSG.section16_primeOrderSubgroupOf_to_section12
    {X H : Subgroup G}
    (hX : section16PrimeOrderSubgroupOf X H) :
    X ∈ section12PrimeOrderSubgroups H := by
  rcases hX with ⟨hXH, hprime⟩
  rcases hprime with ⟨p, hp⟩
  exact ⟨hXH, ⟨p, hp⟩⟩

omit [IsMinCE G] in
public theorem CFSG.section16_exists_primeOrderSubgroup_of_ne_bot
    {H : Subgroup G}
    (hHne : H ≠ ⊥) :
    ∃ X : Subgroup G, X ∈ section12PrimeOrderSubgroups H := by
  classical
  have hcard_ne_one : Nat.card H ≠ 1 := by
    intro hcard
    exact hHne ((Subgroup.card_eq_one (H := H)).1 hcard)
  rcases Nat.exists_prime_and_dvd hcard_ne_one with ⟨p, hpprime, hpdiv⟩
  haveI : Fact p.Prime := ⟨hpprime⟩
  rcases exists_prime_orderOf_dvd_card' (G := H) p hpdiv with ⟨zH, hzH_order⟩
  let z : G := zH
  refine ⟨Subgroup.zpowers z, ?_⟩
  have hzH : z ∈ H := zH.property
  have hz_order : orderOf z = p := by
    simpa [z, Subgroup.orderOf_coe] using hzH_order
  refine ⟨Subgroup.zpowers_le.mpr hzH, ⟨⟨p, hpprime⟩, ?_⟩⟩
  simp [z, Nat.card_zpowers, hz_order]

omit [Finite G] [IsMinCE G] in
private theorem CFSG.section16_section14TISet_to_section16TISubset
    {X : Set G}
    (hTI : section14TISet X) :
    section16TISubset X := by
  classical
  intro g
  by_cases hg : g ∈ Subgroup.normalizer X
  · left
    ext x
    constructor
    · intro hx
      rcases hx with ⟨y, hyX, rfl⟩
      have hgnorm : ∀ n : G, n ∈ X ↔ g * n * g⁻¹ ∈ X := hg
      exact (hgnorm y).1 hyX
    · intro hx
      have hginv : g⁻¹ ∈ Subgroup.normalizer X :=
        (Subgroup.normalizer X).inv_mem hg
      have hyX : g⁻¹ * x * g ∈ X := by
        have hginvnorm :
            ∀ n : G, n ∈ X ↔ g⁻¹ * n * (g⁻¹)⁻¹ ∈ X := hginv
        simpa using (hginvnorm x).1 hx
      exact ⟨g⁻¹ * x * g, hyX, by group⟩
  · right
    have hginv : g⁻¹ ∉ Subgroup.normalizer X := by
      intro hginv
      exact hg (by simpa using (Subgroup.normalizer X).inv_mem hginv)
    intro x hx
    have hx14 : x ∈ X ∩ section14SetConjBy X g⁻¹ := by
      constructor
      · exact hx.1
      · rcases hx.2 with ⟨y, hyX, hxy⟩
        exact ⟨y, hyX, by simpa [section14SetConjBy] using hxy⟩
    exact hTI.2 g⁻¹ hginv hx14

omit [Finite G] [IsMinCE G] in
public theorem CFSG.section16_section14TISet_to_section16TISubsetWithNormalizer
    {X : Set G} {N : Subgroup G}
    (hTI : section14TISet X)
    (hNorm : Subgroup.normalizer X = N) :
    section16TISubsetWithNormalizer X N :=
  ⟨section16_section14TISet_to_section16TISubset (G := G) hTI, hNorm⟩

omit [IsMinCE G] in
public theorem CFSG.section16_MFamilyP1_of_U_eq_bot
    {M K U : Subgroup G}
    (hMP : M ∈ section14MFamilyP G)
    (hKU : section15KUData M K U)
    (hUbot : U = ⊥) :
    M ∈ section14MFamilyP1 G := by
  classical
  have hUHall := hKU.2.2.2.1
  refine ⟨hMP, ?_⟩
  ext p
  constructor
  · intro hpκ
    rcases hpκ with ⟨hpτ, P, hP, _hCent⟩
    refine ⟨?_, ?_⟩
    · rw [subgroupPrimeSet]
      change p.val ∣ Nat.card M
      rw [← hP.2]
      exact Subgroup.card_dvd_of_le hP.1
    · rcases hpτ with hpτ1 | hpτ3
      · exact hpτ1.1
      · exact hpτ3.1
  · intro hp
    by_contra hpκ
    have hpcompl :
        p ∈ ((section14KappaPrimes M ∪ section10SigmaPrimes M)ᶜ) := by
      intro hpκσ
      rcases hpκσ with hpκ' | hpσ
      · exact hpκ hpκ'
      · exact hp.2 hpσ
    have hUsub_bot : U.subgroupOf M = ⊥ := by
      ext x
      constructor
      · intro hx
        have hxU : (x : G) ∈ U := by
          simpa [Subgroup.mem_subgroupOf] using hx
        have hxbot : (x : G) ∈ (⊥ : Subgroup G) := by
          simpa [hUbot] using hxU
        exact Subtype.ext (Subgroup.mem_bot.mp hxbot)
      · intro hx
        have hxone : x = 1 := Subgroup.mem_bot.mp hx
        simp [hxone]
    have hpidx : p.val ∣ (U.subgroupOf M).index := by
      simpa [hUsub_bot, subgroupPrimeSet, Subgroup.index_bot] using hp.1
    exact (hUHall.2.p_in_pi_of_p_dvd_index p hpidx) hpcompl

omit [IsMinCE G] in
public theorem CFSG.section16_U_ne_bot_of_MFamilyP2
    {M K U : Subgroup G}
    (hKU : section15KUData M K U)
    (hP2 : M ∈ section14MFamilyP2 G) :
    U ≠ ⊥ := by
  intro hUbot
  exact hP2.2 (section16_MFamilyP1_of_U_eq_bot (G := G) hP2.1 hKU hUbot).2

private theorem CFSG.section16_proposition14_2AData_of_section15
    {M K U : Subgroup G}
    (hM : M ∈ section9MaximalSubgroups G)
    (hKU : section15KUData M K U)
    (hKne : K ≠ ⊥) :
    section14Proposition14_2AData M K U := by
  classical
  have hMP : M ∈ section14MFamilyP G :=
    section16_MFamilyP_of_nontrivial_hall_kappa (G := G) hM hKU.1 hKne
  obtain ⟨U₀, hU₀⟩ :=
    proposition_14_2_a (G := G) (M := M) (K := K) hMP hKU.1
  exact ⟨hU₀.1, (lemma_15_1_b (G := G) (M := M) (K := K) (U := U)
    hM hKU hKne).2, hKU.2.2.2.1, hKU.2.2.2.2.1,
    ⟨hKU.2.1, hKU.2.2.2.2.2.1⟩⟩

private theorem CFSG.section16_Kstar_prime_order_of_U_eq_bot
    {M K U : Subgroup G}
    (hMP : M ∈ section14MFamilyP G)
    (hKU : section15KUData M K U)
    (hUbot : U = ⊥) :
    section16HasPrimeOrder (section16Kstar M K) := by
  have hP1 : M ∈ section14MFamilyP1 G :=
    section16_MFamilyP1_of_U_eq_bot (G := G) hMP hKU hUbot
  rcases theorem_14_7_f (G := G) (M := M) (K := K) hMP hKU.1 with hfirst | hsecond
  · exact False.elim (hfirst.1.2 hP1.2)
  · exact
      section16_hasPrimeOrder_of_prime_card (G := G) (K := section16Kstar M K) (by
        simpa [section16Kstar, section14KStar] using hsecond.2)

public theorem CFSG.section16_normalizer_U_not_le_M
    {M K U : Subgroup G}
    (hM : M ∈ section9MaximalSubgroups G)
    (hKU : section15KUData M K U)
    (hKne : K ≠ ⊥) :
    ¬ Subgroup.normalizer (U : Set G) ≤ M := by
  classical
  by_cases hUbot : U = ⊥
  · intro hNormLe
    have htop_le_M : (⊤ : Subgroup G) ≤ M := by
      intro g _hg
      have hgNorm : g ∈ Subgroup.normalizer (U : Set G) := by
        rw [Subgroup.mem_normalizer_iff]
        intro n
        simp [hUbot]
      exact hNormLe hgNorm
    exact hM.1 (top_le_iff.mp htop_le_M)
  · intro hNormLe
    have hP2 : M ∈ section14MFamilyP2 G :=
      section16_MFamilyP2_of_nontrivial_U (G := G) hM hKU hKne hUbot
    rcases Nat.exists_prime_and_dvd (n := Nat.card U) (by
        intro hcard
        exact hUbot ((Subgroup.card_eq_one (H := U)).1 hcard)) with
      ⟨r0, hr0prime, hr0dvd⟩
    let r : Nat.Primes := ⟨r0, hr0prime⟩
    have hrU : r ∈ subgroupPrimeSet U := by
      change r0 ∣ Nat.card U
      exact hr0dvd
    let R : Sylow r.val U := Classical.choice (Sylow.nonempty (p := r.val) (G := U))
    let P : Subgroup G := section10AmbientSylowSubgroup U R
    have hP_le_U : P ≤ U := by
      intro x hxP
      rcases Subgroup.mem_map.mp hxP with ⟨y, _hyR, rfl⟩
      exact y.2
    have hP_ne : P ≠ ⊥ := by
      haveI : Fact r.val.Prime := ⟨r.property⟩
      have hR_ne : (R : Subgroup U) ≠ ⊥ :=
        Sylow.ne_bot_of_dvd_card (G := U) R hrU
      intro hPbot
      have hmap_bot : (R : Subgroup U).map U.subtype = (⊥ : Subgroup G) := by
        simpa [P, section10AmbientSylowSubgroup] using hPbot
      have hRbot : (R : Subgroup U) = ⊥ :=
        (Subgroup.map_eq_bot_iff_of_injective
          (H := (R : Subgroup U)) (f := U.subtype) U.subtype_injective).1 hmap_bot
      exact hR_ne hRbot
    have hP_ne_top : P ≠ ⊤ := by
      have hUHall := hKU.2.2.2.1
      intro hPtop
      have htop_le_M : (⊤ : Subgroup G) ≤ M := by
        simpa [P, hPtop] using hP_le_U.trans hUHall.1
      exact hM.1 (top_le_iff.mp htop_le_M)
    have hNormP_ne_top : Subgroup.normalizer (P : Set G) ≠ ⊤ := by
      intro hNormPtop
      have hPnormal : P.Normal := Subgroup.normalizer_eq_top_iff.mp hNormPtop
      letI : IsSimpleGroup G := IsMinCE.simple
      rcases hPnormal.eq_bot_or_eq_top with hPbot | hPtop
      · exact hP_ne hPbot
      · exact hP_ne_top hPtop
    obtain ⟨H, hH⟩ :=
      section9_exists_maximalSubgroupsContaining_of_ne_top
        (G := G) (H := Subgroup.normalizer (P : Set G)) hNormP_ne_top
    have h14 : section14Theorem14_7Data M K (section14Theorem14_7Partner M K) :=
      theorem_14_7_data (G := G) (M := M) (K := K) hP2.1 hKU.1
    have hU14 : section14Proposition14_2AData M K U :=
      section16_proposition14_2AData_of_section15 (G := G) hM hKU hKne
    have hcor :=
      corollary_14_12 (G := G) (M := M) (K := K)
        (Mstar := section14Theorem14_7Partner M K) (U := U)
        hP2 hKU.1 h14 hU14 (r := r) hrU R (H := H) (by
          simpa [P] using hH)
    exact hcor.2.2.2.1 (by
      intro x hx
      exact hNormLe (mem_subgroupNormalizerIn.mp hx).1)

private theorem CFSG.section16_theoremC_partner_unique
    {M K N : Subgroup G}
    (hMP : M ∈ section14MFamilyP G)
    (hKHall : section12HallSubgroupIn (section14KappaPrimes M) K M)
    (hKne : K ≠ ⊥)
    (hNP : N ∈ section14MFamilyP G)
    (hK_eq : K = section14KStar N (section14KStar M K))
    (hKstarHall : section12HallSubgroupIn
      (section14KappaPrimes N) (section14KStar M K) N) :
    N = section14Theorem14_7Partner M K := by
  classical
  rcases section16_exists_primeOrderSubgroup_of_ne_bot (G := G) hKne with ⟨Y, hYK⟩
  have hPartnerUnique :
      section9MaximalSubgroupsContaining (Subgroup.centralizer (Y : Set G)) =
        {section14Theorem14_7Partner M K} :=
    theorem_14_7_a (G := G) (M := M) (K := K) hMP hKHall Y hYK
  have hYNKstar :
      Y ∈ section12PrimeOrderSubgroups (section14KStar N (section14KStar M K)) := by
    simpa [← hK_eq] using hYK
  have hNUnique :
      section9MaximalSubgroupsContaining (Subgroup.centralizer (Y : Set G)) = {N} :=
    (proposition_14_2_c
      (G := G) (M := N) (K := section14KStar M K) hNP hKstarHall).2 Y hYNKstar
  have hNmem :
      N ∈ section9MaximalSubgroupsContaining (Subgroup.centralizer (Y : Set G)) := by
    rw [hNUnique]
    simp
  have hNmemPartner :
      N ∈ ({section14Theorem14_7Partner M K} : Set (Subgroup G)) := by
    simpa [hPartnerUnique] using hNmem
  simpa using hNmemPartner

omit [Finite G] [IsMinCE G] in
private theorem CFSG.section16_conjugatesBySet_TI_of_outside_disjoint
    {M : Subgroup G} {X : Set G}
    (hXM : X ⊆ M)
    (hOutside : ∀ g : G, g ∉ M → X ∩ (M.conjBy g : Set G) = ∅) :
    section16TISubset (section16ConjugatesOfSetBySet X (M : Set G)) := by
  classical
  let T : Set G := section16ConjugatesOfSetBySet X (M : Set G)
  intro g
  by_cases hgM : g ∈ M
  · left
    ext z
    constructor
    · intro hz
      rcases hz with ⟨t, htT, rfl⟩
      rcases htT with ⟨x, hxX, y, hyM, rfl⟩
      refine ⟨x, hxX, g * y, M.mul_mem hgM hyM, ?_⟩
      group
    · intro hzT
      rcases hzT with ⟨x, hxX, y, hyM, rfl⟩
      refine ⟨g⁻¹ * (y * x * y⁻¹) * g, ?_, ?_⟩
      · refine ⟨x, hxX, g⁻¹ * y, M.mul_mem (M.inv_mem hgM) hyM, ?_⟩
        group
      · group
  · right
    intro z hz
    rcases hz with ⟨hzT, hzConj⟩
    rcases hzT with ⟨x, hxX, y, hyM, hz_eq⟩
    rcases hzConj with ⟨w, hwT, hzw⟩
    rcases hwT with ⟨x', hx'X, y', hy'M, hw_eq⟩
    let h : G := y⁻¹ * g * y'
    have hh_notM : h ∉ M := by
      intro hhM
      have hgM' : g ∈ M := by
        have hg_eq : g = y * h * y'⁻¹ := by
          dsimp [h]
          group
        rw [hg_eq]
        exact M.mul_mem (M.mul_mem hyM hhM) (M.inv_mem hy'M)
      exact hgM hgM'
    have hx_conj :
        x ∈ (M.conjBy h : Subgroup G) := by
      rw [Subgroup.conjBy, Subgroup.mem_map]
      refine ⟨x', hXM hx'X, ?_⟩
      simp [MulAut.conj_apply]
      have hmain := congrArg (fun t : G => y⁻¹ * t * y) (hz_eq.symm.trans hzw)
      dsimp [h] at hmain ⊢
      simp [hw_eq, mul_assoc] at hmain
      simpa [mul_assoc] using hmain.symm
    have hx_empty : x ∈ (∅ : Set G) := by
      simpa [hOutside h hh_notM] using (show x ∈ X ∩ (M.conjBy h : Set G) from
        ⟨hxX, hx_conj⟩)
    simp at hx_empty

omit [Finite G] [IsMinCE G] in
private theorem CFSG.section16_kappa_subset_not_sigma
    {M : Subgroup G} :
    section14KappaPrimes M ⊆ (section10SigmaPrimes M)ᶜ := by
  intro p hpκ hpσ
  exact section12_tau13_not_sigma hpκ.1 hpσ

public theorem CFSG.section16_primeSupport_subset_sigma_of_msigmaMember
    {x : G} {M : Subgroup G} (hM : M ∈ section14MsigmaElement x) :
    section14ElementPrimeSupport x ⊆ section10SigmaPrimes M := by
  intro p hp
  exact ((theorem_10_2_b (G := G) hM.1).1).p_in_pi_of_p_dvd_card p <|
    section8_subgroupPrimeSet_mono
      (Subgroup.zpowers_le.2 (hM.2 (by simp))) hp

public theorem CFSG.section16_mem_msigma_of_primeSupport_subset
    {M : Subgroup G}
    (hM : M ∈ section9MaximalSubgroups G)
    {x : G} (hxM : x ∈ M)
    (hxσ : section14ElementPrimeSupport x ⊆ section10SigmaPrimes M) :
    x ∈ section10Msigma M := by
  let q : M →* M ⧸ section10MsigmaSubgroup M :=
    QuotientGroup.mk' (section10MsigmaSubgroup M)
  have hxQ_dvd_order : orderOf (q ⟨x, hxM⟩) ∣ orderOf x := by
    simpa [q] using orderOf_map_dvd (ψ := q) ⟨x, hxM⟩
  have hxQ_dvd_index : orderOf (q ⟨x, hxM⟩) ∣ (section10MsigmaSubgroup M).index := by
    have hxQ_dvd_card :
        orderOf (q ⟨x, hxM⟩) ∣ Nat.card (M ⧸ section10MsigmaSubgroup M) := by
      simpa using orderOf_dvd_natCard (q ⟨x, hxM⟩)
    simpa [Subgroup.index_eq_card] using hxQ_dvd_card
  have hcop : Nat.Coprime (orderOf x) (section10MsigmaSubgroup M).index := by
    refine Nat.coprime_of_dvd ?_
    intro p hpprime hpx hpidx
    let p' : Nat.Primes := ⟨p, hpprime⟩
    have hpSupp : p' ∈ section14ElementPrimeSupport x := by
      change p' ∈ subgroupPrimeSet (Subgroup.zpowers x)
      change p' ∈ {q : Nat.Primes | q.val ∣ Nat.card (Subgroup.zpowers x)}
      change p ∣ Nat.card (Subgroup.zpowers x)
      rw [Nat.card_zpowers]
      exact hpx
    have hpσ : p' ∈ section10SigmaPrimes M := hxσ hpSupp
    exact (((theorem_10_2_b (G := G) hM).2).p_in_pi_of_p_dvd_index p' hpidx) hpσ
  have hxQ1 : orderOf (q ⟨x, hxM⟩) = 1 :=
    Nat.eq_one_of_dvd_coprimes hcop hxQ_dvd_order hxQ_dvd_index
  have hxQeq1 : q ⟨x, hxM⟩ = 1 := (orderOf_eq_one_iff).mp hxQ1
  rw [section10Msigma, Subgroup.mem_map]
  refine ⟨⟨x, hxM⟩, ?_, rfl⟩
  simpa [q, QuotientGroup.ker_mk'] using
    (MonoidHom.mem_ker (f := q) (x := ⟨x, hxM⟩)).2 hxQeq1

omit [Finite G] [IsMinCE G] in
public theorem CFSG.section16_elementPrimeSupport_conj_subset
    {x g : G} :
    section14ElementPrimeSupport (g * x * g⁻¹) ⊆ section14ElementPrimeSupport x := by
  intro p hp
  have hconj_order : orderOf (g * x * g⁻¹) = orderOf x := by
    simpa [MulAut.conj_apply] using (MulAut.conj g).orderOf_eq x
  simpa [section14ElementPrimeSupport, subgroupPrimeSet, Nat.card_zpowers, hconj_order]
    using hp

public theorem CFSG.section16_msigma_inf_conjBy_eq
    {M : Subgroup G}
    (hM : M ∈ section9MaximalSubgroups G) (g : G) :
    section10Msigma M ⊓ M.conjBy g =
      section10Msigma M ⊓ (section10Msigma M).conjBy g := by
  apply le_antisymm
  · intro x hx
    refine ⟨hx.1, ?_⟩
    rcases Subgroup.mem_map.mp hx.2 with ⟨y, hyM, hyx⟩
    have hyσ : section14ElementPrimeSupport y ⊆ section10SigmaPrimes M := by
      intro p hp
      have hy_eq : y = g⁻¹ * x * g := by
        rw [← hyx]
        change y = g⁻¹ * (g * y * g⁻¹) * g
        group
      have hp' : p ∈ section14ElementPrimeSupport x := by
        have hsubset :=
          section16_elementPrimeSupport_conj_subset (G := G) (x := x) (g := g⁻¹)
        have hp_conj :
            p ∈ section14ElementPrimeSupport (g⁻¹ * x * (g⁻¹)⁻¹) := by
          simpa [hy_eq] using hp
        exact hsubset hp_conj
      exact section16_primeSupport_subset_sigma_of_msigmaMember
        (G := G) (x := x) (M := M) ⟨hM, by simpa using hx.1⟩ hp'
    have hyMsigma : y ∈ section10Msigma M :=
      section16_mem_msigma_of_primeSupport_subset (G := G) hM hyM hyσ
    change x ∈ Subgroup.map (MulAut.conj g).toMonoidHom (section10Msigma M)
    exact ⟨y, hyMsigma, hyx⟩
  · intro x hx
    exact ⟨hx.1, (Subgroup.map_mono (section16_msigma_le (G := G) M)) hx.2⟩

omit [IsMinCE G] in
public theorem CFSG.section16_sigmaPrimes_conjBy
    (M : Subgroup G) (a : G) :
    section10SigmaPrimes (M.conjBy a) = section10SigmaPrimes M := by
  ext p
  constructor
  · intro hp
    have hpBack := section10_sigma_conjBy (M := M.conjBy a) hp a⁻¹
    simpa [section10_conjBy_inv] using hpBack
  · intro hp
    exact section10_sigma_conjBy (M := M) hp a

public theorem CFSG.section16_mem_msigma_conjBy
    {M : Subgroup G}
    (hM : M ∈ section9MaximalSubgroups G)
    {x a : G} (hx : x ∈ section10Msigma M) :
    a * x * a⁻¹ ∈ section10Msigma (M.conjBy a) := by
  have hxM : x ∈ M := section16_msigma_le (G := G) M hx
  have hx_conj_M : a * x * a⁻¹ ∈ M.conjBy a := by
    exact Subgroup.mem_map.mpr ⟨x, hxM, by simp [MulAut.conj_apply]⟩
  refine section16_mem_msigma_of_primeSupport_subset
    (G := G) (M := M.conjBy a)
    (section10_maximal_conjBy (G := G) hM a) hx_conj_M ?_
  intro p hp
  have hp_x : p ∈ section14ElementPrimeSupport x :=
    section16_elementPrimeSupport_conj_subset (G := G) (x := x) (g := a) hp
  have hMx : M ∈ section14MsigmaElement x := by
    exact ⟨hM, by simpa [section14MsigmaElement, section14MsigmaFamily,
      Set.singleton_subset_iff] using hx⟩
  exact (section16_sigmaPrimes_conjBy (G := G) M a).symm ▸
    section16_primeSupport_subset_sigma_of_msigmaMember (G := G) hMx hp_x

omit [Finite G] [IsMinCE G] in
private theorem CFSG.section16_section15HallSubgroupOf_self
    (H : Subgroup G) :
    section15HallSubgroupOf H H := by
  refine ⟨le_rfl, ?_⟩
  refine isHallSubgroup_of
    (π := subgroupPrimeSet H)
    (H := H.subgroupOf H) ?_ ?_
  · intro p hp
    simpa [subgroupPrimeSet, natCard_subgroupOf_eq H H le_rfl] using hp
  · intro p _hpπ hpidx
    have htop : H.subgroupOf H = (⊤ : Subgroup H) :=
      Subgroup.subgroupOf_eq_top.2 le_rfl
    have hpone : p.val ∣ 1 := by
      simpa [htop] using hpidx
    exact p.property.not_dvd_one hpone

omit [Finite G] [IsMinCE G] in
private theorem CFSG.section16HallSubgroupOf_self
    (H : Subgroup G) :
    section16HallSubgroupOf H H := by
  simpa [section16HallSubgroupOf, section15HallSubgroupOf] using
    section16_section15HallSubgroupOf_self (G := G) H

omit [Finite G] [IsMinCE G] in
private theorem CFSG.section16HallSubgroupOf_of_le
    {H K L : Subgroup G}
    (hHall : section16HallSubgroupOf H L)
    (hHK : H ≤ K) (hKL : K ≤ L) :
    section16HallSubgroupOf H K := by
  classical
  rcases hHall with ⟨hHL, hHallL⟩
  refine ⟨hHK, ?_⟩
  refine isHallSubgroup_of (G := K) (π := subgroupPrimeSet H)
    (H := H.subgroupOf K) ?_ ?_
  · intro p hp
    have hcardK : Nat.card (H.subgroupOf K) = Nat.card H := by
      exact Nat.card_congr
        (Subgroup.subgroupOfEquivOfLe (H := H) (K := K) hHK).toEquiv
    simpa [subgroupPrimeSet, hcardK] using hp
  · intro p hpπ hpidx
    let KsubL : Subgroup L := K.subgroupOf L
    have hHsub_le_Ksub : H.subgroupOf L ≤ KsubL := by
      intro x hx
      exact hHK hx
    have hrel_eq :
        (H.subgroupOf K).index = (H.subgroupOf L).relIndex KsubL := by
      have hsub :=
        Subgroup.relIndex_subgroupOf (H := H) (K := K) (L := L) hKL
      simpa [KsubL, Subgroup.relIndex] using hsub.symm
    have hidx_dvd :
        (H.subgroupOf K).index ∣ (H.subgroupOf L).index := by
      have hrel_dvd :
          (H.subgroupOf L).relIndex KsubL ∣ (H.subgroupOf L).index :=
        Subgroup.relIndex_dvd_index_of_le hHsub_le_Ksub
      simpa [hrel_eq] using hrel_dvd
    exact (hHallL.p_in_pi_of_p_dvd_index p (hpidx.trans hidx_dvd)) hpπ

public theorem CFSG.section16_nilpotent_hall_fusion_control
    (H : Subgroup G)
    (hHall : section16HallSubgroupOf H ⊤)
    (hNil : Group.IsNilpotent H) :
    ∀ x y : G, x ∈ H → y ∈ H →
      (section16ConjugateInSubgroup ⊤ x y ↔
        section16ConjugateInSubgroup (Subgroup.normalizer (H : Set G)) x y) := by
  classical
  intro x y hxH hyH
  constructor
  · intro hxy
    by_cases hHbot : H = ⊥
    · have hx_one : x = 1 := by
        simpa [hHbot] using hxH
      have hy_one : y = 1 := by
        simpa [hHbot] using hyH
      subst x
      subst y
      exact ⟨1, by simp, by simp⟩
    · have hHall15Top : section15HallSubgroupOf H (⊤ : Subgroup G) := by
        simpa [section16HallSubgroupOf, section15HallSubgroupOf] using hHall
      rcases corollary_15_4 (G := G) (H := H) hHbot hHall15Top hNil with
        ⟨M, hM, hHleMsigma⟩
      rcases section15_exists_MFSubgroup (G := G) M with ⟨MF, hMF15⟩
      have hHallMsigma16 : section16HallSubgroupOf H (section10Msigma M) :=
        section16HallSubgroupOf_of_le (G := G) hHall hHleMsigma le_top
      have hHallMsigma15 : section15HallSubgroupOf H (section10Msigma M) := by
        simpa [section16HallSubgroupOf, section15HallSubgroupOf] using hHallMsigma16
      have hxy15 : section15ConjugateInSubgroup (⊤ : Subgroup G) x y := by
        simpa [section16ConjugateInSubgroup, section15ConjugateInSubgroup] using hxy
      rcases corollary_15_3_b (G := G) (M := M) (H := H)
          hM hMF15 hHbot hHallMsigma15 x y hxH hyH hxy15 with
        ⟨g, hg, hgy⟩
      exact ⟨g, (mem_subgroupNormalizerIn.mp hg).1, hgy⟩
  · intro hxy
    rcases hxy with ⟨g, _hg, hgy⟩
    exact ⟨g, by simp, hgy⟩

public theorem CFSG.section16_fusion_in_msigma
    {M MF : Subgroup G}
    (hM : M ∈ section9MaximalSubgroups G)
    (hMF : section15MFSubgroup M MF) :
    ∀ x y : G, x ∈ section10Msigma M → y ∈ section10Msigma M →
      section16ConjugateInSubgroup ⊤ x y →
        section16ConjugateInSubgroup M x y := by
  intro x y hx hy hxy
  have hHne : section10Msigma M ≠ ⊥ := theorem_10_2_e (G := G) hM
  have hxy15 : section15ConjugateInSubgroup (⊤ : Subgroup G) x y := by
    simpa [section16ConjugateInSubgroup, section15ConjugateInSubgroup] using hxy
  rcases corollary_15_3_b (G := G) (M := M) (H := section10Msigma M)
      hM hMF hHne (section16_section15HallSubgroupOf_self (G := G) (section10Msigma M))
      x y hx hy hxy15 with
    ⟨g, hg, hgy⟩
  exact ⟨g, (mem_subgroupNormalizerIn.mp hg).2, hgy⟩

public theorem CFSG.section16_msigma_inf_conjBy_cyclic
    {M : Subgroup G}
    (hM : M ∈ section9MaximalSubgroups G) :
    ∀ g : G, g ∉ M → IsCyclic (section10Msigma M ⊓ M.conjBy g : Subgroup G) := by
  have hbotπ :
      IsPiSubgroup (G := G) (section10SigmaPrimes M)ᶜ (⊥ : Subgroup G) := by
    intro q hq
    exact False.elim (q.property.not_dvd_one (by simpa using hq))
  rcases section13_exists_EData_containing_sigma_compl_piSubgroup
      (G := G) (M := M) (A := ⊥) hM bot_le hbotπ with
    ⟨E, E₁₂, E₁, E₂, E₃, hE, _⟩
  intro g hg
  exact ((lemma_12_17 (G := G) (M := M) (E := E) (E₁₂ := E₁₂)
    (E₁ := E₁) (E₂ := E₂) (E₃ := E₃) hM hE).2.2 g hg).1

private theorem CFSG.section16_conjugatesContaining_subset_msigmaElement
    {M : Subgroup G}
    (hM : M ∈ section9MaximalSubgroups G)
    {x : G} (hx : x ∈ section10Msigma M) :
    ∀ N : Subgroup G, N ∈ section16ConjugatesContainingElement M x →
      N ∈ section14MsigmaElement x := by
  intro N hN
  rcases hN with ⟨g, rfl, hxMg⟩
  refine ⟨section10_maximal_conjBy (G := G) hM g, ?_⟩
  intro y hy
  have hyx : y = x := by simpa using hy
  subst y
  rcases Subgroup.mem_map.mp hxMg with ⟨z, hzM, hzx⟩
  have hz_eq : z = g⁻¹ * x * g := by
    rw [← hzx]
    change z = g⁻¹ * (g * z * g⁻¹) * g
    group
  have hzσ : section14ElementPrimeSupport z ⊆ section10SigmaPrimes M := by
    intro p hp
    have hp_x : p ∈ section14ElementPrimeSupport x := by
      have hsubset :=
        section16_elementPrimeSupport_conj_subset (G := G) (x := x) (g := g⁻¹)
      have hp_conj :
          p ∈ section14ElementPrimeSupport (g⁻¹ * x * (g⁻¹)⁻¹) := by
        simpa [hz_eq] using hp
      exact hsubset hp_conj
    exact section16_primeSupport_subset_sigma_of_msigmaMember
      (G := G) (x := x) (M := M) ⟨hM, by simpa using hx⟩ hp_x
  have hzMσ : z ∈ section10Msigma M :=
    section16_mem_msigma_of_primeSupport_subset (G := G) hM hzM hzσ
  have hxσ_conj :
      g * z * g⁻¹ ∈ section10Msigma (M.conjBy g) :=
    section16_mem_msigma_conjBy (G := G) hM hzMσ
  have hconj_eq : g * z * g⁻¹ = x := by
    simpa [MulAut.conj_apply] using hzx
  simpa [hconj_eq] using hxσ_conj

omit [Finite G] [IsMinCE G] in
private theorem CFSG.section16_sharpTransitiveOn_conjugates
    {M R : Subgroup G} {x : G}
    (hsubset : ∀ N : Subgroup G, N ∈ section16ConjugatesContainingElement M x →
      N ∈ section14MsigmaElement x)
    (hsharp : section14SharpTransitiveOn R (section14MsigmaElement x)) :
    section16ActsSharplyTransitivelyOnConjugates R M x := by
  intro N₁ hN₁ N₂ hN₂
  exact hsharp N₁ (hsubset N₁ hN₁) N₂ (hsubset N₂ hN₂)

omit [Finite G] [IsMinCE G] in
private theorem CFSG.section16_isComplement'_self_bot
    (K : Subgroup G) :
    (K.subgroupOf K).IsComplement' ((⊥ : Subgroup G).subgroupOf K) := by
  have hKtop : K.subgroupOf K = (⊤ : Subgroup K) :=
    Subgroup.subgroupOf_eq_top.2 le_rfl
  have hbot : ((⊥ : Subgroup G).subgroupOf K) = (⊥ : Subgroup K) := by
    ext x
    constructor
    · intro hx
      have hxbot : (x : G) ∈ (⊥ : Subgroup G) := by
        simpa [Subgroup.mem_subgroupOf] using hx
      exact Subtype.ext (Subgroup.mem_bot.mp hxbot)
    · intro hx
      have hxone : x = 1 := Subgroup.mem_bot.mp hx
      subst x
      simp
  rw [hKtop, hbot]
  refine Subgroup.isComplement'_of_disjoint_and_mul_eq_univ ?_ ?_
  · exact disjoint_bot_right
  · ext x
    simp

omit [Finite G] [IsMinCE G] in
private theorem CFSG.section16_isComplement'_subgroupOf_of_disjoint_mul_eq_univ
    {K H R : Subgroup G} (hHK : H ≤ K) (hRK : R ≤ K)
    (hdisj : Disjoint H R)
    (hmul : ((K : Set G) = (H : Set G) * (R : Set G))) :
    (H.subgroupOf K).IsComplement' (R.subgroupOf K) := by
  refine Subgroup.isComplement'_of_disjoint_and_mul_eq_univ ?_ ?_
  · rw [Subgroup.disjoint_def]
    intro x hxH hxR
    apply Subtype.ext
    exact Subgroup.disjoint_def.mp hdisj
      (by simpa [Subgroup.mem_subgroupOf] using hxH)
      (by simpa [Subgroup.mem_subgroupOf] using hxR)
  · rw [Set.eq_univ_iff_forall]
    intro x
    have hxprod : (x : G) ∈ (H : Set G) * (R : Set G) := by
      rw [← hmul]
      exact x.property
    rcases hxprod with ⟨h, hhH, r, hrR, hhr⟩
    refine ⟨⟨h, hHK hhH⟩, ?_, ⟨r, hRK hrR⟩, ?_, ?_⟩
    · simpa [Subgroup.mem_subgroupOf] using hhH
    · simpa [Subgroup.mem_subgroupOf] using hrR
    · apply Subtype.ext
      exact hhr

omit [Finite G] [IsMinCE G] in
private theorem CFSG.section16_hallSubgroupOf_of_complement_normalHall
    {K H R : Subgroup G} (hHK : H ≤ K) (_hRK : R ≤ K)
    (hRHall : ∃ π : Set Nat.Primes, IsHallSubgroup π (R.subgroupOf K))
    (hcomp : (H.subgroupOf K).IsComplement' (R.subgroupOf K)) :
    section16HallSubgroupOf H K := by
  rcases hRHall with ⟨π, hRHallπ⟩
  refine ⟨hHK, ?_⟩
  refine isHallSubgroup_of
    (G := K) (π := subgroupPrimeSet H) (H := H.subgroupOf K) ?_ ?_
  · intro p hpH
    have hcard : Nat.card (H.subgroupOf K) = Nat.card H :=
      natCard_subgroupOf_eq H K hHK
    simpa [subgroupPrimeSet, hcard] using hpH
  · intro p hpH hpidx
    have hpRcard : p.val ∣ Nat.card (R.subgroupOf K) := by
      simpa [subgroupPrimeSet, hcomp.symm.index_eq_card] using hpidx
    have hpπ : p ∈ π := hRHallπ.p_in_pi_of_p_dvd_card p hpRcard
    have hpHcard : p.val ∣ Nat.card (H.subgroupOf K) := by
      have hcard : Nat.card (H.subgroupOf K) = Nat.card H :=
        natCard_subgroupOf_eq H K hHK
      simpa [subgroupPrimeSet, hcard] using hpH
    have hpRidx : p.val ∣ (R.subgroupOf K).index := by
      simpa [hcomp.index_eq_card] using hpHcard
    exact (hRHallπ.p_in_pi_of_p_dvd_index p hpRidx) hpπ

omit [Finite G] [IsMinCE G] in
public theorem CFSG.section16_elementCentralizerIn_inf_eq_left_of_centralizer_le
    {M N : Subgroup G} {x : G}
    (hCxN : Subgroup.centralizer ({x} : Set G) ≤ N) :
    elementCentralizerIn (M ⊓ N) x = elementCentralizerIn M x := by
  ext y
  constructor
  · intro hy
    exact ⟨hy.1.1, hy.2⟩
  · intro hy
    exact ⟨⟨hy.1, hCxN hy.2⟩, hy.2⟩

public theorem CFSG.section16_msigmaElement_card_gt_one_of_not_centralizer_le
    {M : Subgroup G}
    (hM : M ∈ section9MaximalSubgroups G)
    {x : G} (hx : x ∈ section10Msigma M)
    (hCGnot : ¬ Subgroup.centralizer ({x} : Set G) ≤ M) :
    1 < Nat.card {L : Subgroup G // L ∈ section14MsigmaElement x} := by
  classical
  have hMx : M ∈ section14MsigmaElement x := by
    exact ⟨hM, by simpa [section14MsigmaElement, section14MsigmaFamily,
      Set.singleton_subset_iff] using hx⟩
  obtain ⟨c, hcCx, hcM⟩ := Set.not_subset.mp hCGnot
  have hconj_x : c * x * c⁻¹ = x := by
    have hcomm : Commute c x :=
      Subgroup.mem_centralizer_singleton_iff.mp hcCx
    calc
      c * x * c⁻¹ = (c * x) * c⁻¹ := by rw [mul_assoc]
      _ = (x * c) * c⁻¹ := by rw [hcomm.eq]
      _ = x := by simp [mul_assoc]
  have hMcx : M.conjBy c ∈ section14MsigmaElement x := by
    refine ⟨section10_maximal_conjBy (G := G) hM c, ?_⟩
    intro y hy
    have hyx : y = x := by simpa using hy
    subst y
    have hx_conj := section16_mem_msigma_conjBy (G := G) hM (a := c) hx
    simpa [hconj_x] using hx_conj
  have hneq : M.conjBy c ≠ M := by
    intro hEq
    have hcNorm : c ∈ Subgroup.normalizer (M : Set G) :=
      section16_mem_normalizer_of_conjBy_eq (G := G) hEq
    exact hcM (by
      simpa [section16_maximal_normalizer_eq_self (G := G) hM] using hcNorm)
  let Ωx := {L : Subgroup G // L ∈ section14MsigmaElement x}
  let L₁ : Ωx := ⟨M, hMx⟩
  let L₂ : Ωx := ⟨M.conjBy c, hMcx⟩
  have hL₁_ne_L₂ : L₁ ≠ L₂ := by
    intro hEq
    exact hneq (congrArg Subtype.val hEq).symm
  haveI : Nontrivial Ωx := ⟨L₁, L₂, hL₁_ne_L₂⟩
  change 1 < Nat.card Ωx
  exact Finite.one_lt_card

public theorem CFSG.section16_section14R_eq_bot_of_centralizer_le
    {M : Subgroup G}
    (hM : M ∈ section9MaximalSubgroups G)
    {x : G} (hx : x ∈ section10Msigma M) (hxne : x ≠ 1)
    (hCGM : Subgroup.centralizer ({x} : Set G) ≤ M) :
    section14R x = (⊥ : Subgroup G) := by
  classical
  have hMx : M ∈ section14MsigmaElement x := by
    exact ⟨hM, by simpa [section14MsigmaElement, section14MsigmaFamily,
      Set.singleton_subset_iff] using hx⟩
  have hσ : (section14MsigmaElement x).Nonempty := ⟨M, hMx⟩
  have hnotcard :
      ¬ 1 < Nat.card {L : Subgroup G // L ∈ section14MsigmaElement x} := by
    intro hcard
    rcases (theorem_14_4 (G := G) (x := x) hxne hσ).2.2 hcard with
      ⟨N, hNcont, hNdata, hNuniq⟩
    have hMcont :
        M ∈ section9MaximalSubgroupsContaining (Subgroup.centralizer ({x} : Set G)) :=
      ⟨hM, hCGM⟩
    have hMN : M = N := hNuniq M hMcont
    have hDataM := hNdata M hMx
    have hcompN :
        section12ComplementIn N (section10Msigma N) (M ⊓ N) :=
      hDataM.2.2.2.2.2.2.1
    have hxNσ : x ∈ section10Msigma N := by
      simpa [← hMN] using hx
    have hxMN : x ∈ M ⊓ N := by
      exact ⟨section16_msigma_le (G := G) M hx, hMN ▸ section16_msigma_le (G := G) M hx⟩
    have hxbot : x ∈ (⊥ : Subgroup G) :=
      Subgroup.disjoint_def.mp hcompN.2.2.2 hxNσ hxMN
    exact hxne (by simpa using hxbot)
  have hcard' :
      ¬ 1 < (section14MsigmaElement x).ncard := by
    simpa only [Nat.card_coe_set_eq] using hnotcard
  simp [section14R, hxne, hσ, hcard']

public theorem CFSG.section16_theoremDComplement
    {M : Subgroup G}
    (hM : M ∈ section9MaximalSubgroups G)
    {x : G} (hx : x ∈ section10Msigma M) (hxne : x ≠ 1) :
    section16TheoremDComplement M x (section14R x) := by
  classical
  let Cx : Subgroup G := Subgroup.centralizer ({x} : Set G)
  let Cmx : Subgroup G := elementCentralizerIn M x
  have hMx : M ∈ section14MsigmaElement x := by
    exact ⟨hM, by simpa [section14MsigmaElement, section14MsigmaFamily,
      Set.singleton_subset_iff] using hx⟩
  have hσ : (section14MsigmaElement x).Nonempty := ⟨M, hMx⟩
  have h14 := theorem_14_4 (G := G) (x := x) hxne hσ
  rcases h14.1 with ⟨hRleCx, hRnormIn, hRHall⟩
  have hsubset :
      ∀ N : Subgroup G, N ∈ section16ConjugatesContainingElement M x →
        N ∈ section14MsigmaElement x :=
    section16_conjugatesContaining_subset_msigmaElement (G := G) hM hx
  have hsharp16 :
      section16ActsSharplyTransitivelyOnConjugates (section14R x) M x :=
    section16_sharpTransitiveOn_conjugates (G := G) hsubset h14.2.1
  by_cases hCGM : Cx ≤ M
  · have hRbot : section14R x = (⊥ : Subgroup G) :=
      section16_section14R_eq_bot_of_centralizer_le (G := G) hM hx hxne (by
        simpa [Cx] using hCGM)
    have hCmx_eq_Cx : Cmx = Cx := by
      ext y
      constructor
      · intro hy
        exact hy.2
      · intro hy
        exact ⟨hCGM hy, hy⟩
    have hHall : section16HallSubgroupOf Cmx Cx := by
      rw [hCmx_eq_Cx]
      exact section16HallSubgroupOf_self (G := G) Cx
    have hNormComp : section16NormalComplementIn Cmx Cx (section14R x) := by
      rw [hCmx_eq_Cx, hRbot]
      refine ⟨le_rfl, bot_le, ?_, section16_isComplement'_self_bot (G := G) Cx⟩
      infer_instance
    simpa [section16TheoremDComplement, Cx, Cmx] using
      ⟨hHall, hNormComp, hsharp16⟩
  · have hcard :
        1 < Nat.card {L : Subgroup G // L ∈ section14MsigmaElement x} :=
      section16_msigmaElement_card_gt_one_of_not_centralizer_le (G := G) hM hx (by
        simpa [Cx] using hCGM)
    rcases h14.2.2 hcard with ⟨N, hNcont, hNdata, _hNuniq⟩
    have hDataM := hNdata M hMx
    rcases hDataM with
      ⟨hReq, _hRne, hprod, _hsupp, _htau, _hbeta, hcompN, _hNF⟩
    have hCmx_eq :
        elementCentralizerIn (M ⊓ N) x = Cmx := by
      simpa [Cmx] using
        section16_elementCentralizerIn_inf_eq_left_of_centralizer_le
          (G := G) (M := M) (N := N) (x := x) hNcont.2
    have hCmx_le_Cx : Cmx ≤ Cx := by
      intro y hy
      exact hy.2
    have hRle_Cx : section14R x ≤ Cx := by
      simpa [Cx] using hRleCx
    have hRle_Nσ : section14R x ≤ section10Msigma N := by
      rw [hReq]
      intro y hy
      exact hy.1
    have hCmx_le_MN : Cmx ≤ M ⊓ N := by
      rw [← hCmx_eq]
      intro y hy
      exact hy.1
    have hdisj : Disjoint Cmx (section14R x) := by
      rw [Subgroup.disjoint_def]
      intro y hyC hyR
      exact Subgroup.disjoint_def.mp hcompN.2.2.2
        (hRle_Nσ hyR) (hCmx_le_MN hyC)
    have hprod' : ((Cx : Subgroup G) : Set G) =
        (Cmx : Set G) * (section14R x : Set G) := by
      simpa [Cx, hCmx_eq] using hprod
    have hcomp :
        (Cmx.subgroupOf Cx).IsComplement' ((section14R x).subgroupOf Cx) :=
      section16_isComplement'_subgroupOf_of_disjoint_mul_eq_univ
        (G := G) hCmx_le_Cx hRle_Cx hdisj hprod'
    have hHall : section16HallSubgroupOf Cmx Cx :=
      section16_hallSubgroupOf_of_complement_normalHall
        (G := G) hCmx_le_Cx hRle_Cx hRHall hcomp
    have hNormComp : section16NormalComplementIn Cmx Cx (section14R x) := by
      refine ⟨hCmx_le_Cx, hRle_Cx, ?_, hcomp⟩
      simpa [Cx] using hRnormIn.2
    simpa [section16TheoremDComplement, Cx, Cmx] using
      ⟨hHall, hNormComp, hsharp16⟩

omit [IsMinCE G] in
public theorem CFSG.section16_isPiElement_of_mem_hall
    {M K : Subgroup G} {π : Set Nat.Primes}
    (hK : section12HallSubgroupIn π K M)
    {x : G} (hx : x ∈ K) :
    section14IsPiElement π x := by
  intro p hpSupp
  have hpK : p ∈ subgroupPrimeSet K :=
    section8_subgroupPrimeSet_mono (Subgroup.zpowers_le.2 hx) hpSupp
  have hpKcard : p.val ∣ Nat.card K := by
    simpa [subgroupPrimeSet] using hpK
  have hpKsub : p.val ∣ Nat.card (K.subgroupOf M) := by
    simpa [section12_card_subgroupOf_eq hK.1] using hpKcard
  exact hK.2.p_in_pi_of_p_dvd_card p hpKsub

omit [Finite G] [IsMinCE G] in
private theorem CFSG.section16_coprime_order_of_support_split
    {a b : G} {π : Set Nat.Primes}
    (ha : section14ElementPrimeSupport a ⊆ πᶜ)
    (hb : section14ElementPrimeSupport b ⊆ π) :
    Nat.Coprime (orderOf a) (orderOf b) := by
  refine Nat.coprime_of_dvd ?_
  intro l hlprime hla hlb
  let l' : Nat.Primes := ⟨l, hlprime⟩
  have hla' : l' ∈ section14ElementPrimeSupport a := by
    simpa [section14ElementPrimeSupport, subgroupPrimeSet, Nat.card_zpowers] using hla
  have hlb' : l' ∈ section14ElementPrimeSupport b := by
    simpa [section14ElementPrimeSupport, subgroupPrimeSet, Nat.card_zpowers] using hlb
  exact ha hla' (hb hlb')

omit [Finite G] [IsMinCE G] in
private theorem CFSG.section16_mem_zpowers_mul_of_commute_of_coprime_order
    {a b : G} (hab : Commute a b)
    (hcop : Nat.Coprime (orderOf a) (orderOf b)) :
    a ∈ Subgroup.zpowers (a * b) := by
  have hbpow : b ^ orderOf b = 1 := pow_orderOf_eq_one b
  have hpow : (a * b) ^ orderOf b = a ^ orderOf b := by
    rw [hab.mul_pow, hbpow, mul_one]
  have hamem : a ∈ Subgroup.zpowers (a ^ orderOf b) := by
    rw [mem_zpowers_pow_iff]
    simpa [Nat.gcd_comm] using hcop.gcd_eq_one
  rcases hamem with ⟨n, hn⟩
  refine ⟨(orderOf b : ℤ) * n, ?_⟩
  calc
    (a * b) ^ ((orderOf b : ℤ) * n) =
        ((a * b) ^ (orderOf b : ℤ)) ^ n := by
          rw [zpow_mul]
    _ = ((a * b) ^ orderOf b) ^ n := by
          rw [zpow_natCast]
    _ = (a ^ orderOf b) ^ n := by
          rw [hpow]
    _ = a := by
          simpa using hn

omit [Finite G] [IsMinCE G] in
public theorem CFSG.section16_exists_prime_mem_elementPrimeSupport
    {x : G} (hxne : x ≠ 1) :
    (section14ElementPrimeSupport x).Nonempty := by
  classical
  have hcard_ne_one : Nat.card (Subgroup.zpowers x) ≠ 1 := by
    intro hcard
    have hbot : Subgroup.zpowers x = (⊥ : Subgroup G) :=
      (Subgroup.card_eq_one (H := Subgroup.zpowers x)).1 hcard
    have hxbot : x ∈ (⊥ : Subgroup G) := by
      simpa [hbot] using (Subgroup.mem_zpowers x)
    exact hxne (by simpa using hxbot)
  rcases Nat.exists_prime_and_dvd hcard_ne_one with ⟨p, hpprime, hpdiv⟩
  exact ⟨⟨p, hpprime⟩, by
    change (⟨p, hpprime⟩ : Nat.Primes) ∈ subgroupPrimeSet (Subgroup.zpowers x)
    change p ∣ Nat.card (Subgroup.zpowers x)
    exact hpdiv⟩

omit [Finite G] [IsMinCE G] in
private theorem CFSG.section16_kappa_subset_tau13 {M : Subgroup G} :
    section14KappaPrimes M ⊆ section12Tau1Primes M ∪ section12Tau3Primes M := by
  intro p hpκ
  exact hpκ.1

omit [Finite G] [IsMinCE G] in
private theorem CFSG.section16_tau2_not_tau13
    {M : Subgroup G} {p : Nat.Primes}
    (hp2 : p ∈ section12Tau2Primes M) :
    p ∉ section12Tau1Primes M ∪ section12Tau3Primes M := by
  intro hp13
  rcases hp13 with hp1 | hp3
  · have h2 : primeRank p.val M = 2 := hp2.2
    have h1 : primeRank p.val M = 1 := hp1.2.2
    have hbad : (2 : ℕ) = 1 := h2.symm.trans h1
    norm_num at hbad
  · have h2 : primeRank p.val M = 2 := hp2.2
    have h1 : primeRank p.val M = 1 := hp3.2.2
    have hbad : (2 : ℕ) = 1 := h2.symm.trans h1
    norm_num at hbad

private theorem CFSG.section16_msigma_mfSubgroup_of_nilpotent
    {M : Subgroup G}
    (hM : M ∈ section9MaximalSubgroups G)
    (hNil : Group.IsNilpotent (section10Msigma M)) :
    section16MFSubgroup M (section10Msigma M) := by
  classical
  have hMsigma15 :
      section15NilpotentNormalHallIn (section10Msigma M) M :=
    section15_msigma_nilpotentNormalHallIn_of_nilpotent (G := G) hM hNil
  refine ⟨?_, ?_⟩
  · simpa [section16NilpotentNormalHallIn, section15NilpotentNormalHallIn] using
      hMsigma15
  · intro H hH
    have hH15 : section15NilpotentNormalHallIn H M := by
      simpa [section16NilpotentNormalHallIn, section15NilpotentNormalHallIn] using hH
    rcases hH15 with ⟨hHM, hHnormM, hHnil, hHHall⟩
    have hHπ : IsPiSubgroup (G := G) (section10SigmaPrimes M) H := by
      intro p hpH
      exact section15_prime_mem_sigma_of_nilpotentNormalHallIn
        (G := G) hM ⟨hHM, hHnormM, hHnil, hHHall⟩ hpH
    have hcore : H ≤ piCoreIn (section10SigmaPrimes M) M :=
      section8_le_piCoreIn_of_normal_isPiSubgroup hHM hHnormM hHπ
    simpa [section10Msigma, section10MsigmaSubgroup, piCoreIn] using hcore

omit [Finite G] [IsMinCE G] in
private theorem CFSG.section16NilpotentNormalHallIn_bot
    (M : Subgroup G) :
    section16NilpotentNormalHallIn (⊥ : Subgroup G) M := by
  classical
  refine ⟨bot_le, inferInstance, inferInstance, ?_⟩
  refine isHallSubgroup_of (G := M)
    (π := subgroupPrimeSet (⊥ : Subgroup G))
    (H := (⊥ : Subgroup G).subgroupOf M) ?_ ?_
  · intro p hp
    have hcard :
        Nat.card ((⊥ : Subgroup G).subgroupOf M) =
          Nat.card (⊥ : Subgroup G) :=
      natCard_subgroupOf_eq (⊥ : Subgroup G) M bot_le
    simpa [subgroupPrimeSet, hcard] using hp
  · intro p hp hpidx
    exact p.property.not_dvd_one (by simpa [subgroupPrimeSet] using hp)

omit [IsMinCE G] in
private theorem CFSG.section16NilpotentNormalHallIn_sup
    {M H K : Subgroup G}
    (hH : section16NilpotentNormalHallIn H M)
    (hK : section16NilpotentNormalHallIn K M) :
    section16NilpotentNormalHallIn (H ⊔ K) M := by
  classical
  rcases hH with ⟨hHM, hHnormM, hHnil, hHHall⟩
  rcases hK with ⟨hKM, hKnormM, hKnil, hKHall⟩
  let π : Set Nat.Primes := subgroupPrimeSet H ∪ subgroupPrimeSet K
  let Hm : Subgroup M := H.subgroupOf M
  let Km : Subgroup M := K.subgroupOf M
  let SK : Subgroup G := H ⊔ K
  have hSKM : SK ≤ M := sup_le hHM hKM
  have hsub_eq :
      SK.subgroupOf M = Hm ⊔ Km := by
    dsimp [SK, Hm, Km]
    exact Subgroup.subgroupOf_sup (A := H) (A' := K) (B := M) hHM hKM
  have hHπ : IsPiSubgroup (G := M) π Hm := by
    intro p hp
    left
    have hcard : Nat.card Hm = Nat.card H :=
      natCard_subgroupOf_eq H M hHM
    simpa [π, subgroupPrimeSet, Hm, hcard] using hp
  have hKπ : IsPiSubgroup (G := M) π Km := by
    intro p hp
    right
    have hcard : Nat.card Km = Nat.card K :=
      natCard_subgroupOf_eq K M hKM
    simpa [π, subgroupPrimeSet, Km, hcard] using hp
  haveI : Km.Normal := hKnormM
  have hsupπ : IsPiSubgroup (G := M) π (Hm ⊔ Km) :=
    IsPiSubgroup.sup_of_normal_right hHπ hKπ
  have hSKnormM : (SK.subgroupOf M).Normal := by
    haveI : Hm.Normal := hHnormM
    haveI : Km.Normal := hKnormM
    have hsupNorm : (Hm ⊔ Km).Normal := Subgroup.sup_normal Hm Km
    simpa [hsub_eq] using hsupNorm
  have hHleF : H ≤ section8FittingSubgroup M :=
    section12_le_fittingSubgroupOf_of_normalIn_nilpotent hHM hHnormM hHnil
  have hKleF : K ≤ section8FittingSubgroup M :=
    section12_le_fittingSubgroupOf_of_normalIn_nilpotent hKM hKnormM hKnil
  have hSKleF : SK ≤ section8FittingSubgroup M := sup_le hHleF hKleF
  have hSKnil : Group.IsNilpotent SK := by
    haveI : Group.IsNilpotent (section8FittingSubgroup M) :=
      section8FittingSubgroup_isNilpotent M
    haveI : Group.IsNilpotent (SK.subgroupOf (section8FittingSubgroup M)) := by
      infer_instance
    let e :=
      Subgroup.subgroupOfEquivOfLe (G := G) (H := SK)
        (K := section8FittingSubgroup M) hSKleF
    exact Group.nilpotent_of_mulEquiv
      (G := SK.subgroupOf (section8FittingSubgroup M)) (G' := SK) e
  refine ⟨hSKM, hSKnormM, hSKnil, ?_⟩
  refine isHallSubgroup_of (G := M) (π := subgroupPrimeSet SK)
    (H := SK.subgroupOf M) ?_ ?_
  · intro p hp
    have hcard : Nat.card (SK.subgroupOf M) = Nat.card SK :=
      natCard_subgroupOf_eq SK M hSKM
    simpa [subgroupPrimeSet, hcard] using hp
  · intro p hpSK hpidx
    have hpSKsub : p.val ∣ Nat.card (SK.subgroupOf M) := by
      have hcard : Nat.card (SK.subgroupOf M) = Nat.card SK :=
        natCard_subgroupOf_eq SK M hSKM
      simpa [subgroupPrimeSet, hcard] using hpSK
    have hpSup : p.val ∣ Nat.card (Hm ⊔ Km : Subgroup M) := by
      simpa [hsub_eq] using hpSKsub
    have hpπ : p ∈ π := hsupπ p hpSup
    rcases hpπ with hpH | hpK
    · have hHmSKm : Hm ≤ SK.subgroupOf M := by
        dsimp [Hm, SK]
        exact Subgroup.subgroupOf_mono M le_sup_left
      have hpidxH : p.val ∣ Hm.index := by
        rw [← Subgroup.relIndex_mul_index hHmSKm]
        exact dvd_mul_of_dvd_right hpidx (Hm.relIndex (SK.subgroupOf M))
      exact (hHHall.p_in_pi_of_p_dvd_index p hpidxH) hpH
    · have hKmSKm : Km ≤ SK.subgroupOf M := by
        dsimp [Km, SK]
        exact Subgroup.subgroupOf_mono M le_sup_right
      have hpidxK : p.val ∣ Km.index := by
        rw [← Subgroup.relIndex_mul_index hKmSKm]
        exact dvd_mul_of_dvd_right hpidx (Km.relIndex (SK.subgroupOf M))
      exact (hKHall.p_in_pi_of_p_dvd_index p hpidxK) hpK

omit [IsMinCE G] in
/-- Every finite subgroup has a largest nilpotent normal Hall subgroup in the
Section 16 sense. -/
public theorem CFSG.section16_exists_mfSubgroup
    (M : Subgroup G) :
    ∃ MF : Subgroup G, section16MFSubgroup M MF := by
  classical
  let candidates : Set (Subgroup G) :=
    {H : Subgroup G | section16NilpotentNormalHallIn H M}
  have hnonempty : candidates.Nonempty :=
    ⟨⊥, section16NilpotentNormalHallIn_bot (G := G) M⟩
  have hfinite : candidates.Finite := Set.toFinite candidates
  rcases hfinite.exists_maximal hnonempty with ⟨MF, hMFmax⟩
  have hMFmax' := maximal_mem_iff.mp hMFmax
  refine ⟨MF, hMFmax'.1, ?_⟩
  intro H hH
  have hJoin : section16NilpotentNormalHallIn (MF ⊔ H) M :=
    section16NilpotentNormalHallIn_sup (G := G) hMFmax'.1 hH
  have hEq : MF = MF ⊔ H := hMFmax'.2 hJoin le_sup_left
  rw [hEq]
  exact le_sup_right

omit [Finite G] [IsMinCE G] in
public theorem CFSG.section16_complementIn_normal_isComplement'
    {M K L : Subgroup G}
    (hcomp : section12ComplementIn M K L)
    (hLnorm : section10NormalIn L M) :
    (K.subgroupOf M).IsComplement' (L.subgroupOf M) := by
  classical
  have hK_norm_L : K ≤ Subgroup.normalizer (L : Set G) :=
    hcomp.1.trans ((Subgroup.normal_subgroupOf_iff_le_normalizer hLnorm.1).1 hLnorm.2)
  have hmul_sup :
      (((K ⊔ L : Subgroup G) : Set G)) = (K : Set G) * (L : Set G) :=
    Subgroup.coe_mul_of_left_le_normalizer_right K L hK_norm_L
  have hmul :
      ((M : Set G) = (K : Set G) * (L : Set G)) := by
    rw [hcomp.2.2.1, hmul_sup]
  exact section16_isComplement'_subgroupOf_of_disjoint_mul_eq_univ
    (G := G) hcomp.1 hcomp.2.1 hcomp.2.2.2 hmul

omit [Finite G] [IsMinCE G] in
private theorem CFSG.section16_mem_normal_complement_of_support_disjoint_hall
    {M K L : Subgroup G} {π : Set Nat.Primes}
    (hKHall : section12HallSubgroupIn π K M)
    (hcomp : section12ComplementIn M K L)
    (hLnorm : section10NormalIn L M)
    {x : G} (hxM : x ∈ M)
    (hxπc : section14ElementPrimeSupport x ⊆ πᶜ) :
    x ∈ L := by
  classical
  let Lsub : Subgroup M := L.subgroupOf M
  haveI : Lsub.Normal := by
    simpa [Lsub] using hLnorm.2
  let q : M →* M ⧸ Lsub := QuotientGroup.mk' Lsub
  let xM : M := ⟨x, hxM⟩
  have hcompLocal :
      (K.subgroupOf M).IsComplement' Lsub :=
    section16_complementIn_normal_isComplement'
      (G := G) (M := M) (K := K) (L := L) hcomp hLnorm
  have hq_dvd_orderM : orderOf (q xM) ∣ orderOf xM := by
    simpa [q] using orderOf_map_dvd (ψ := q) xM
  have hq_dvd_order : orderOf (q xM) ∣ orderOf x := by
    simpa [xM, Subgroup.orderOf_coe] using hq_dvd_orderM
  have hq_dvd_index : orderOf (q xM) ∣ Lsub.index := by
    have hq_dvd_card :
        orderOf (q xM) ∣ Nat.card (M ⧸ Lsub) := orderOf_dvd_natCard (q xM)
    simpa [Subgroup.index_eq_card] using hq_dvd_card
  have hq_dvd_cardK : orderOf (q xM) ∣ Nat.card (K.subgroupOf M) := by
    simpa [hcompLocal.index_eq_card] using hq_dvd_index
  have hcop : Nat.Coprime (orderOf x) (Nat.card (K.subgroupOf M)) := by
    refine Nat.coprime_of_dvd ?_
    intro p hpprime hpx hpK
    let p' : Nat.Primes := ⟨p, hpprime⟩
    have hpSupp : p' ∈ section14ElementPrimeSupport x := by
      change p' ∈ subgroupPrimeSet (Subgroup.zpowers x)
      change p' ∈ {q : Nat.Primes | q.val ∣ Nat.card (Subgroup.zpowers x)}
      change p ∣ Nat.card (Subgroup.zpowers x)
      rw [Nat.card_zpowers]
      exact hpx
    have hpπ : p' ∈ π := hKHall.2.p_in_pi_of_p_dvd_card p' (by simpa [p'] using hpK)
    exact hxπc hpSupp hpπ
  have hq_order_one : orderOf (q xM) = 1 :=
    Nat.eq_one_of_dvd_coprimes hcop hq_dvd_order hq_dvd_cardK
  have hq_eq_one : q xM = 1 := orderOf_eq_one_iff.mp hq_order_one
  have hxLsub : xM ∈ Lsub :=
    (QuotientGroup.eq_one_iff (N := Lsub) xM).1 hq_eq_one
  simpa [Lsub, xM, Subgroup.mem_subgroupOf] using hxLsub

omit [Finite G] [IsMinCE G] in
private theorem CFSG.section16_mem_U_mul_msigma_of_support_tau2
    {M K U : Subgroup G}
    (hKU : section15KUData M K U)
    {x : G} (hxM : x ∈ M)
    (hxsupp : section14ElementPrimeSupport x ⊆ section12Tau2Primes M) :
    x ∈ (U : Set G) * (section10Msigma M : Set G) := by
  classical
  have hxκc : section14ElementPrimeSupport x ⊆ (section14KappaPrimes M)ᶜ := by
    intro p hp hpκ
    exact section16_tau2_not_tau13 (G := G) (hxsupp hp)
      (section16_kappa_subset_tau13 (G := G) hpκ)
  have hUHall := hKU.2.2.2.1
  have hNormComp : section14NormalComplementIn M K (U ⊔ section10Msigma M) :=
    ⟨hKU.2.1, hKU.2.2.2.2.2.1⟩
  let L : Subgroup G := U ⊔ section10Msigma M
  have hxL : x ∈ L :=
    section16_mem_normal_complement_of_support_disjoint_hall
      (G := G) (M := M) (K := K) (L := L) hKU.1 hNormComp.1 hNormComp.2
      hxM hxκc
  have hU_norm_sigma : U ≤ Subgroup.normalizer (section10Msigma M : Set G) :=
    hUHall.1.trans (section12_le_normalizer_msigma (M := M))
  have hprod :
      ((L : Subgroup G) : Set G) = (U : Set G) * (section10Msigma M : Set G) := by
    simpa [L] using
      Subgroup.coe_mul_of_left_le_normalizer_right U (section10Msigma M) hU_norm_sigma
  exact hprod ▸ hxL

set_option linter.unusedVariables false in
public theorem CFSG.section16_theoremD_auxiliary_data
    {M N : Subgroup G} {x : G}
    (hxne : x ≠ 1)
    (hNcont : N ∈ section9MaximalSubgroupsContaining (Subgroup.centralizer ({x} : Set G)))
    (hReq : section14R x = elementCentralizerIn (section10Msigma N) x)
    (hRne : section14R x ≠ ⊥)
    (hsupp : section14ElementPrimeSupport x ⊆ section12Tau2Primes N)
    (hNF_or_P2 : N ∈ section14MFamilyF G ∪ section14MFamilyP2 G) :
    ∃ NF NK NU : Subgroup G, section16MFSubgroup N NF ∧
      section16KUData N NK NU ∧
        section10Msigma N = NF ∧ x ∈ section16ASet N NU \ (section10Msigma N : Set G) := by
  classical
  have hxN : x ∈ N := by
    exact hNcont.2 (Subgroup.mem_centralizer_singleton_iff.mpr (Commute.refl x))
  rcases section15_exists_KUData_for_maximal (G := G) (M := N) hNcont.1 with
    ⟨NK, NU, hKU15⟩
  have hNil : Group.IsNilpotent (section10Msigma N) := by
    rcases hNF_or_P2 with hNF | hNP2
    · have hNnotP1 : N ∉ section14MFamilyP1 G := by
        intro hP1
        rcases hP1.1.2 with ⟨p, hpκ⟩
        simp [hNF.2] at hpκ
      rcases section16_exists_prime_mem_elementPrimeSupport (G := G) hxne with ⟨p, hpSupp⟩
      have hpTau2 : p ∈ section12Tau2Primes N := hsupp hpSupp
      have hpN : p ∈ subgroupPrimeSet N :=
        section8_subgroupPrimeSet_mono (Subgroup.zpowers_le.2 hxN) hpSupp
      have hpNotSigma : p ∉ section10SigmaPrimes N := hpTau2.1
      have hpNotKappa : p ∉ section14KappaPrimes N := by
        intro hpκ
        simp [hNF.2] at hpκ
      let S : Sylow p.val N := Classical.choice (Sylow.nonempty (p := p.val) (G := N))
      exact (lemma_14_1 (G := G) hNF.1 hNnotP1
        (p := p) ⟨hpN, by
          intro hpUnion
          rcases hpUnion with hpσ | hpκ
          · exact hpNotSigma hpσ
          · exact hpNotKappa hpκ⟩ S).2.2
    · exact (proposition_14_2_g (G := G) (M := N) (K := NK)
        hNP2 hKU15.1).2.2.1
  have hMFN : section16MFSubgroup N (section10Msigma N) :=
    section16_msigma_mfSubgroup_of_nilpotent (G := G) hNcont.1 hNil
  have hHat : x ∈ section16HatMsigmaSet N := by
    refine ⟨hxN, ?_⟩
    simpa [← hReq] using hRne
  have hxProd : x ∈ (NU : Set G) * (section10Msigma N : Set G) :=
    section16_mem_U_mul_msigma_of_support_tau2 (G := G) (M := N) (K := NK)
      (U := NU) hKU15 hxN hsupp
  have hxNotSigma : x ∉ section10Msigma N := by
    intro hxSigma
    rcases section16_exists_prime_mem_elementPrimeSupport (G := G) hxne with ⟨p, hpSupp⟩
    have hpSigma : p ∈ section10SigmaPrimes N :=
      section16_primeSupport_subset_sigma_of_msigmaMember
        (G := G) (x := x) (M := N)
        ⟨hNcont.1, by
          intro y hy
          have hyx : y = x := by simpa using hy
          simpa [hyx] using hxSigma⟩ hpSupp
    exact (hsupp hpSupp).1 hpSigma
  refine ⟨section10Msigma N, NK, NU, hMFN, ?_, rfl, ?_⟩
  · exact section16_KUData_of_section15 (G := G) hKU15
  · exact ⟨⟨hHat, hxProd, hxne⟩, hxNotSigma⟩

omit [IsMinCE G] in
public theorem CFSG.section16_exists_prime_order_zpower
    {x : G} (hxne : x ≠ 1) :
    ∃ r : Nat.Primes, ∃ xr : G,
      r ∈ subgroupPrimeSet (Subgroup.zpowers x) ∧
        xr ∈ Subgroup.zpowers x ∧ orderOf xr = r.val := by
  classical
  have hcard_ne_one : Nat.card (Subgroup.zpowers x) ≠ 1 := by
    intro hcard
    have hzbot : Subgroup.zpowers x = ⊥ :=
      (Subgroup.card_eq_one (H := Subgroup.zpowers x)).1 hcard
    have hxbot : x ∈ (⊥ : Subgroup G) := by
      simpa [hzbot] using (Subgroup.mem_zpowers x)
    exact hxne (by simpa using hxbot)
  rcases Nat.exists_prime_and_dvd hcard_ne_one with ⟨q, hqprime, hqdiv⟩
  let r : Nat.Primes := ⟨q, hqprime⟩
  haveI : Fact q.Prime := ⟨hqprime⟩
  obtain ⟨z, hz_order⟩ :=
    exists_prime_orderOf_dvd_card' (G := Subgroup.zpowers x) q hqdiv
  refine ⟨r, z, ?_, z.property, ?_⟩
  · change q ∣ Nat.card (Subgroup.zpowers x)
    exact hqdiv
  · simpa [r, Subgroup.orderOf_coe] using hz_order

public theorem CFSG.section16_MF_eq_msigma_of_typeF
    {M MF K : Subgroup G}
    (hM : M ∈ section9MaximalSubgroups G)
    (hMF : section15MFSubgroup M MF)
    (hK : section12HallSubgroupIn (section14KappaPrimes M) K M)
    (hF : M ∈ section14MFamilyF G) :
    MF = section10Msigma M := by
  by_contra hne
  have hP1 := theorem_15_2_a (G := G) (M := M) (MF := MF) (K := K)
    hM hMF hK hne
  rcases hP1.1.1.2 with ⟨p, hpκ⟩
  simp [hF.2] at hpκ

private theorem CFSG.section16_section15KUData_bot_of_typeF_cyclic_complement
    {M E : Subgroup G}
    (hF : M ∈ section14MFamilyF G)
    (hcomp : section12ComplementToMsigma M E)
    (hcyc : IsCyclic E) :
    section15KUData M (⊥ : Subgroup G) E := by
  classical
  have hKHall : section12HallSubgroupIn (section14KappaPrimes M)
      (⊥ : Subgroup G) M := by
    refine ⟨bot_le, ?_⟩
    refine isHallSubgroup_of (G := M) (section14KappaPrimes M)
      (((⊥ : Subgroup G).subgroupOf M)) ?_ ?_
    · intro p hp
      have hcard : Nat.card (((⊥ : Subgroup G).subgroupOf M)) = 1 := by
        simp
      exact False.elim (p.property.not_dvd_one (by simpa [hcard] using hp))
    · intro p hpκ hpidx
      simp [hF.2] at hpκ
  have hCompLeft :
      section12ComplementIn M (⊥ : Subgroup G) (E ⊔ section10Msigma M) := by
    refine ⟨bot_le, sup_le hcomp.2.1 hcomp.1, ?_, disjoint_bot_left⟩
    calc
      M = section10Msigma M ⊔ E := hcomp.2.2.1
      _ = E ⊔ section10Msigma M := by rw [sup_comm]
      _ = (⊥ : Subgroup G) ⊔ (E ⊔ section10Msigma M) := by simp
  have hCompRight :
      section12ComplementIn M (section10Msigma M) ((⊥ : Subgroup G) ⊔ E) := by
    simpa [section12ComplementToMsigma] using hcomp
  have hUcomm : IsMulCommutative E := by
    letI : IsCyclic E := hcyc
    infer_instance
  have hUHall :
      section12HallSubgroupIn
        ((section14KappaPrimes M ∪ section10SigmaPrimes M)ᶜ) E M := by
    refine ⟨hcomp.2.1, ?_⟩
    simpa [hF.2] using
      section12_msigma_complement_isHall_sigma_compl (G := G) hF.1 hcomp
  have hActsReg : section14ActsRegularlyOn (⊥ : Subgroup G) E := by
    refine ⟨bot_le, ?_⟩
    intro x hxbot hxne
    exact False.elim (hxne (by simpa using hxbot))
  have hNormComp :
      section14NormalComplementIn M (⊥ : Subgroup G) (E ⊔ section10Msigma M) := by
    have hCompBot : section12ComplementIn M (⊥ : Subgroup G)
        (E ⊔ section10Msigma M) := by
      refine ⟨bot_le, sup_le hcomp.2.1 hcomp.1, ?_, disjoint_bot_left⟩
      calc
        M = section10Msigma M ⊔ E := hcomp.2.2.1
        _ = E ⊔ section10Msigma M := by rw [sup_comm]
        _ = (⊥ : Subgroup G) ⊔ (E ⊔ section10Msigma M) := by simp
    have hEMsigma_eq : E ⊔ section10Msigma M = M := by
      rw [sup_comm]
      exact hcomp.2.2.1.symm
    have hNormalSelf : section10NormalIn M M := by
      refine ⟨le_rfl, ?_⟩
      simp
    exact ⟨hCompBot, by simpa [hEMsigma_eq] using hNormalSelf⟩
  have hUnorm : section10NormalIn E ((⊥ : Subgroup G) ⊔ E) := by
    simpa using
      (show section10NormalIn E E from
        ⟨le_rfl, by simp⟩)
  exact ⟨hKHall, hCompLeft, hCompRight, hUHall, hActsReg, hNormComp.2, hUnorm⟩

public theorem CFSG.section16_frobeniusWithCyclicComplement_of_typeF_cyclic_msigma_complement
    {M MF E K : Subgroup G}
    (hM : M ∈ section9MaximalSubgroups G)
    (hMF : section15MFSubgroup M MF)
    (hK : section12HallSubgroupIn (section14KappaPrimes M) K M)
    (hF : M ∈ section14MFamilyF G)
    (hcomp : section12ComplementToMsigma M E)
    (hcyc : IsCyclic E) :
    section16FrobeniusWithCyclicComplement M MF := by
  classical
  have hMF_eq : MF = section10Msigma M :=
    section16_MF_eq_msigma_of_typeF (G := G) hM hMF hK hF
  have hKU_E : section15KUData M (⊥ : Subgroup G) E :=
    section16_section15KUData_bot_of_typeF_cyclic_complement (G := G) hF hcomp hcyc
  have hEne : E ≠ ⊥ := by
    intro hEbot
    have hchain := theorem_15_2_chain (G := G) (M := M) (MF := MF) hM hMF
    have hMsigma_lt_M : section10Msigma M < M :=
      lt_of_le_of_lt hchain.2.2.1 hchain.2.2.2
    have hM_eq : M = section10Msigma M := by
      simpa [hEbot] using hcomp.2.2.1
    exact hMsigma_lt_M.ne hM_eq.symm
  rcases lemma_15_1_e_join (G := G) (M := M) (K := (⊥ : Subgroup G))
      (U := E) hM hKU_E hEne with
    ⟨E₀, hE₀E, hExp, hFrobE₀⟩
  have hE₀cyc : IsCyclic E₀ := by
    letI : IsCyclic E := hcyc
    exact (Subgroup.subgroupOfEquivOfLe (H := E₀) (K := E) hE₀E).isCyclic.1
      (by infer_instance)
  have hcard_eq : Nat.card E₀ = Nat.card E := by
    letI : IsCyclic E₀ := hE₀cyc
    letI : IsCyclic E := hcyc
    calc
      Nat.card E₀ = Monoid.exponent E₀ := (IsCyclic.exponent_eq_card (α := E₀)).symm
      _ = Monoid.exponent E := hExp
      _ = Nat.card E := IsCyclic.exponent_eq_card (α := E)
  have hE₀_eq : E₀ = E :=
    Subgroup.eq_of_le_of_card_ge hE₀E (by rw [← hcard_eq])
  refine ⟨E, ?_, ?_, hcyc⟩
  · simpa [section12ComplementToMsigma, hMF_eq] using hcomp
  · have hFrobE : section12FrobeniusJoinWithKernel (section10Msigma M) E := by
      simpa [hE₀_eq] using hFrobE₀
    simpa [hMF_eq] using hFrobE

private theorem CFSG.section16_msigma_normalizer_eq_self
    {M : Subgroup G}
    (hM : M ∈ section9MaximalSubgroups G) :
    Subgroup.normalizer (section10Msigma M : Set G) = M := by
  classical
  have hMsigma_ne : section10Msigma M ≠ ⊥ := theorem_10_2_e (G := G) hM
  have hMsigmaSub_ne : section10MsigmaSubgroup M ≠ ⊥ := by
    intro hbot
    exact hMsigma_ne (by simp [section10Msigma, hbot])
  have hnorm :=
    section10_normalizer_map_subtype_eq_of_maximal_of_normal_ne_bot
      (G := G) hM (N := section10MsigmaSubgroup M) hMsigmaSub_ne
  simpa [section10Msigma] using hnorm

omit [Finite G] [IsMinCE G] in
public theorem CFSG.section16_mem_normalizer_of_conjugateSet_eq
    {X : Set G} {g : G}
    (hconj : section16ConjugateSet X g = X) :
    g ∈ Subgroup.normalizer X := by
  change ∀ x : G, x ∈ X ↔ g * x * g⁻¹ ∈ X
  intro x
  constructor
  · intro hx
    have hxconj : g * x * g⁻¹ ∈ section16ConjugateSet X g :=
      ⟨x, hx, rfl⟩
    simpa [hconj] using hxconj
  · intro hx
    have hxconj : g * x * g⁻¹ ∈ section16ConjugateSet X g := by
      simpa [hconj] using hx
    rcases hxconj with ⟨y, hy, hy_eq⟩
    have hxy : x = y := by
      calc
        x = g⁻¹ * (g * x * g⁻¹) * g := by group
        _ = g⁻¹ * (g * y * g⁻¹) * g := by rw [hy_eq]
        _ = y := by group
    simpa [hxy] using hy

omit [Finite G] [IsMinCE G] in
private theorem CFSG.section16_normalizer_le_of_nonempty_subset_ti
    {X : Set G} {W : Subgroup G} {W0 : Set G}
    (hTI : section16TISubsetWithNormalizer X W)
    (hOne : (1 : G) ∉ X)
    (hW0ne : W0.Nonempty)
    (hW0sub : W0 ⊆ X) :
    Subgroup.normalizer W0 ≤ W := by
  intro g hg
  rcases hW0ne with ⟨x, hxW0⟩
  have hxX : x ∈ X := hW0sub hxW0
  have hxne : x ≠ 1 := by
    intro hx
    exact hOne (by simpa [hx] using hxX)
  have hgnorm : ∀ y : G, y ∈ W0 ↔ g * y * g⁻¹ ∈ W0 := by
    change ∀ y : G, y ∈ W0 ↔ g * y * g⁻¹ ∈ W0 at hg
    exact hg
  have hgxW0 : g * x * g⁻¹ ∈ W0 := (hgnorm x).1 hxW0
  have hgxX : g * x * g⁻¹ ∈ X := hW0sub hgxW0
  have hgxConj : g * x * g⁻¹ ∈ section16ConjugateSet X g :=
    ⟨x, hxX, rfl⟩
  rcases hTI.1 g with hconj | hsmall
  · have hgNormX : g ∈ Subgroup.normalizer X :=
      section16_mem_normalizer_of_conjugateSet_eq (G := G) hconj
    simpa [hTI.2] using hgNormX
  · have hgx_one_mem : g * x * g⁻¹ ∈ ({1} : Set G) :=
      hsmall ⟨hgxX, hgxConj⟩
    have hgx_one : g * x * g⁻¹ = 1 := by
      simpa using hgx_one_mem
    have hx_one : x = 1 := by
      calc
        x = g⁻¹ * (g * x * g⁻¹) * g := by group
        _ = 1 := by rw [hgx_one]; simp
    exact False.elim (hxne hx_one)

omit [Finite G] [IsMinCE G] in
private theorem CFSG.section16_commutative_subgroup_le_normalizer_of_subset
    {W : Subgroup G} {W0 : Set G}
    (hWcomm : IsMulCommutative W)
    (hW0sub : W0 ⊆ (W : Set G)) :
    W ≤ Subgroup.normalizer W0 := by
  intro z hzW
  change ∀ x : G, x ∈ W0 ↔ z * x * z⁻¹ ∈ W0
  intro x
  constructor
  · intro hxW0
    have hxW : x ∈ W := hW0sub hxW0
    have hcomm : z * x = x * z :=
      setLike_mul_comm (s := W) hzW hxW
    simpa [hcomm, mul_assoc] using hxW0
  · intro hxW0
    have hzInvW : z⁻¹ ∈ W := W.inv_mem hzW
    let y : G := z * x * z⁻¹
    have hyW0 : y ∈ W0 := by simpa [y] using hxW0
    have hyW : y ∈ W := hW0sub hyW0
    have hcomm : z⁻¹ * y = y * z⁻¹ :=
      setLike_mul_comm (s := W) hzInvW hyW
    have h_eq : z⁻¹ * y * z = y := by
      calc
        z⁻¹ * y * z = (y * z⁻¹) * z := by rw [hcomm]
        _ = y := by simp [mul_assoc]
    have hpre : z⁻¹ * y * z ∈ W0 := by
      rw [h_eq]
      exact hyW0
    have hx_eq : x = z⁻¹ * y * z := by
      simp [y]
      group
    simpa [hx_eq] using hpre

omit [Finite G] [IsMinCE G] in
private theorem CFSG.section16_one_not_mem_hatW
    {W1 W2 : Subgroup G} :
    (1 : G) ∉ section16HatW W1 W2 := by
  intro h
  exact h.2 (Or.inl W1.one_mem)

omit [Finite G] [IsMinCE G] in
public theorem CFSG.section16_hatW_subset_normalizer_eq_of_ti
    {W1 W2 : Subgroup G} {W0 : Set G}
    (hTI :
      section16TISubsetWithNormalizer (section16HatW W1 W2) (W1 ⊔ W2 : Subgroup G))
    (hWcomm : IsMulCommutative (W1 ⊔ W2 : Subgroup G))
    (hW0ne : W0.Nonempty)
    (hW0sub : W0 ⊆ section16HatW W1 W2) :
    Subgroup.normalizer W0 = (W1 ⊔ W2 : Subgroup G) := by
  apply le_antisymm
  · exact section16_normalizer_le_of_nonempty_subset_ti
      (G := G) hTI (section16_one_not_mem_hatW (G := G)) hW0ne hW0sub
  · exact section16_commutative_subgroup_le_normalizer_of_subset
      (G := G) hWcomm (fun x hx => (hW0sub hx).1)

public theorem CFSG.section16_hatW_subset_normalizer_eq_of_caseP
    {M K : Subgroup G} {W0 : Set G}
    (hMP : M ∈ section14MFamilyP G)
    (hK : section12HallSubgroupIn (section14KappaPrimes M) K M)
    (hW0ne : W0.Nonempty)
    (hW0sub : W0 ⊆ section16HatW K (section16Kstar M K)) :
    Subgroup.normalizer W0 = section16ZSubgroup K (section16Kstar M K) := by
  let Kstar : Subgroup G := section16Kstar M K
  have h147d := theorem_14_7_d (G := G) (M := M) (K := K) hMP hK
  have h147e := theorem_14_7_e (G := G) (M := M) (K := K) hMP hK
  have hTI :
      section16TISubsetWithNormalizer (section16HatW K Kstar)
        (K ⊔ Kstar : Subgroup G) := by
    have hTI0 :
        section16TISubsetWithNormalizer (section16HatZ K Kstar)
          (section16ZSubgroup K Kstar) := by
      simpa [Kstar, section16HatZ, section16ZSubgroup, section16Kstar,
        section14WidehatZ, section14Z, section14KStar] using
        (section16_section14TISet_to_section16TISubsetWithNormalizer
          (G := G) h147e.1 h147e.2.1)
    simpa [section16HatW, section16HatZ, section16ZSubgroup] using hTI0
  have hZcyc : IsCyclic (K ⊔ Kstar : Subgroup G) := by
    change IsCyclic (section14Z M K)
    exact h147d.2.1
  have hWcomm : IsMulCommutative (K ⊔ Kstar : Subgroup G) := by
    letI : IsCyclic (K ⊔ Kstar : Subgroup G) := hZcyc
    infer_instance
  have hEq := section16_hatW_subset_normalizer_eq_of_ti
    (G := G) hTI hWcomm hW0ne (by simpa [Kstar] using hW0sub)
  simpa [Kstar, section16ZSubgroup] using hEq

public theorem CFSG.section16_not_TISubset_MF_of_not_centralizer_le
    {M MF : Subgroup G} {x : G}
    (hM : M ∈ section9MaximalSubgroups G)
    (hMF_eq : MF = section10Msigma M)
    (hx : x ∈ section10Msigma M)
    (hxne : x ≠ 1)
    (hCGnot : ¬ Subgroup.centralizer ({x} : Set G) ≤ M) :
    ¬ section16TISubset (MF : Set G) := by
  intro hTI
  apply hCGnot
  intro c hc
  have hTIσ : section16TISubset (section10Msigma M : Set G) := by
    simpa [hMF_eq] using hTI
  have hxConj : x ∈ section16ConjugateSet (section10Msigma M : Set G) c := by
    refine ⟨x, hx, ?_⟩
    have hcomm : c * x = x * c :=
      Subgroup.mem_centralizer_singleton_iff.mp hc
    exact (by
      calc
        x = x * c * c⁻¹ := by simp [mul_assoc]
        _ = c * x * c⁻¹ := by rw [← hcomm])
  rcases hTIσ c with hConjEq | hInter
  · have hcNorm : c ∈ Subgroup.normalizer (section10Msigma M : Set G) :=
      section16_mem_normalizer_of_conjugateSet_eq (G := G) hConjEq
    simpa [section16_msigma_normalizer_eq_self (G := G) hM] using hcNorm
  · have hx_one : x ∈ ({1} : Set G) :=
      hInter ⟨hx, hxConj⟩
    exact False.elim (hxne (by simpa using hx_one))

public theorem CFSG.section16_hatZ_decomp_with_kstar_zpower
    {M K : Subgroup G}
    (hMP : M ∈ section14MFamilyP G)
    (hK : section12HallSubgroupIn (section14KappaPrimes M) K M)
    (hZdp : section14ZInternalDirectProduct M K)
    {t : G}
    (ht : t ∈ section16HatZ K (section16Kstar M K)) :
    ∃ y k : G,
      y ∈ section16Kstar M K ∧ y ≠ 1 ∧
        k ∈ K ∧ k ≠ 1 ∧
          t = y * k ∧ Commute y k ∧ y ∈ Subgroup.zpowers t := by
  classical
  let Z : Subgroup G := section14Z M K
  have htWidehat : t ∈ section14WidehatZ M K := by
    simpa [section16HatZ, section16ZSubgroup, section16Kstar,
      section14WidehatZ, section14Z, section14KStar] using ht
  have htZ : t ∈ Z := htWidehat.1
  have htNotK : t ∉ K := by
    intro htK
    exact htWidehat.2 (Or.inl htK)
  have htNotKstar : t ∉ section14KStar M K := by
    intro htKstar
    exact htWidehat.2 (Or.inr htKstar)
  have hK_norm_Kstar : K ≤ Subgroup.normalizer (section14KStar M K : Set G) := by
    intro x hxK
    exact (centralizer_le_normalizer (section14KStar M K)) (hZdp.2.2.2.2 hxK)
  have hKstarNormal : ((section14KStar M K).subgroupOf Z).Normal := by
    change ((section14KStar M K).subgroupOf (K ⊔ section14KStar M K)).Normal
    exact Subgroup.normal_subgroupOf_sup_of_le_normalizer
      (H := K) (N := section14KStar M K) hK_norm_Kstar
  letI : ((section14KStar M K).subgroupOf Z).Normal := hKstarNormal
  have htop0 : (K.subgroupOf Z) ⊔ ((section14KStar M K).subgroupOf Z) = ⊤ := by
    change
      K.subgroupOf (K ⊔ section14KStar M K) ⊔
          (section14KStar M K).subgroupOf (K ⊔ section14KStar M K) = ⊤
    exact (Subgroup.codisjoint_subgroupOf_sup K (section14KStar M K)).eq_top
  have htop :
      ((section14KStar M K).subgroupOf Z) ⊔ (K.subgroupOf Z) = ⊤ := by
    simpa [sup_comm] using htop0
  let tZ : Z := ⟨t, htZ⟩
  have htTop : tZ ∈ ((section14KStar M K).subgroupOf Z) ⊔ (K.subgroupOf Z) := by
    simp [htop]
  rcases
      (Subgroup.mem_sup_of_normal_left
        (x := tZ) (s := (section14KStar M K).subgroupOf Z) (t := K.subgroupOf Z)).1
        htTop with
    ⟨yKstar, hyKstar0, kK, hkK0, htEq0⟩
  let y : G := yKstar
  let k : G := kK
  have hyKstar14 : y ∈ section14KStar M K := by
    simpa [y, Subgroup.mem_subgroupOf] using hyKstar0
  have hkK : k ∈ K := by
    simpa [k, Subgroup.mem_subgroupOf] using hkK0
  have htEq : t = y * k := by
    simpa [y, k] using congrArg Subtype.val htEq0.symm
  have hyne : y ≠ 1 := by
    intro hy1
    have htK : t ∈ K := by
      simpa [htEq, y, k, hy1] using hkK
    exact htNotK htK
  have hkne : k ≠ 1 := by
    intro hk1
    have htKstar : t ∈ section14KStar M K := by
      simpa [htEq, y, k, hk1] using hyKstar14
    exact htNotKstar htKstar
  have hMy : M ∈ section14MsigmaElement y := by
    refine ⟨hMP.1, ?_⟩
    simpa using hyKstar14.1
  have hySigma :
      section14ElementPrimeSupport y ⊆ section10SigmaPrimes M :=
    section16_primeSupport_subset_sigma_of_msigmaMember (G := G) hMy
  have hkKappa : section14IsPiElement (section14KappaPrimes M) k :=
    section16_isPiElement_of_mem_hall (G := G) hK hkK
  have hkSigmaCompl :
      section14ElementPrimeSupport k ⊆ (section10SigmaPrimes M)ᶜ := by
    intro p hp hpSigma
    exact section16_kappa_subset_not_sigma (M := M) (hkKappa hp) hpSigma
  have hykComm : Commute y k :=
    (Subgroup.mem_centralizer_iff.mp hyKstar14.2 k hkK).symm
  have hcop : Nat.Coprime (orderOf y) (orderOf k) :=
    section16_coprime_order_of_support_split hkSigmaCompl hySigma |>.symm
  have hyT : y ∈ Subgroup.zpowers t := by
    have hyT0 : y ∈ Subgroup.zpowers (y * k) :=
      section16_mem_zpowers_mul_of_commute_of_coprime_order hykComm hcop
    simpa [htEq] using hyT0
  refine ⟨y, k, ?_, hyne, hkK, hkne, htEq, hykComm, hyT⟩
  simpa [section16Kstar, section14KStar] using hyKstar14

private theorem CFSG.section16_eq_one_of_mem_kstar_and_conj_k
    {M K : Subgroup G}
    (hMP : M ∈ section14MFamilyP G)
    (hK : section12HallSubgroupIn (section14KappaPrimes M) K M)
    {g y : G}
    (_hgM : g ∈ M)
    (hyKstar : y ∈ section16Kstar M K)
    (hyKg : y ∈ K.conjBy g) :
    y = 1 := by
  classical
  by_contra hyne
  rcases Subgroup.mem_map.mp hyKg with ⟨x, hxK, hxy⟩
  have hySigmaMem : y ∈ section10Msigma M := by
    simpa [section16Kstar, section14KStar] using hyKstar.1
  have hMy : M ∈ section14MsigmaElement y := ⟨hMP.1, by simpa using hySigmaMem⟩
  have hySigma :
      section14ElementPrimeSupport y ⊆ section10SigmaPrimes M :=
    section16_primeSupport_subset_sigma_of_msigmaMember (G := G) hMy
  have horder_ne_one : orderOf y ≠ 1 := by
    intro horder
    exact hyne (orderOf_eq_one_iff.mp horder)
  rcases Nat.exists_prime_and_dvd horder_ne_one with ⟨p, hpprime, hpdiv⟩
  let p' : Nat.Primes := ⟨p, hpprime⟩
  have hpSupp : p' ∈ section14ElementPrimeSupport y := by
    change p' ∈ subgroupPrimeSet (Subgroup.zpowers y)
    change p' ∈ {q : Nat.Primes | q.val ∣ Nat.card (Subgroup.zpowers y)}
    change p ∣ Nat.card (Subgroup.zpowers y)
    rw [Nat.card_zpowers]
    exact hpdiv
  have hpSigma : p' ∈ section10SigmaPrimes M := hySigma hpSupp
  have hy_eq : y = g * x * g⁻¹ := by
    simpa [MulAut.conj_apply] using hxy.symm
  have hconj_order : orderOf (g * x * g⁻¹) = orderOf x := by
    simpa [MulAut.conj_apply] using (MulAut.conj g).orderOf_eq x
  have hpOrderX : p ∣ orderOf x := by
    have hpOrderConj : p ∣ orderOf (g * x * g⁻¹) := by
      simpa [hy_eq] using hpdiv
    simpa [hconj_order] using hpOrderConj
  have hpKcard : p ∣ Nat.card K :=
    hpOrderX.trans (Subgroup.orderOf_dvd_natCard K hxK)
  have hpKsub : p ∣ Nat.card (K.subgroupOf M) := by
    simpa [section12_card_subgroupOf_eq hK.1] using hpKcard
  have hpKappa : p' ∈ section14KappaPrimes M :=
    hK.2.p_in_pi_of_p_dvd_card p' (by simpa [p'] using hpKsub)
  exact section16_kappa_subset_not_sigma (M := M) hpKappa hpSigma

private theorem CFSG.section16_conjugates_hatZ_subset_A0_diff_A
    {M K U : Subgroup G}
    (hMP : M ∈ section14MFamilyP G)
    (hKU : section15KUData M K U) :
    section16ConjugatesOfSetBySet
        (section16HatZ K (section16Kstar M K)) (M : Set G) ⊆
      section16AZeroSet M K \ section16ASet M U := by
  classical
  intro a ha
  rcases ha with ⟨t, htHat, m, hmM, rfl⟩
  have hUHall := hKU.2.2.2.1
  have hNormComp : section14NormalComplementIn M K (U ⊔ section10Msigma M) :=
    ⟨hKU.2.1, hKU.2.2.2.2.2.1⟩
  have hZdp : section14ZInternalDirectProduct M K :=
    (theorem_14_7_d (G := G) (M := M) (K := K) hMP hKU.1).1
  rcases section16_hatZ_decomp_with_kstar_zpower
      (G := G) (M := M) (K := K) hMP hKU.1 hZdp htHat with
    ⟨y, k, hyKstar, hyne, hkK, hkne, htEq, hykComm, hyT⟩
  have hySigma : y ∈ section10Msigma M := by
    simpa [section16Kstar, section14KStar] using hyKstar.1
  have hyM : y ∈ M := section16_msigma_le (G := G) M hySigma
  have hkM : k ∈ M := hKU.1.1 hkK
  have htM : t ∈ M := by
    rw [htEq]
    exact M.mul_mem hyM hkM
  have haM : m * t * m⁻¹ ∈ M :=
    M.mul_mem (M.mul_mem hmM htM) (M.inv_mem hmM)
  have hyCommT : Commute y t := by
    change y * t = t * y
    rw [htEq]
    calc
      y * (y * k) = y * (k * y) := by rw [hykComm.eq]
      _ = (y * k) * y := by simp [mul_assoc]
  have hHatSigma :
      m * t * m⁻¹ ∈ section16HatMsigmaSet M := by
    refine ⟨haM, ?_⟩
    have hmNormSigma : m ∈ Subgroup.normalizer (section10Msigma M : Set G) :=
      section12_le_normalizer_msigma (M := M) hmM
    have hyConjSigma : m * y * m⁻¹ ∈ section10Msigma M :=
      (Subgroup.mem_normalizer_iff.mp hmNormSigma y).1 hySigma
    have hyConjCent :
        m * y * m⁻¹ ∈ Subgroup.centralizer ({m * t * m⁻¹} : Set G) := by
      rw [Subgroup.mem_centralizer_singleton_iff]
      have h := congrArg (fun z : G => m * z * m⁻¹) hyCommT.eq
      simpa [mul_assoc] using h
    have hyConjNe : m * y * m⁻¹ ≠ 1 := by
      intro hyConjOne
      apply hyne
      have h := congrArg (fun z : G => m⁻¹ * z * m) hyConjOne
      simpa [mul_assoc] using h
    apply Subgroup.ne_bot_iff_exists_ne_one.mpr
    let zC : elementCentralizerIn (section10Msigma M) (m * t * m⁻¹) :=
      ⟨m * y * m⁻¹, ⟨hyConjSigma, hyConjCent⟩⟩
    refine ⟨zC, ?_⟩
    intro hzC
    exact hyConjNe (by simpa [zC] using congrArg Subtype.val hzC)
  have hNotConjK :
      m * t * m⁻¹ ∉
        section16ConjugatesOfSetBySet
          (section16NonidentityElements (K : Set G)) (M : Set G) := by
    intro hConjK
    rcases hConjK with ⟨x, hxKnon, n, hnM, hEqA⟩
    rcases hxKnon with ⟨hxK, _hxne⟩
    let g : G := m⁻¹ * n
    have hgM : g ∈ M := M.mul_mem (M.inv_mem hmM) hnM
    have htKg : t ∈ K.conjBy g := by
      rw [Subgroup.conjBy, Subgroup.mem_map]
      refine ⟨x, hxK, ?_⟩
      simp [MulAut.conj_apply, g]
      have h := congrArg (fun z : G => m⁻¹ * z * m) hEqA
      simpa [mul_assoc] using h.symm
    have hyKg : y ∈ K.conjBy g :=
      (Subgroup.zpowers_le.2 htKg) hyT
    exact hyne
      (section16_eq_one_of_mem_kstar_and_conj_k
        (G := G) (M := M) (K := K) hMP hKU.1 hgM hyKstar hyKg)
  have hNotA : m * t * m⁻¹ ∉ section16ASet M U := by
    intro hA
    let N : Subgroup G := U ⊔ section10Msigma M
    have hU_norm_sigma :
        U ≤ Subgroup.normalizer (section10Msigma M : Set G) :=
      hUHall.1.trans (section12_le_normalizer_msigma (M := M))
    have hNset :
        ((N : Subgroup G) : Set G) =
          (U : Set G) * (section10Msigma M : Set G) := by
      simpa [N] using
        Subgroup.coe_mul_of_left_le_normalizer_right U (section10Msigma M)
          hU_norm_sigma
    have haN : m * t * m⁻¹ ∈ N := by
      have haNset : m * t * m⁻¹ ∈ (N : Set G) := by
        simpa [hNset] using hA.2.1
      exact haNset
    have hNnorm : section10NormalIn N M := by
      simpa [N] using hNormComp.2
    have hMnormN : M ≤ Subgroup.normalizer (N : Set G) :=
      (Subgroup.normal_subgroupOf_iff_le_normalizer hNnorm.1).1 hNnorm.2
    have htN : t ∈ N := by
      have hconjN :
          m⁻¹ * (m * t * m⁻¹) * (m⁻¹)⁻¹ ∈ N :=
        (Subgroup.mem_normalizer_iff.mp (hMnormN (M.inv_mem hmM))
          (m * t * m⁻¹)).1 haN
      simpa [mul_assoc] using hconjN
    have hyN : y ∈ N := by
      exact Subgroup.mem_sup_right hySigma
    have hkN : k ∈ N := by
      have hkEq : k = y⁻¹ * t := by
        rw [htEq]
        group
      rw [hkEq]
      exact N.mul_mem (N.inv_mem hyN) htN
    have hkBot : k ∈ (⊥ : Subgroup G) := by
      simpa [N, hNormComp.1.2.2.2.eq_bot] using
        (show k ∈ K ⊓ N from ⟨hkK, hkN⟩)
    exact hkne (Subgroup.mem_bot.mp hkBot)
  have htne : m * t * m⁻¹ ≠ 1 := by
    have ht_ne : t ≠ 1 := by
      intro ht_one
      exact htHat.2 (Or.inl (by
        simp [ht_one]))
    intro h
    exact ht_ne (by
      have h' := congrArg (fun z : G => m⁻¹ * z * m) h
      simpa [mul_assoc] using h')
  exact ⟨⟨hHatSigma, hNotConjK, htne⟩, hNotA⟩

private theorem CFSG.section16_A0_diff_A_subset_conjugates_hatZ
    {M K U : Subgroup G}
    (hMP : M ∈ section14MFamilyP G)
    (hKU : section15KUData M K U) :
    section16AZeroSet M K \ section16ASet M U ⊆
      section16ConjugatesOfSetBySet
        (section16HatZ K (section16Kstar M K)) (M : Set G) := by
  classical
  intro a ha
  rcases ha with ⟨haA0, haNotA⟩
  rcases haA0 with ⟨haHat, haNotConjK, hane⟩
  let S : Subgroup G := section10Msigma M
  have hUHall := hKU.2.2.2.1
  have hReg := hKU.2.2.2.2.1
  have hNormComp : section14NormalComplementIn M K (U ⊔ S) :=
    ⟨by simpa [S] using hKU.2.1, by simpa [S] using hKU.2.2.2.2.2.1⟩
  let N : Subgroup G := U ⊔ section10Msigma M
  have hNcomp : section12ComplementIn M K N := hNormComp.1
  have hNnorm : section10NormalIn N M := hNormComp.2
  have haM : a ∈ M := haHat.1
  have hU_norm_sigma :
      U ≤ Subgroup.normalizer (section10Msigma M : Set G) :=
    hUHall.1.trans (section12_le_normalizer_msigma (M := M))
  have hNset :
      ((N : Subgroup G) : Set G) =
        (U : Set G) * (section10Msigma M : Set G) := by
    simpa [N] using
      Subgroup.coe_mul_of_left_le_normalizer_right U (section10Msigma M)
        hU_norm_sigma
  have haNotProd : a ∉ (U : Set G) * (section10Msigma M : Set G) := by
    intro haProd
    exact haNotA ⟨haHat, haProd, hane⟩
  have haNotN : a ∉ N := by
    intro haN
    have haN' : a ∈ (N : Set G) := haN
    exact haNotProd (by simpa [hNset] using haN')
  let Ksub : Subgroup M := K.subgroupOf M
  let Nsub : Subgroup M := N.subgroupOf M
  haveI : Nsub.Normal := by
    simpa [Nsub] using hNnorm.2
  let aM : M := ⟨a, haM⟩
  have htop : Ksub ⊔ Nsub = ⊤ := by
    calc
      Ksub ⊔ Nsub = (K ⊔ N).subgroupOf M := by
        symm
        exact Subgroup.subgroupOf_sup (A := K) (A' := N) (B := M)
          hNcomp.1 hNcomp.2.1
      _ = ⊤ := by
        rw [← hNcomp.2.2.1]
        simp
  have haTop : aM ∈ Ksub ⊔ Nsub := by
    simp [htop]
  rcases (Subgroup.mem_sup_of_normal_right
      (s := Ksub) (t := Nsub) (x := aM)).1 haTop with
    ⟨kM, hkKsub, nM, hnNsub, hkn⟩
  let k : G := kM
  have hkK : k ∈ K := by
    simpa [k, Ksub, Subgroup.mem_subgroupOf] using hkKsub
  have hnN : (nM : G) ∈ N := by
    simpa [Nsub, Subgroup.mem_subgroupOf] using hnNsub
  have hk_ne : k ≠ 1 := by
    intro hk_one
    have hval := congrArg (fun x : M => (x : G)) hkn
    have ha_eq_n : a = (nM : G) := by
      simpa [aM, k, hk_one] using hval.symm
    exact haNotN (by simpa [ha_eq_n] using hnN)
  let n0 : Nsub := ⟨kM * nM * kM⁻¹,
    (show Nsub.Normal from inferInstance).conj_mem nM hnNsub kM⟩
  have hn0k : (n0 : M) * kM = aM := by
    change (kM * nM * kM⁻¹) * kM = aM
    rw [← hkn]
    group
  have hKsub_card : Nat.card Ksub = Nat.card K := by
    exact section12_card_subgroupOf_eq hNcomp.1
  have hNsub_card : Nat.card Nsub = Nat.card N := by
    exact section12_card_subgroupOf_eq hNcomp.2.1
  have hLocalComp :
      Ksub.IsComplement' Nsub := by
    refine Subgroup.isComplement'_of_disjoint_and_mul_eq_univ ?_ ?_
    · rw [Subgroup.disjoint_def]
      intro x hxK hxN
      apply Subtype.ext
      have hxInf : ((x : M) : G) ∈ K ⊓ N := by
        exact ⟨by simpa [Ksub, Subgroup.mem_subgroupOf] using hxK,
          by simpa [Nsub, Subgroup.mem_subgroupOf] using hxN⟩
      have hxBot : ((x : M) : G) ∈ (⊥ : Subgroup G) := by
        simpa [hNcomp.2.2.2.eq_bot] using hxInf
      simpa using hxBot
    · rw [Set.eq_univ_iff_forall]
      intro x
      have hxTop : x ∈ Ksub ⊔ Nsub := by
        simp [htop]
      rcases (Subgroup.mem_sup_of_normal_right
          (s := Ksub) (t := Nsub) (x := x)).1 hxTop with
        ⟨k0, hk0, n0, hn0, hmul⟩
      exact ⟨k0, hk0, n0, hn0, hmul⟩
  have hcopKsubNsub :
      Nat.Coprime (Nat.card Ksub) (Nat.card Nsub) := by
    have hHallCoprime : Nat.Coprime (Nat.card Ksub) Ksub.index :=
      hKU.1.2.card_coprime_index
    simpa [hLocalComp.symm.index_eq_card] using hHallCoprime
  have hcop_k_Nsub : Nat.Coprime (orderOf kM) (Nat.card Nsub) :=
    Nat.Coprime.of_dvd_left
      (Subgroup.orderOf_dvd_natCard Ksub hkKsub) hcopKsubNsub
  rcases section16_exists_centralizer_coset_conj_of_coprime
      (K := Nsub) (g := kM) hcop_k_Nsub n0 with
    ⟨r, u, huCent, huConj⟩
  let rG : G := (r : M)
  let uG : G := (u : M)
  have hrM : rG ∈ M := (r : M).property
  have huNsub : (u : M) ∈ Nsub := (Subgroup.mem_inf.mp huCent).1
  have huElemCent : (u : M) ∈ Section2.elementCentralizer kM :=
    (Subgroup.mem_inf.mp huCent).2
  have hcommM : Commute (u : M) kM := by
    change (u : M) * kM = kM * (u : M)
    exact (section16_section2_mem_elementCentralizer_commute
      (g := kM) (c := (u : M)) huElemCent).symm
  have hcommG : Commute uG k := by
    change uG * k = k * uG
    exact congrArg (fun x : M => (x : G)) hcommM.eq
  have hconjG :
      uG * k = rG⁻¹ * a * rG := by
    have hval := congrArg (fun x : M => (x : G)) huConj
    simpa [uG, rG, k, aM, hn0k, mul_assoc] using hval
  let X : Subgroup G := Subgroup.zpowers k
  have hXleK : X ≤ K := Subgroup.zpowers_le.mpr hkK
  have hXne : X ≠ ⊥ := by
    intro hXbot
    have hkBot : k ∈ (⊥ : Subgroup G) := by
      simpa [X, hXbot] using (Subgroup.mem_zpowers k)
    exact hk_ne (Subgroup.mem_bot.mp hkBot)
  have hXreg : section14ActsRegularlyOn X U := by
    refine ⟨hXleK.trans hReg.1, ?_⟩
    intro x hxX hxne
    exact hReg.2 x (hXleK hxX) hxne
  have hXnormSigma : X ≤ Subgroup.normalizer (section10Msigma M : Set G) :=
    hXleK.trans (hKU.1.1.trans (section12_le_normalizer_msigma (M := M)))
  have hdisjUSigma : Disjoint U (section10Msigma M) := by
    have hdisjSigmaKU : Disjoint (section10Msigma M) (K ⊔ U) :=
      hKU.2.2.1.2.2.2
    rw [Subgroup.disjoint_def]
    intro x hxU hxSigma
    have hxKU : x ∈ K ⊔ U := Subgroup.mem_sup_right hxU
    exact Subgroup.disjoint_def.mp hdisjSigmaKU hxSigma hxKU
  have hCentEq :
      subgroupCentralizerIn N X =
        subgroupCentralizerIn (section10Msigma M) X := by
    simpa [N] using
      section14_b1_subgroupCentralizerIn_sup_eq_of_regular
        (G := G) (X := X) (U := U) (S := section10Msigma M)
        hXne hXreg hXnormSigma hU_norm_sigma hdisjUSigma
  have huCentX : uG ∈ subgroupCentralizerIn N X := by
    refine ⟨by
      simpa [uG] using (Subgroup.mem_subgroupOf.mp huNsub), ?_⟩
    change uG ∈ Subgroup.centralizer ((X : Subgroup G) : Set G)
    rw [Subgroup.mem_centralizer_iff]
    intro z hzX
    rcases Subgroup.mem_zpowers_iff.mp hzX with ⟨n, rfl⟩
    exact (hcommG.zpow_right n).eq.symm
  have huCentSigma : uG ∈ subgroupCentralizerIn (section10Msigma M) X := by
    simpa [hCentEq] using huCentX
  have huSigma : uG ∈ section10Msigma M := huCentSigma.1
  have huKstar : uG ∈ section14KStar M K :=
    section14_mem_kstar_of_mem_msigma_of_mem_hall_of_commute
      (G := G) (M := M) (K := K) hMP hKU.1
      huSigma hkK hk_ne hcommG
  have hu_ne : uG ≠ 1 := by
    intro hu_one
    apply haNotConjK
    refine ⟨k, ⟨hkK, hk_ne⟩, rG, hrM, ?_⟩
    have hk_conj : k = rG⁻¹ * a * rG := by
      simpa [uG, hu_one] using hconjG
    calc
      a = rG * (rG⁻¹ * a * rG) * rG⁻¹ := by group
      _ = rG * k * rG⁻¹ := by rw [← hk_conj]
  have hwidehatKU : k * uG ∈ section14WidehatZ M K :=
    section14_mul_mem_widehatZ_of_mem_hall_of_mem_kstar
      (G := G) (M := M) (K := K) hMP hKU.1 hkK hk_ne huKstar hu_ne
  have hwidehatUK : uG * k ∈ section16HatZ K (section16Kstar M K) := by
    have huk : uG * k = k * uG := hcommG.eq
    simpa [huk, section16HatZ, section16ZSubgroup, section16Kstar,
      section14WidehatZ, section14Z, section14KStar] using hwidehatKU
  refine ⟨uG * k, hwidehatUK, rG, hrM, ?_⟩
  calc
    a = rG * (rG⁻¹ * a * rG) * rG⁻¹ := by group
    _ = rG * (uG * k) * rG⁻¹ := by rw [← hconjG]

public theorem CFSG.section16_conjugates_hatZ_eq_A0_diff_A
    {M K U : Subgroup G}
    (hMP : M ∈ section14MFamilyP G)
    (hKU : section15KUData M K U) :
    section16ConjugatesOfSetBySet
        (section16HatZ K (section16Kstar M K)) (M : Set G) =
      section16AZeroSet M K \ section16ASet M U := by
  exact Set.Subset.antisymm
    (section16_conjugates_hatZ_subset_A0_diff_A
      (G := G) (M := M) (K := K) (U := U) hMP hKU)
    (section16_A0_diff_A_subset_conjugates_hatZ
      (G := G) (M := M) (K := K) (U := U) hMP hKU)

private theorem CFSG.section16_A0_diff_A_TI
    {M K U : Subgroup G}
    (hMP : M ∈ section14MFamilyP G)
    (hKU : section15KUData M K U) :
    section16TISubset (section16AZeroSet M K \ section16ASet M U) := by
  classical
  have hKHall : section12HallSubgroupIn (section14KappaPrimes M) K M := hKU.1
  have h147e := theorem_14_7_e (G := G) (M := M) (K := K) hMP hKHall
  have hXleM :
      section16HatZ K (section16Kstar M K) ⊆ M := by
    intro x hx
    have hxZ : x ∈ section16ZSubgroup K (section16Kstar M K) := hx.1
    have hZleM : section16ZSubgroup K (section16Kstar M K) ≤ M := by
      exact sup_le hKHall.1 (fun z hz => section16_msigma_le (G := G) M hz.1)
    exact hZleM hxZ
  have hOutside :
      ∀ g : G, g ∉ M →
        section16HatZ K (section16Kstar M K) ∩ (M.conjBy g : Set G) = ∅ := by
    intro g hgM
    simpa [section16HatZ, section16ZSubgroup, section16Kstar,
      section14WidehatZ, section14Z, section14KStar] using h147e.2.2.1 g hgM
  have hTIConj :
      section16TISubset
        (section16ConjugatesOfSetBySet
          (section16HatZ K (section16Kstar M K)) (M : Set G)) :=
    section16_conjugatesBySet_TI_of_outside_disjoint
      (G := G) (M := M) hXleM hOutside
  simpa [section16_conjugates_hatZ_eq_A0_diff_A
    (G := G) (M := M) (K := K) (U := U) hMP hKU] using hTIConj

/-- Theorem C of Section 16. -/
public theorem CFSG.theorem_16_C
    {M MF K U : Subgroup G}
    (hM : M ∈ section9MaximalSubgroups G)
    (hMF : section16MFSubgroup M MF)
    (hKU : section16KUData M K U)
    (hK : K ≠ ⊥) :
    section16TheoremCConclusions M MF K U := by
  classical
  have hKU15 : section15KUData M K U :=
    section16_kudata_to_section15 (G := G) hKU
  have hMF15 : section15MFSubgroup M MF :=
    section16_mf_to_section15 (G := G) hMF
  have hKHall : section12HallSubgroupIn (section14KappaPrimes M) K M := hKU15.1
  have hMP : M ∈ section14MFamilyP G :=
    section16_MFamilyP_of_nontrivial_hall_kappa (G := G) hM hKHall hK
  let Kstar : Subgroup G := section16Kstar M K
  let Mstar : Subgroup G := section14Theorem14_7Partner M K
  have h151b := lemma_15_1_b (G := G) (M := M) (K := K) (U := U) hM hKU15 hK
  have h156 := corollary_15_6 (G := G) (M := M) (MF := MF) (K := K)
    hMP hMF15 hKHall
  have hKstar_ne : Kstar ≠ ⊥ := by
    simpa [Kstar, section16Kstar, section14KStar] using h156.1
  have h147d := theorem_14_7_d (G := G) (M := M) (K := K) hMP hKHall
  have h147e := theorem_14_7_e (G := G) (M := M) (K := K) hMP hKHall
  have h147f := theorem_14_7_f (G := G) (M := M) (K := K) hMP hKHall
  have hKstar_pos : ⊥ < Kstar := bot_lt_iff_ne_bot.mpr hKstar_ne
  rcases Subgroup.ne_bot_iff_exists_ne_one.mp hK with ⟨x, hxne⟩
  rcases Subgroup.ne_bot_iff_exists_ne_one.mp hKstar_ne with ⟨y, hyne⟩
  have hInterData :=
    h147d.2.2 (x : G) (y : G) x.property (by simpa using hxne)
      (by exact y.property)
      (by simpa using hyne)
  have hCase :
      section16CaseP2 K U ∨ section16MaximalTypeP2 Mstar := by
    rcases h147f with hfirst | hsecond
    · left
      exact ⟨hK, section16_U_ne_bot_of_MFamilyP2 (G := G) hKU15 hfirst.1⟩
    · right
      simpa [Mstar, section16MaximalTypeP2] using hsecond.1
  have hHatZTI :
      section16TISubsetWithNormalizer (section16HatZ K Kstar)
        (section16ZSubgroup K Kstar) := by
    simpa [Kstar, section16HatZ, section16ZSubgroup, section16Kstar,
      section14WidehatZ, section14Z, section14KStar] using
      (section16_section14TISet_to_section16TISubsetWithNormalizer
        (G := G) h147e.1 h147e.2.1)
  dsimp [section16TheoremCConclusions]
  refine ⟨
    h151b.2,
    section16_normalizer_U_not_le_M (G := G) hM hKU15 hK,
    ?_,
    hKstar_pos,
    ?_,
    ?_,
    h151b.1,
    ?_,
    Mstar,
    ?_⟩
  · change IsCyclic (section14KStar M K)
    exact h156.2.1
  · simpa [Kstar, section16Kstar, section14KStar] using h156.2.2.1
  · exact h156.2.2.2.2
  · simpa [Kstar, section16Kstar, section14KStar,
      section16SecondDerivedSubgroup, section15SecondDerivedSubgroup] using h156.2.2.2.1
  · refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · simpa [Mstar, section16MaximalTypeP] using
        (theorem_14_7_data (G := G) (M := M) (K := K) hMP hKHall).1
    · intro N hN
      exact section16_theoremC_partner_unique (G := G) hMP hKHall hK
        (by simpa [section16MaximalTypeP] using hN.1)
        (by
          simpa [Kstar, section16Kstar, section14KStar] using hN.2.1)
        (by
          simpa [Kstar, section16KappaPrimes, section16Kstar, section14KStar] using
            hN.2.2)
    · simpa [Mstar, Kstar, section16Kstar, section14KStar] using
        (theorem_14_7_c (G := G) (M := M) (K := K) hMP hKHall).1
    · simpa [Mstar, Kstar, section16KappaPrimes, section16Kstar, section14KStar] using
        (theorem_14_7_b (G := G) (M := M) (K := K) hMP hKHall).1
    · intro X hX
      exact (proposition_14_2_c (G := G) (M := M) (K := K) hMP hKHall).2 X
        (by
          simpa [Kstar, section16Kstar, section14KStar] using
            section16_primeOrderSubgroupOf_to_section12 (G := G) hX)
    · intro Y hY
      exact theorem_14_7_a (G := G) (M := M) (K := K) hMP hKHall Y
        (section16_primeOrderSubgroupOf_to_section12 (G := G) hY)
    · simpa [Mstar, Kstar, section16ZSubgroup, section16Kstar, section14Z, section14KStar]
        using hInterData.1
    · simpa [Kstar, section16ZSubgroup, section16Kstar, section14ZInternalDirectProduct,
        section14Z, section14KStar] using h147d.1
    · change IsCyclic (section14Z M K)
      exact h147d.2.1
    · exact hCase
    · intro H hH
      simpa [Mstar, section16MaximalTypeP, section14ConjugateSubgroups] using
        theorem_14_7_g (G := G) (M := M) (K := K) hMP hKHall H
          (by simpa [section16MaximalTypeP] using hH)
    · exact hHatZTI
    · simpa [Kstar] using
        section16_conjugates_hatZ_eq_A0_diff_A (G := G) (M := M) (K := K) (U := U)
          hMP hKU15
    · exact section16_A0_diff_A_TI (G := G) (M := M) (K := K) (U := U) hMP hKU15
    · constructor
      · exact section16_fitting_TI_prime_order_of_U_ne_bot
          (G := G) hM hMF15 hKU15 hK
      · intro hUbot
        simpa [Kstar] using
          section16_Kstar_prime_order_of_U_eq_bot (G := G) hMP hKU15 hUbot

/-- Theorem D: the four fusion and centralizer assertions for `M_sigma`. -/
@[expose] public def CFSG.section16TheoremDConclusions
    (M MF _K _U : Subgroup G) : Prop :=
  (∀ x y : G, x ∈ section10Msigma M → y ∈ section10Msigma M →
    section16ConjugateInSubgroup ⊤ x y → section16ConjugateInSubgroup M x y) ∧
  (∀ g : G, g ∉ M →
    section10Msigma M ⊓ M.conjBy g =
      section10Msigma M ⊓ (section10Msigma M).conjBy g ∧
        IsCyclic ((section10Msigma M ⊓ M.conjBy g : Subgroup G))) ∧
  ∀ x : G, x ∈ section10Msigma M → x ≠ 1 →
    ∃ R : Subgroup G,
      section16TheoremDComplement M x R ∧
        (¬ Subgroup.centralizer ({x} : Set G) ≤ M →
          ∃ N : Subgroup G,
            section9MaximalSubgroupsContaining (Subgroup.centralizer ({x} : Set G)) = {N} ∧
              R = elementCentralizerIn (section10Msigma N) x ∧
              (∃ NF NK NU : Subgroup G, section16MFSubgroup N NF ∧
                section16KUData N NK NU ∧
                  section10Msigma N = NF ∧
                    x ∈ section16ASet N NU \ (section10Msigma N : Set G)) ∧
              (section16MaximalTypeF N ∨ section16MaximalTypeP2 N) ∧
              section12ComplementIn N (section10Msigma N) (M ⊓ N) ∧
              (section16MaximalTypeP2 N →
                section16MaximalTypeF M ∧
                  section16FrobeniusWithCyclicComplement M MF ∧
                    ¬ section16TISubset (MF : Set G)))

end MainResults
