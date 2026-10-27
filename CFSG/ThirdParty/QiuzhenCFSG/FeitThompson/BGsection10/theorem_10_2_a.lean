module

public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.BGsection10.theorem_10_1_c
public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.BGsection4.theorem_4_20_a
public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.BGsection10.theorem_10_1_d
public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.BGsection10.theorem_10_1_e
import Mathlib.GroupTheory.Schreier
import Mathlib.LinearAlgebra.Projectivization.Cardinality

namespace CFSG
end CFSG
open CFSG

open scoped Pointwise commutatorElement

/-!
# Theorem 10.2(a) from BG Section 10

This file records a statement-only scaffold for Section 10 of
`Local Analysis for the Odd Order Theorem`.

The local PDF extraction mangles the Greek letters used in the book. This
module imports the shared Section 10 notation from `FeitThompson.BGsection10.Defs`.
-/

section Section10

variable {G : Type*} [Group G] [Finite G] [IsMinCE G]

public theorem CFSG.section10_alpha_sylow_normalizer_le_pre
    {M : Subgroup G} (hM : M ∈ section9MaximalSubgroups G)
    {q : Nat.Primes} (hqα : q ∈ section10AlphaPrimes M)
    (P : Sylow q.val M) :
    Subgroup.normalizer ((section10AmbientSylowSubgroup M P : Subgroup G) : Set G) ≤ M := by
  classical
  have : Fact q.val.Prime := ⟨q.2⟩
  let PG : Subgroup G := section10AmbientSylowSubgroup M P
  have hPG_le_M : PG ≤ M := by
    intro x hx
    rcases Subgroup.mem_map.mp hx with ⟨y, _hy, rfl⟩
    exact y.property
  have hqrankM : 3 ≤ primeRank q.val M :=
    Nat.succ_le_of_lt hqα.2
  have hPrank : 3 ≤ groupRank (P : Subgroup M) :=
    hqrankM.trans (section10_primeRank_le_groupRank_sylow_pre (G := M) P)
  let ePG : (P : Subgroup M) ≃* PG :=
    Subgroup.equivMapOfInjective
      (f := M.subtype) (P : Subgroup M) M.subtype_injective
  have hPGrank : 3 ≤ groupRank PG :=
    hPrank.trans
      (section10_groupRank_le_of_equiv_pre
        (R := PG) (S := (P : Subgroup M)) ePG.symm)
  have hqP : q.val ∣ Nat.card (P : Subgroup M) :=
    Sylow.dvd_card_of_dvd_card P hqα.1
  have hPGcard_eq : Nat.card PG = Nat.card (P : Subgroup M) := by
    simpa [PG, section10AmbientSylowSubgroup] using
      (Subgroup.card_map_of_injective
        (K := (P : Subgroup M)) (f := M.subtype) M.subtype_injective)
  have hqPG : q.val ∣ Nat.card PG := by
    rwa [hPGcard_eq]
  have hPGne : PG ≠ ⊥ := by
    intro hbot
    have hcard : Nat.card PG = 1 := by
      simp [hbot]
    rw [hcard] at hqPG
    exact q.2.not_dvd_one hqPG
  exact section10_normalizer_le_maximal_of_three_le_groupRank_seed
    (P := PG) (X := PG) (M := M) hM hPG_le_M Subgroup.le_normalizer
    hPG_le_M hPGne hPGrank

public theorem CFSG.section10_alpha_subset_sigma
    {M : Subgroup G} (hM : M ∈ section9MaximalSubgroups G) :
    section10AlphaPrimes M ⊆ section10SigmaPrimes M := by
  intro p hpα
  have : Fact p.val.Prime := ⟨p.2⟩
  let P : Sylow p.val M := default
  exact ⟨hpα.1, P, section10_alpha_sylow_normalizer_le_pre hM hpα P⟩

omit [Group G] [Finite G] [IsMinCE G] in
public theorem CFSG.section10_piCore_mono
    {H : Type*} [Group H] [Finite H] {π ρ : Set Nat.Primes}
    (hπρ : π ⊆ ρ) :
    piCore π H ≤ piCore ρ H := by
  have hπ : IsPiSubgroup (G := H) π (piCore π H) :=
    piCore_isPiSubgroup (G := H) π
  have hρ : IsPiSubgroup (G := H) ρ (piCore π H) := by
    intro p hp
    exact hπρ (hπ p hp)
  have hmem :
      piCore π H ∈
        ({K : Subgroup H | K.Normal ∧ IsPiSubgroup (G := H) ρ K} : Set (Subgroup H)) :=
    ⟨inferInstance, hρ⟩
  exact le_sSup hmem

public theorem CFSG.section10_malphaSubgroup_le_msigmaSubgroup
    {M : Subgroup G} (hM : M ∈ section9MaximalSubgroups G) :
    section10MalphaSubgroup M ≤ section10MsigmaSubgroup M := by
  simpa [section10MalphaSubgroup, section10MsigmaSubgroup] using
    section10_piCore_mono (H := M) (section10_alpha_subset_sigma hM)

public theorem CFSG.section10_minCE_derivedSubgroup_eq_top :
    derivedSubgroup G = ⊤ := by
  have : IsSimpleGroup G := IsMinCE.simple
  have hnormal : (derivedSubgroup G).Normal :=
    derivedSeries_normal (G := G) 1
  rcases (haveI := hnormal; IsSimpleGroup.eq_bot_or_eq_top_of_normal (derivedSubgroup G)) with hbot | htop
  · have hcomm_bot : commutator G = ⊥ := by
      rw [_root_.commutator_def]
      exact hbot
    have hcenter_top : Subgroup.center G = ⊤ :=
      (commutator_eq_bot_iff_center_eq_top (G := G)).mp hcomm_bot
    have hcomm : ∀ a b : G, a * b = b * a := by
      intro a b
      have hb : b ∈ Subgroup.center G := by
        rw [hcenter_top]
        exact Subgroup.mem_top b
      exact Subgroup.mem_center_iff.mp hb a
    exact False.elim <|
      IsMinCE.not_solvable (G := G) (Group.isSolvable_of_comm hcomm)
  · exact htop

public theorem CFSG.section10_sigma_focal_generator_mem_ambientDerived
    {M : Subgroup G} (hM : M ∈ section9MaximalSubgroups G)
    {p : Nat.Primes} (hpσ : p ∈ section10SigmaPrimes M)
    (P : Sylow p.val M) {x y : G}
    (hxP : x ∈ section10AmbientSylowSubgroup M P)
    (hyP : y ∈ section10AmbientSylowSubgroup M P)
    (hxy : IsConj x y) :
    x⁻¹ * y ∈ ambientDerivedSubgroup M := by
  classical
  have : Fact p.val.Prime := ⟨p.property⟩
  by_cases hx1 : x = 1
  · have hy1 : y = 1 := by
      have hxy1 : IsConj 1 y := by simpa [hx1] using hxy
      exact isConj_one_right.mp hxy1
    simp [hx1, hy1, ambientDerivedSubgroup]
  · rcases isConj_iff.mp hxy with ⟨g, hgxy⟩
    let X : Subgroup G := Subgroup.zpowers x
    let PG : Subgroup G := section10AmbientSylowSubgroup M P
    have hPG_le_M : PG ≤ M := by
      intro z hz
      rcases Subgroup.mem_map.mp hz with ⟨zM, _hzP, rfl⟩
      exact zM.property
    have hxM : x ∈ M := hPG_le_M hxP
    have hyM : y ∈ M := hPG_le_M hyP
    have hXne : X ≠ ⊥ := by
      intro hXbot
      have hxbot : x ∈ (⊥ : Subgroup G) := by
        simpa [X, hXbot] using (Subgroup.mem_zpowers x)
      exact hx1 (by simpa using hxbot)
    have hX_le_PG : X ≤ PG := by
      simpa [X, PG] using (Subgroup.zpowers_le.mpr hxP)
    have hXM : X ≤ M := hX_le_PG.trans hPG_le_M
    have hPGp : IsPGroup p.val PG := by
      change IsPGroup p.val ((P : Subgroup M).map M.subtype)
      simpa using
        IsPGroup.map (p := p.val) (H := (P : Subgroup M)) P.isPGroup' M.subtype
    have hXp : IsPGroup p.val X := by
      let XPG : Subgroup PG := X.subgroupOf PG
      have hXPGp : IsPGroup p.val XPG :=
        IsPGroup.to_subgroup (H := XPG) hPGp
      exact hXPGp.of_equiv
        (Subgroup.subgroupOfEquivOfLe (H := X) (K := PG) hX_le_PG)
    have hXgM : X.conjBy g ≤ M := by
      intro z hz
      rw [Subgroup.conjBy, Subgroup.mem_map] at hz
      rcases hz with ⟨u, huX, rfl⟩
      rcases Subgroup.mem_zpowers_iff.mp (by simpa [X] using huX) with ⟨n, rfl⟩
      have hmap :
          (MulAut.conj g).toMonoidHom (x ^ n) = y ^ n := by
        rw [map_zpow]
        simp [MulAut.conj_apply, hgxy]
      rw [hmap]
      exact M.zpow_mem hyM n
    rcases theorem_10_1_a hM hpσ hXne hXp hXM hXgM with ⟨m, c, hg⟩
    have hcx : (c : G) * x * (c : G)⁻¹ = x := by
      have hcomm := (Subgroup.mem_centralizer_iff.mp c.property) x (by
        simp [X])
      calc
        (c : G) * x * (c : G)⁻¹ = x * (c : G) * (c : G)⁻¹ := by
          rw [← hcomm]
        _ = x := by simp [mul_assoc]
    have hy_eq : y = (m : G) * x * (m : G)⁻¹ := by
      calc
        y = g * x * g⁻¹ := hgxy.symm
        _ = ((m : G) * (c : G)) * x * (((m : G) * (c : G))⁻¹) := by rw [hg]
        _ = (m : G) * ((c : G) * x * (c : G)⁻¹) * (m : G)⁻¹ := by group
        _ = (m : G) * x * (m : G)⁻¹ := by rw [hcx]
    let xM : M := ⟨x, hxM⟩
    have hlocal :
        ⁅xM⁻¹, m⁆ ∈ derivedSubgroup M := by
      change ⁅xM⁻¹, m⁆ ∈ derivedSeries M 1
      rw [derivedSeries_one, _root_.commutator_def]
      exact Subgroup.commutator_mem_commutator (by simp) (by simp)
    have hmap :
        ((xM⁻¹ : M) * m * xM * m⁻¹ : M) ∈ derivedSubgroup M := by
      simpa [commutatorElement_def, mul_assoc] using hlocal
    have hambient :
        (((xM⁻¹ : M) * m * xM * m⁻¹ : M) : G) ∈ ambientDerivedSubgroup M :=
      Subgroup.mem_map_of_mem M.subtype hmap
    simpa [ambientDerivedSubgroup, xM, hy_eq, mul_assoc] using hambient

public theorem CFSG.section10_sigma_ambient_sylow_le_ambientDerived
    {M : Subgroup G} (hM : M ∈ section9MaximalSubgroups G)
    {p : Nat.Primes} (hpσ : p ∈ section10SigmaPrimes M)
    (P : Sylow p.val M) :
    section10AmbientSylowSubgroup M P ≤ ambientDerivedSubgroup M := by
  classical
  have : Fact p.val.Prime := ⟨p.property⟩
  let PG : Subgroup G := section10AmbientSylowSubgroup M P
  have hPGp : IsPGroup p.val PG := by
    change IsPGroup p.val ((P : Subgroup M).map M.subtype)
    simpa using
      IsPGroup.map (p := p.val) (H := (P : Subgroup M)) P.isPGroup' M.subtype
  rcases IsPGroup.exists_le_sylow (G := G) (p := p.val) hPGp with ⟨S, hPGS⟩
  have hS_eq : (S : Subgroup G) = PG :=
    section10_sigma_ambient_sylow_eq_of_le_sylow hpσ P S (by simpa [PG] using hPGS)
  have hfocal_le :
      Subgroup.closure {z : G | ∃ x : G, x ∈ (S : Subgroup G) ∧
        ∃ y : G, y ∈ (S : Subgroup G) ∧ IsConj x y ∧ z = x⁻¹ * y} ≤
        ambientDerivedSubgroup M := by
    rw [Subgroup.closure_le]
    intro z hz
    rcases hz with ⟨x, hxS, y, hyS, hxy, rfl⟩
    exact section10_sigma_focal_generator_mem_ambientDerived hM hpσ P
      (by simpa [PG, hS_eq] using hxS)
      (by simpa [PG, hS_eq] using hyS) hxy
  intro x hxPG
  have hxS : x ∈ (S : Subgroup G) := by
    simpa [PG, hS_eq] using hxPG
  have hxDerG : x ∈ derivedSubgroup G := by
    rw [section10_minCE_derivedSubgroup_eq_top]
    exact Subgroup.mem_top x
  have hxInf : x ∈ ((S : Subgroup G) ⊓ derivedSubgroup G) := ⟨hxS, hxDerG⟩
  have hxClosure :
        x ∈ Subgroup.closure {z : G | ∃ x : G, x ∈ (S : Subgroup G) ∧
        ∃ y : G, y ∈ (S : Subgroup G) ∧ IsConj x y ∧ z = x⁻¹ * y} := by
    rw [← theorem_1_17 (G := G) p.val S]
    exact hxInf
  exact hfocal_le hxClosure

public theorem CFSG.section10_sigma_sylow_le_derivedSubgroup
    {M : Subgroup G} (hM : M ∈ section9MaximalSubgroups G)
    {p : Nat.Primes} (hpσ : p ∈ section10SigmaPrimes M)
    (P : Sylow p.val M) :
    (P : Subgroup M) ≤ derivedSubgroup M := by
  have hPG_le :
      section10AmbientSylowSubgroup M P ≤ ambientDerivedSubgroup M :=
    section10_sigma_ambient_sylow_le_ambientDerived hM hpσ P
  intro x hxP
  have hxPG : ((x : M) : G) ∈ section10AmbientSylowSubgroup M P :=
    Subgroup.mem_map_of_mem M.subtype hxP
  have hxDerG : ((x : M) : G) ∈ ambientDerivedSubgroup M := hPG_le hxPG
  rcases Subgroup.mem_map.mp hxDerG with ⟨d, hd, hd_eq⟩
  have hxd : x = d := Subtype.ext hd_eq.symm
  simpa [hxd] using hd

public theorem CFSG.section10_sigma_not_dvd_quotient_derived
    {M : Subgroup G} (hM : M ∈ section9MaximalSubgroups G)
    {p : Nat.Primes} (hpσ : p ∈ section10SigmaPrimes M) :
    ¬ p.val ∣ Nat.card (M ⧸ derivedSubgroup M) := by
  classical
  have : Fact p.val.Prime := ⟨p.property⟩
  let P : Sylow p.val M := default
  have hP_le_der : (P : Subgroup M) ≤ derivedSubgroup M :=
    section10_sigma_sylow_le_derivedSubgroup hM hpσ P
  intro hp_dvd
  have hp_dvd_der_index : p.val ∣ (derivedSubgroup M).index := by
    simpa [Subgroup.index_eq_card] using hp_dvd
  have hidx_dvd : (derivedSubgroup M).index ∣ (P : Subgroup M).index :=
    Subgroup.index_dvd_of_le hP_le_der
  exact P.not_dvd_index (hp_dvd_der_index.trans hidx_dvd)

public theorem CFSG.section10_msigmaSubgroup_le_derivedSubgroup
    {M : Subgroup G} (hM : M ∈ section9MaximalSubgroups G) :
    section10MsigmaSubgroup M ≤ derivedSubgroup M := by
  classical
  let K : Subgroup M := section10MsigmaSubgroup M
  let D : Subgroup M := derivedSubgroup M
  let q : M →* M ⧸ D := QuotientGroup.mk' D
  have hKmap_bot : K.map q = ⊥ := by
    by_contra hne
    have hcard_ne_one : Nat.card (K.map q) ≠ 1 := by
      intro hcard
      exact hne ((Subgroup.card_eq_one (H := K.map q)).mp hcard)
    obtain ⟨r, hrprime, hrdvd⟩ := Nat.exists_prime_and_dvd hcard_ne_one
    let p : Nat.Primes := ⟨r, hrprime⟩
    have hp_dvd_K : p.val ∣ Nat.card K := by
      exact hrdvd.trans (card_map_dvd_card (f := q) (H := K))
    have hpσ : p ∈ section10SigmaPrimes M := by
      simpa [K, section10MsigmaSubgroup] using
        (piCore_isPiSubgroup (G := M) (section10SigmaPrimes M) p hp_dvd_K)
    have hp_dvd_quot : p.val ∣ Nat.card (M ⧸ D) :=
      hrdvd.trans (Subgroup.card_subgroup_dvd_card (K.map q))
    exact section10_sigma_not_dvd_quotient_derived hM hpσ (by simpa [D] using hp_dvd_quot)
  have hK_le_ker : K ≤ q.ker := (Subgroup.map_eq_bot_iff (H := K) (f := q)).mp hKmap_bot
  have hker_eq : q.ker = D := by
    simp [q]
  rwa [hker_eq] at hK_le_ker

omit [IsMinCE G] in
public theorem CFSG.section10_sylow_map_le_pCore_of_nilpotent_normal
    {H : Type*} [Group H] [Finite H]
    {N : Subgroup H} (hN : N.Normal) (hnil : Group.IsNilpotent N)
    (p : ℕ) [Fact p.Prime] (P : Sylow p N) :
    (P : Subgroup N).map N.subtype ≤ pCore p H := by
  have hP_normal : (P : Subgroup N).Normal :=
    Group.IsNilpotent.sylow_normal hnil p P
  have hP_char : (P : Subgroup N).Characteristic :=
    Sylow.characteristic_of_normal P hP_normal
  have hmap_normal : ((P : Subgroup N).map N.subtype).Normal := by
    infer_instance
  have hmap_p : IsPGroup p ((P : Subgroup N).map N.subtype) := by
    exact IsPGroup.map (p := p) (H := (P : Subgroup N)) P.isPGroup' N.subtype
  exact le_sSup
    (show (P : Subgroup N).map N.subtype ∈
        {K : Subgroup H | K.Normal ∧ IsPGroup p K} from
      ⟨hmap_normal, hmap_p⟩)

omit [IsMinCE G] in
public theorem CFSG.section10_pCore_quotient_piCore_eq_bot
    {H : Type*} [Group H] [Finite H] {π : Set Nat.Primes} {p : Nat.Primes}
    (hpπ : p ∈ π) :
    pCore p.val (H ⧸ piCore π H) = ⊥ := by
  classical
  have : Fact p.val.Prime := ⟨p.property⟩
  let K : Subgroup H := piCore π H
  let Q := H ⧸ K
  let q : H →* Q := QuotientGroup.mk' K
  let P : Subgroup Q := pCore p.val Q
  let N : Subgroup H := P.comap q
  have hK_le_N : K ≤ N := by
    intro x hx
    change q x ∈ P
    have hxq : q x = 1 := (QuotientGroup.eq_one_iff (N := K) x).2 hx
    simp [hxq]
  have hN_normal : N.Normal := by
    dsimp [N]
    infer_instance
  have hK_normal_in_N : (K.subgroupOf N).Normal :=
    Subgroup.Normal.subgroupOf (inferInstance : K.Normal) N
  let fN : N →* Q := q.comp N.subtype
  have hker : fN.ker = K.subgroupOf N := by
    ext x
    constructor
    · intro hx
      change q (x : H) = 1 at hx
      exact (QuotientGroup.eq_one_iff (N := K) (x : H)).1 hx
    · intro hx
      change q (x : H) = 1
      exact (QuotientGroup.eq_one_iff (N := K) (x : H)).2 hx
  have hrange : fN.range = P := by
    ext y
    constructor
    · intro hy
      rcases hy with ⟨x, rfl⟩
      exact x.property
    · intro hyP
      rcases QuotientGroup.mk'_surjective K y with ⟨x, rfl⟩
      exact ⟨⟨x, hyP⟩, rfl⟩
  have hP_pi_group : IsPiGroup π P := by
    rw [IsPiGroup_iff]
    intro r hr
    have hPp : IsPGroup p.val P := by
      simpa [P] using (pCore_isPGroup (p := p.val) (G := Q))
    rcases (IsPGroup.iff_card.mp hPp) with ⟨n, hcard⟩
    have hrp : r.val = p.val :=
      Nat.prime_eq_prime_of_dvd_pow r.property p.property (by simpa [hcard] using hr)
    have : r = p := Subtype.ext hrp
    simpa [this] using hpπ
  have hquot_pi : IsPiGroup π (N ⧸ K.subgroupOf N) := by
    let e0 : N ⧸ fN.ker ≃* fN.range := QuotientGroup.quotientKerEquivRange fN
    let e1 : N ⧸ K.subgroupOf N ≃* fN.range :=
      (QuotientGroup.quotientMulEquivOfEq hker.symm).trans e0
    let e2 : fN.range ≃* P := MulEquiv.subgroupCongr hrange
    exact IsPiGroup.of_equiv (π := π) (G := N ⧸ K.subgroupOf N) (H := P)
      hP_pi_group (e1.trans e2)
  have hK_pi_sub : IsPiSubgroup (G := N) π (K.subgroupOf N) := by
    intro r hr
    have hcard_eq : Nat.card (K.subgroupOf N) = Nat.card K := by
      simpa using Nat.card_congr
        (Subgroup.subgroupOfEquivOfLe (H := K) (K := N) hK_le_N).toEquiv
    exact (piCore_isPiSubgroup (G := H) π) r (by simpa [hcard_eq] using hr)
  have hN_pi_group : IsPiGroup π N :=
    IsPiGroup.of_normal_subgroup_and_quotient (π := π) (G := N)
      (K.subgroupOf N) hK_pi_sub hquot_pi
  have hN_pi : IsPiSubgroup (G := H) π N := by
    intro r hr
    exact (IsPiGroup_iff π N).1 hN_pi_group r hr
  have hN_le_K : N ≤ K := le_piCore_of_normal_isPiSubgroup (G := H) π N hN_pi
  apply le_antisymm
  · intro y hyP
    rcases QuotientGroup.mk'_surjective K y with ⟨x, rfl⟩
    have hxN : x ∈ N := by
      change q x ∈ P
      exact hyP
    exact (QuotientGroup.eq_one_iff (N := K) x).2 (hN_le_K hxN)
  · exact bot_le

omit [IsMinCE G] in
public theorem CFSG.section10_fitting_quotient_piCore_isPiSubgroup_compl
    {H : Type*} [Group H] [Finite H] {π : Set Nat.Primes} :
    IsPiSubgroup (G := H ⧸ piCore π H) πᶜ (fittingSubgroup (H ⧸ piCore π H)) := by
  classical
  intro p hp_dvd
  by_contra hp_not_compl
  have hpπ : p ∈ π := by
    simpa using hp_not_compl
  have : Fact p.val.Prime := ⟨p.property⟩
  let K : Subgroup H := piCore π H
  have : K.Normal := by
    dsimp [K]
    infer_instance
  let F : Subgroup (H ⧸ K) := fittingSubgroup (H ⧸ K)
  let P : Sylow p.val F := default
  have hp_dvd_P : p.val ∣ Nat.card (P : Subgroup F) :=
    Sylow.dvd_card_of_dvd_card P (by simpa [K, F] using hp_dvd)
  have hPmap_le : (P : Subgroup F).map F.subtype ≤ pCore p.val (H ⧸ K) :=
    section10_sylow_map_le_pCore_of_nilpotent_normal
      (H := H ⧸ K) (N := F) (by infer_instance)
      (by infer_instance) p.val P
  have hcore_bot : pCore p.val (H ⧸ K) = ⊥ := by
    simpa [K] using section10_pCore_quotient_piCore_eq_bot
      (H := H) (π := π) hpπ
  have hPmap_bot : (P : Subgroup F).map F.subtype = ⊥ := by
    apply le_antisymm
    · simpa [hcore_bot] using hPmap_le
    · exact bot_le
  have hcard_map :
      Nat.card ((P : Subgroup F).map F.subtype) = Nat.card (P : Subgroup F) := by
    simpa using
      (Subgroup.card_map_of_injective (K := (P : Subgroup F)) (f := F.subtype)
        F.subtype_injective)
  have hcard_P_one : Nat.card (P : Subgroup F) = 1 := by
    calc
      Nat.card (P : Subgroup F) = Nat.card ((P : Subgroup F).map F.subtype) := hcard_map.symm
      _ = Nat.card (⊥ : Subgroup (H ⧸ K)) := by rw [hPmap_bot]
      _ = 1 := by simp
  have hp_dvd_one : p.val ∣ 1 := by
    simpa [hcard_P_one] using hp_dvd_P
  exact p.property.not_dvd_one hp_dvd_one

omit [IsMinCE G] in
public theorem CFSG.section10_primeRank_quotient_piCore_le_of_not_mem
    {H : Type*} [Group H] [Finite H] {π : Set Nat.Primes} {p : Nat.Primes}
    (hpπ : p ∉ π) :
    primeRank p.val (H ⧸ piCore π H) ≤ primeRank p.val H := by
  classical
  have : Fact p.val.Prime := ⟨p.property⟩
  let N₀ : Subgroup H := piCore π H
  have : N₀.Normal := by
    dsimp [N₀]
    infer_instance
  let Q := H ⧸ N₀
  let T : Set ℕ :=
    {n : ℕ | ∃ A : Subgroup Q, IsPGroup p.val A ∧ IsMulCommutative A ∧
      n ≤ generatorRank A}
  have hTbdd : BddAbove T := by
    refine ⟨Nat.card Q, ?_⟩
    intro n hn
    rcases hn with ⟨A, _hAp, _hAcomm, hnA⟩
    exact hnA.trans <|
      (section10_generatorRank_le_natCard_pre A).trans (Subgroup.card_le_card_group A)
  by_cases hT : T.Nonempty
  · have hsSup_mem : sSup T ∈ T := Nat.sSup_mem hT hTbdd
    rcases hsSup_mem with ⟨A, hAp, hAcomm, hsSup_le⟩
    let q : H →* Q := QuotientGroup.mk' N₀
    let L : Subgroup H := A.comap q
    have hN₀_le_L : N₀ ≤ L := by
      intro x hx
      change q x ∈ A
      have hxq : q x = 1 := (QuotientGroup.eq_one_iff (N := N₀) x).2 hx
      simp [hxq]
    let N : Subgroup L := N₀.subgroupOf L
    have hN_normal : N.Normal :=
      Subgroup.Normal.subgroupOf (inferInstance : N₀.Normal) L
    let : N.Normal := hN_normal
    have hLmap : L.map q = A := by
      ext y
      constructor
      · intro hy
        rcases Subgroup.mem_map.mp hy with ⟨x, hxL, rfl⟩
        exact hxL
      · intro hyA
        rcases QuotientGroup.mk'_surjective N₀ y with ⟨x, rfl⟩
        exact ⟨x, hyA, rfl⟩
    let eLA : L ⧸ N ≃* A :=
      (quotientSubgroupRangeEquiv L N₀).trans (MulEquiv.subgroupCongr hLmap)
    have hquot_p : IsPGroup p.val (L ⧸ N) := hAp.of_equiv eLA.symm
    have hNπ : IsPiSubgroup (G := L) π N := by
      intro r hr
      have hcard_eq : Nat.card N = Nat.card N₀ := by
        simpa [N] using Nat.card_congr
          (Subgroup.subgroupOfEquivOfLe (H := N₀) (K := L) hN₀_le_L).toEquiv
      exact (piCore_isPiSubgroup (G := H) π) r (by simpa [N₀, hcard_eq] using hr)
    have hNcop_p : Nat.Coprime p.val (Nat.card N) := by
      refine (Nat.Prime.coprime_iff_not_dvd p.property).2 ?_
      intro hp_dvd_N
      exact hpπ (hNπ p hp_dvd_N)
    have hN_index_cop : Nat.Coprime (Nat.card N) N.index := by
      rcases (IsPGroup.iff_card.mp hquot_p) with ⟨m, hm⟩
      rw [Subgroup.index_eq_card, hm]
      exact hNcop_p.symm.pow_right m
    obtain ⟨C, hcompl⟩ := Subgroup.exists_right_complement'_of_coprime
      (N := N) hN_index_cop
    let qL : L →* L ⧸ N := QuotientGroup.mk' N
    let qC : C →* L ⧸ N := qL.comp C.subtype
    have hqC_inj : Function.Injective qC := by
      intro a b hab
      apply Subtype.ext
      change qL (a : L) = qL (b : L) at hab
      have habN : (a : L)⁻¹ * (b : L) ∈ N := QuotientGroup.eq.mp hab
      have habC : (a : L)⁻¹ * (b : L) ∈ C := C.mul_mem (C.inv_mem a.property) b.property
      have hab_one : (a : L)⁻¹ * (b : L) = 1 :=
        (Subgroup.disjoint_def.mp hcompl.disjoint) habN habC
      have := congrArg (fun t : L => (a : L) * t) hab_one
      simpa [mul_assoc] using this.symm
    have hqC_surj : Function.Surjective qC := by
      intro y
      refine QuotientGroup.induction_on y ?_
      intro x
      have hx_sup : x ∈ N ⊔ C := by
        simp [hcompl.sup_eq_top]
      rcases (Subgroup.mem_sup_of_normal_left (s := N) (t := C) (x := x)).1 hx_sup with
        ⟨n, hnN, c, hcC, hnc⟩
      refine ⟨⟨c, hcC⟩, ?_⟩
      change qL (c : L) = qL x
      have hn1 : qL n = 1 := (QuotientGroup.eq_one_iff (N := N) n).2 hnN
      calc
        qL (c : L) = qL n * qL c := by simp [hn1]
        _ = qL (n * c) := by simp [qL]
        _ = qL x := by simp [hnc]
    let eCLN : C ≃* L ⧸ N := MulEquiv.ofBijective qC ⟨hqC_inj, hqC_surj⟩
    let eCA : C ≃* A := eCLN.trans eLA
    let B : Subgroup H := C.map L.subtype
    let eCB : C ≃* B := Subgroup.equivMapOfInjective C L.subtype L.subtype_injective
    have hCp : IsPGroup p.val C := hAp.of_equiv eCA.symm
    have hBp : IsPGroup p.val B :=
      IsPGroup.map (p := p.val) (H := C) hCp L.subtype
    have hCcomm : IsMulCommutative C := by
      let : IsMulCommutative A := hAcomm
      refine ⟨⟨fun x y => ?_⟩⟩
      apply eCA.injective
      calc
        eCA (x * y) = eCA x * eCA y := map_mul eCA x y
        _ = eCA y * eCA x :=
          (IsMulCommutative.is_comm (M := A)).comm (eCA x) (eCA y)
        _ = eCA (y * x) := (map_mul eCA y x).symm
    have hBcomm : IsMulCommutative B := by
      let : IsMulCommutative C := hCcomm
      simpa [B] using Subgroup.map_isMulCommutative (f := L.subtype) (H := C)
    have hgen_le : generatorRank A ≤ generatorRank B := by
      let eAB : A ≃* B := eCA.symm.trans eCB
      rw [generatorRank_eq_group_rank, generatorRank_eq_group_rank]
      exact le_of_eq (Group.rank_congr eAB)
    have hmem : generatorRank A ∈
        {n : ℕ | ∃ B : Subgroup H, IsPGroup p.val B ∧ IsMulCommutative B ∧
          n ≤ generatorRank B} :=
      ⟨B, hBp, hBcomm, hgen_le⟩
    have hprimeRank : generatorRank A ≤ primeRank p.val H := by
      rw [primeRank]
      refine le_csSup ?_ hmem
      refine ⟨Nat.card H, ?_⟩
      intro n hn
      rcases hn with ⟨B, _hBp, _hBcomm, hnB⟩
      exact hnB.trans <|
        (section10_generatorRank_le_natCard_pre B).trans (Subgroup.card_le_card_group B)
    rw [primeRank]
    exact hsSup_le.trans hprimeRank
  · have hTempty : T = ∅ := Set.not_nonempty_iff_eq_empty.mp hT
    have hSet :
        {n : ℕ | ∃ A : Subgroup (H ⧸ piCore π H), IsPGroup p.val A ∧
          IsMulCommutative A ∧ n ≤ generatorRank A} = ∅ := by
      simpa [T, Q, N₀] using hTempty
    rw [primeRank, hSet]
    simp

omit [IsMinCE G] in
public theorem CFSG.section10_exists_pSubgroup_three_le_generatorRank_of_three_le_primeRank_pre
    {p : ℕ} {R : Type*} [Group R] [Finite R] (hrank : 3 ≤ primeRank p R) :
    ∃ A : Subgroup R, IsPGroup p A ∧ IsMulCommutative A ∧ 3 ≤ generatorRank A := by
  let T : Set ℕ :=
    {n : ℕ | ∃ A : Subgroup R, IsPGroup p A ∧ IsMulCommutative A ∧
      n ≤ generatorRank A}
  have hrank' : 2 < sSup T := by
    exact lt_of_lt_of_le (by decide : 2 < 3) (by simpa [primeRank, T] using hrank)
  have hTbdd : BddAbove T := by
    refine ⟨Nat.card R, ?_⟩
    intro n hn
    rcases hn with ⟨A, _hAp, _hAcomm, hnA⟩
    exact hnA.trans <|
      (section10_generatorRank_le_natCard_pre A).trans (Subgroup.card_le_card_group A)
  have hTnonempty : T.Nonempty := by
    by_contra hT
    have hTempty : T = ∅ := Set.not_nonempty_iff_eq_empty.mp hT
    have : ¬ 2 < sSup T := by
      simp [hTempty]
    exact this hrank'
  have htSup_mem : sSup T ∈ T := Nat.sSup_mem hTnonempty hTbdd
  rcases htSup_mem with ⟨A, hAp, hAcomm, htSup_le⟩
  exact ⟨A, hAp, hAcomm, Nat.succ_le_of_lt (lt_of_lt_of_le hrank' htSup_le)⟩

omit [IsMinCE G] in
public theorem CFSG.section10_prime_dvd_card_of_three_le_primeRank_pre
    {p : ℕ} [Fact p.Prime] {R : Type*} [Group R] [Finite R]
    (hrank : 3 ≤ primeRank p R) :
    p ∣ Nat.card R := by
  rcases section10_exists_pSubgroup_three_le_generatorRank_of_three_le_primeRank_pre
      (p := p) (R := R) hrank with
    ⟨A, hAp, _hAcomm, hAgen⟩
  have hAnoncyc : ¬ IsCyclic A := by
    intro hcyc
    have hle : generatorRank A ≤ 1 := generatorRank_le_one_of_isCyclic (G := A) hcyc
    omega
  have hAnontrivial : Nontrivial A := by
    by_contra hnt
    let : Subsingleton A := not_nontrivial_iff_subsingleton.mp hnt
    exact hAnoncyc (isCyclic_of_subsingleton (α := A))
  obtain ⟨n, hn_pos, hAcard⟩ :=
    (IsPGroup.nontrivial_iff_card (p := p) (G := A) (hG := hAp)).mp hAnontrivial
  obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hn_pos)
  have hp_dvd_A : p ∣ Nat.card A := by
    rw [hAcard, pow_succ']
    exact dvd_mul_right p (p ^ m)
  exact hp_dvd_A.trans (Subgroup.card_subgroup_dvd_card A)

omit [IsMinCE G] in
public theorem CFSG.section10_fitting_quotient_malpha_groupRank_le_two
    {M : Subgroup G} (_hM : M ∈ section9MaximalSubgroups G) :
    groupRank (fittingSubgroup (M ⧸ section10MalphaSubgroup M)) ≤ 2 := by
  classical
  let π : Set Nat.Primes := section10AlphaPrimes M
  let Q := M ⧸ section10MalphaSubgroup M
  let F : Subgroup Q := fittingSubgroup Q
  have hFπc : IsPiSubgroup (G := Q) πᶜ F := by
    change IsPiSubgroup
      (G := M ⧸ piCore (section10AlphaPrimes M) M)
      (section10AlphaPrimes M)ᶜ
      (fittingSubgroup (M ⧸ piCore (section10AlphaPrimes M) M))
    exact section10_fitting_quotient_piCore_isPiSubgroup_compl
      (H := M) (π := section10AlphaPrimes M)
  rw [groupRank]
  refine csSup_le ?_ ?_
  · exact ⟨0, 2, Nat.prime_two, Nat.zero_le _⟩
  · intro n hn
    rcases hn with ⟨q, hqprime, hnq⟩
    by_cases hn_le_two : n ≤ 2
    · exact hn_le_two
    have hthree_n : 3 ≤ n := by omega
    let p : Nat.Primes := ⟨q, hqprime⟩
    have : Fact p.val.Prime := ⟨p.property⟩
    have hthree_rank_F : 3 ≤ primeRank p.val F := hthree_n.trans hnq
    have hp_dvd_F : p.val ∣ Nat.card F :=
      section10_prime_dvd_card_of_three_le_primeRank_pre
        (p := p.val) (R := F) hthree_rank_F
    have hp_not_alpha : p ∉ π := by
      have hp_compl : p ∈ πᶜ := hFπc p hp_dvd_F
      simpa using hp_compl
    have hprankF_le_Q : primeRank p.val F ≤ primeRank p.val Q := by
      simpa [Q, F, p] using section8_primeRank_le_of_subgroup (G := Q) F p.val
    have hprankQ_le_M : primeRank p.val Q ≤ primeRank p.val M := by
      change primeRank p.val (M ⧸ piCore (section10AlphaPrimes M) M) ≤
        primeRank p.val M
      exact section10_primeRank_quotient_piCore_le_of_not_mem
        (H := M) (π := section10AlphaPrimes M) (p := p) (by
          simpa [π] using hp_not_alpha)
    have hp_dvd_M : p.val ∣ Nat.card M := by
      exact (hp_dvd_F.trans (Subgroup.card_subgroup_dvd_card F)).trans
        (Subgroup.card_quotient_dvd_card (s := section10MalphaSubgroup M))
    have hprankM_le_two : primeRank p.val M ≤ 2 := by
      by_contra hnot
      have hgt : 2 < primeRank p.val M := Nat.lt_of_not_ge hnot
      exact hp_not_alpha (by simpa [π, section10AlphaPrimes, subgroupPrimeSet] using
        (show p ∈ section10AlphaPrimes M from ⟨hp_dvd_M, hgt⟩))
    exact hnq.trans (hprankF_le_Q.trans (hprankQ_le_M.trans hprankM_le_two))

omit [Finite G] [IsMinCE G] in
public theorem CFSG.section10_card_derivedSubgroup_quotient_malpha_eq
    {M : Subgroup G} :
    Nat.card (derivedSubgroup M ⧸
        (section10MalphaSubgroup M).subgroupOf (derivedSubgroup M)) =
      Nat.card (derivedSubgroup (M ⧸ section10MalphaSubgroup M)) := by
  classical
  let K : Subgroup M := section10MalphaSubgroup M
  let D : Subgroup M := derivedSubgroup M
  have hKnormalD : (K.subgroupOf D).Normal :=
    (inferInstance : K.Normal).subgroupOf D
  let Q := M ⧸ K
  let q : M →* Q := QuotientGroup.mk' K
  let φ : D →* Q := q.comp D.subtype
  have hφker : φ.ker = K.subgroupOf D := by
    ext x
    constructor
    · intro hx
      have hx1 : φ x = 1 := by
        simpa [MonoidHom.mem_ker] using hx
      have hx1' : ((x : M) : M ⧸ K) = 1 := by
        change q (x : M) = 1 at hx1
        exact hx1
      have hxK : (x : M) ∈ K :=
        (QuotientGroup.eq_one_iff (N := K) (x := (x : M))).1 hx1'
      change (x : M) ∈ K
      exact hxK
    · intro hx
      have hxK : (x : M) ∈ K := by
        change (x : M) ∈ K at hx
        exact hx
      have hx1 : ((x : M) : M ⧸ K) = 1 :=
        (QuotientGroup.eq_one_iff (N := K) (x := (x : M))).2 hxK
      rw [MonoidHom.mem_ker]
      change q (x : M) = 1
      exact hx1
  have hφrange : φ.range = derivedSubgroup Q := by
    have hrange_map : φ.range = D.map q := by
      ext y
      constructor
      · intro hy
        rcases hy with ⟨x, rfl⟩
        exact Subgroup.mem_map_of_mem q x.property
      · intro hy
        rcases Subgroup.mem_map.mp hy with ⟨x, hxD, rfl⟩
        exact ⟨⟨x, hxD⟩, rfl⟩
    have hDmap : D.map q = derivedSubgroup Q := by
      have hmap :
          (derivedSeries M 1).map q = derivedSeries Q 1 := by
        simpa [Q, q] using
          (map_derivedSeries_eq (f := q) (QuotientGroup.mk'_surjective K) 1)
      simpa [D, derivedSubgroup] using hmap
    exact hrange_map.trans hDmap
  let e : D ⧸ K.subgroupOf D ≃* derivedSubgroup Q :=
    ((QuotientGroup.quotientMulEquivOfEq hφker.symm).trans
      (QuotientGroup.quotientKerEquivRange φ)).trans
      (MulEquiv.subgroupCongr hφrange)
  simpa [D, K, Q] using Nat.card_congr e.toEquiv

omit [Finite G] [IsMinCE G] in
public theorem CFSG.section10_card_derivedSubgroup_quotient_eq
    {H : Type*} [Group H] [Finite H] (K : Subgroup H) [K.Normal] :
    Nat.card (derivedSubgroup H ⧸ K.subgroupOf (derivedSubgroup H)) =
      Nat.card (derivedSubgroup (H ⧸ K)) := by
  classical
  let D : Subgroup H := derivedSubgroup H
  have hKnormalD : (K.subgroupOf D).Normal :=
    (inferInstance : K.Normal).subgroupOf D
  let Q := H ⧸ K
  let q : H →* Q := QuotientGroup.mk' K
  let φ : D →* Q := q.comp D.subtype
  have hφker : φ.ker = K.subgroupOf D := by
    ext x
    constructor
    · intro hx
      have hx1 : φ x = 1 := by
        simpa [MonoidHom.mem_ker] using hx
      have hx1' : ((x : H) : H ⧸ K) = 1 := by
        change q (x : H) = 1 at hx1
        exact hx1
      have hxK : (x : H) ∈ K :=
        (QuotientGroup.eq_one_iff (N := K) (x := (x : H))).1 hx1'
      change (x : H) ∈ K
      exact hxK
    · intro hx
      have hxK : (x : H) ∈ K := by
        change (x : H) ∈ K at hx
        exact hx
      have hx1 : ((x : H) : H ⧸ K) = 1 :=
        (QuotientGroup.eq_one_iff (N := K) (x := (x : H))).2 hxK
      rw [MonoidHom.mem_ker]
      change q (x : H) = 1
      exact hx1
  have hφrange : φ.range = derivedSubgroup Q := by
    have hrange_map : φ.range = D.map q := by
      ext y
      constructor
      · intro hy
        rcases hy with ⟨x, rfl⟩
        exact Subgroup.mem_map_of_mem q x.property
      · intro hy
        rcases Subgroup.mem_map.mp hy with ⟨x, hxD, rfl⟩
        exact ⟨⟨x, hxD⟩, rfl⟩
    have hDmap : D.map q = derivedSubgroup Q := by
      have hmap :
          (derivedSeries H 1).map q = derivedSeries Q 1 := by
        simpa [Q, q] using
          (map_derivedSeries_eq (f := q) (QuotientGroup.mk'_surjective K) 1)
      simpa [D, derivedSubgroup] using hmap
    exact hrange_map.trans hDmap
  let e : D ⧸ K.subgroupOf D ≃* derivedSubgroup Q :=
    ((QuotientGroup.quotientMulEquivOfEq hφker.symm).trans
      (QuotientGroup.quotientKerEquivRange φ)).trans
      (MulEquiv.subgroupCongr hφrange)
  simpa [D, Q] using Nat.card_congr e.toEquiv

public theorem CFSG.section10_derivedSubgroup_quotient_malpha_nilpotent
    {M : Subgroup G} (hM : M ∈ section9MaximalSubgroups G) :
    section10QuotientNilpotent (derivedSubgroup M) (section10MalphaSubgroup M) := by
  classical
  let K : Subgroup M := section10MalphaSubgroup M
  let D : Subgroup M := derivedSubgroup M
  have hKD : K ≤ D := by
    exact (section10_malphaSubgroup_le_msigmaSubgroup hM).trans
      (section10_msigmaSubgroup_le_derivedSubgroup hM)
  have hKnormalD : (K.subgroupOf D).Normal :=
    (inferInstance : K.Normal).subgroupOf D
  let Q := M ⧸ K
  have hMsolv : Group.IsSolvable M :=
    IsMinCE.proper_subgroups_solvable M (lt_top_iff_ne_top.2 hM.1)
  have hQsolv : Group.IsSolvable Q := by
    let : Group.IsSolvable M := hMsolv
    dsimp [Q]
    infer_instance
  have hModd : Odd (Nat.card M) :=
    odd_of_card_dvd IsMinCE.odd_order (Subgroup.card_subgroup_dvd_card M)
  have hQodd : Odd (Nat.card Q) :=
    hModd.of_dvd_nat (Subgroup.card_quotient_dvd_card (s := K))
  have hF_rank : groupRank (fittingSubgroup Q) ≤ 2 := by
    simpa [Q, K] using section10_fitting_quotient_malpha_groupRank_le_two hM
  have hDerQ_nil : Group.IsNilpotent (derivedSubgroup Q) :=
    theorem_4_20_a (G := Q) hQsolv hQodd (Or.inr hF_rank)
  let q : M →* Q := QuotientGroup.mk' K
  let φ : D →* Q := q.comp D.subtype
  have hφker : φ.ker = K.subgroupOf D := by
    ext x
    constructor
    · intro hx
      have hx1 : φ x = 1 := by
        simpa [MonoidHom.mem_ker] using hx
      have hx1' : ((x : M) : M ⧸ K) = 1 := by
        change q (x : M) = 1 at hx1
        exact hx1
      have hxK : (x : M) ∈ K :=
        (QuotientGroup.eq_one_iff (N := K) (x := (x : M))).1 hx1'
      change (x : M) ∈ K
      exact hxK
    · intro hx
      have hxK : (x : M) ∈ K := by
        change (x : M) ∈ K at hx
        exact hx
      have hx1 : ((x : M) : M ⧸ K) = 1 :=
        (QuotientGroup.eq_one_iff (N := K) (x := (x : M))).2 hxK
      rw [MonoidHom.mem_ker]
      change q (x : M) = 1
      exact hx1
  have hφrange : φ.range = derivedSubgroup Q := by
    have hrange_map : φ.range = D.map q := by
      ext y
      constructor
      · intro hy
        rcases hy with ⟨x, rfl⟩
        exact Subgroup.mem_map_of_mem q x.property
      · intro hy
        rcases Subgroup.mem_map.mp hy with ⟨x, hxD, rfl⟩
        exact ⟨⟨x, hxD⟩, rfl⟩
    have hDmap : D.map q = derivedSubgroup Q := by
      have hmap :
          (derivedSeries M 1).map q = derivedSeries Q 1 := by
        simpa [Q, q] using
          (map_derivedSeries_eq (f := q) (QuotientGroup.mk'_surjective K) 1)
      simpa [D, derivedSubgroup] using hmap
    exact hrange_map.trans hDmap
  have hφrange_nil : Group.IsNilpotent φ.range := by
    rw [hφrange]
    exact hDerQ_nil
  have hquot_ker_nil : Group.IsNilpotent (D ⧸ φ.ker) := by
    let : Group.IsNilpotent φ.range := hφrange_nil
    exact Group.nilpotent_of_mulEquiv
      (G := φ.range) (G' := D ⧸ φ.ker) (QuotientGroup.quotientKerEquivRange φ).symm
  have hquot_nil : Group.IsNilpotent (D ⧸ K.subgroupOf D) := by
    let e : D ⧸ K.subgroupOf D ≃* D ⧸ φ.ker :=
      QuotientGroup.quotientMulEquivOfEq hφker.symm
    let : Group.IsNilpotent (D ⧸ φ.ker) := hquot_ker_nil
    exact Group.nilpotent_of_mulEquiv (G := D ⧸ φ.ker) (G' := D ⧸ K.subgroupOf D) e.symm
  exact ⟨hKD, hKnormalD, by simpa [D, K] using hquot_nil⟩

public theorem CFSG.section10_prime_not_dvd_derived_quotient_malpha_of_mem_alpha
    {M : Subgroup G} (hM : M ∈ section9MaximalSubgroups G) {p : Nat.Primes}
    (hpα : p ∈ section10AlphaPrimes M) :
    ¬ p.val ∣ Nat.card (derivedSubgroup M ⧸
      (section10MalphaSubgroup M).subgroupOf (derivedSubgroup M)) := by
  classical
  intro hp_dvd
  let π : Set Nat.Primes := section10AlphaPrimes M
  let K : Subgroup M := section10MalphaSubgroup M
  let Q := M ⧸ K
  have hMsolv : Group.IsSolvable M :=
    IsMinCE.proper_subgroups_solvable M (lt_top_iff_ne_top.2 hM.1)
  have hQsolv : Group.IsSolvable Q := by
    let : Group.IsSolvable M := hMsolv
    dsimp [Q]
    infer_instance
  have hModd : Odd (Nat.card M) :=
    odd_of_card_dvd IsMinCE.odd_order (Subgroup.card_subgroup_dvd_card M)
  have hQodd : Odd (Nat.card Q) :=
    hModd.of_dvd_nat (Subgroup.card_quotient_dvd_card (s := K))
  have hF_rank : groupRank (fittingSubgroup Q) ≤ 2 := by
    simpa [Q, K] using section10_fitting_quotient_malpha_groupRank_le_two hM
  have hDerQ_nil : Group.IsNilpotent (derivedSubgroup Q) :=
    theorem_4_20_a (G := Q) hQsolv hQodd (Or.inr hF_rank)
  have hDerQ_le_F : derivedSubgroup Q ≤ fittingSubgroup Q :=
    le_sSup ⟨inferInstance, hDerQ_nil⟩
  have hcard_eq :
      Nat.card (derivedSubgroup M ⧸ K.subgroupOf (derivedSubgroup M)) =
        Nat.card (derivedSubgroup Q) := by
    simpa [Q, K] using section10_card_derivedSubgroup_quotient_malpha_eq (M := M)
  have hp_dvd_derQ : p.val ∣ Nat.card (derivedSubgroup Q) := by
    rw [← hcard_eq]
    simpa [K] using hp_dvd
  have hp_dvd_F : p.val ∣ Nat.card (fittingSubgroup Q) :=
    hp_dvd_derQ.trans (Subgroup.card_dvd_of_le hDerQ_le_F)
  have hFπc :
      IsPiSubgroup (G := Q) πᶜ (fittingSubgroup Q) := by
    change IsPiSubgroup
      (G := M ⧸ piCore (section10AlphaPrimes M) M)
      (section10AlphaPrimes M)ᶜ
      (fittingSubgroup (M ⧸ piCore (section10AlphaPrimes M) M))
    exact section10_fitting_quotient_piCore_isPiSubgroup_compl
      (H := M) (π := section10AlphaPrimes M)
  exact (hFπc p hp_dvd_F) hpα

public theorem CFSG.section10_malphaSubgroup_isHall
    {M : Subgroup G} (hM : M ∈ section9MaximalSubgroups G) :
    IsHallSubgroup (section10AlphaPrimes M) (section10MalphaSubgroup M) := by
  classical
  let π : Set Nat.Primes := section10AlphaPrimes M
  let K : Subgroup M := section10MalphaSubgroup M
  refine isHallSubgroup_of (G := M) (π := π) (H := K) ?_ ?_
  · intro p hp_dvd
    simpa [K, π, section10MalphaSubgroup] using
      (piCore_isPiSubgroup (G := M) π p hp_dvd)
  · intro p hpα hp_dvd_index
    let D : Subgroup M := derivedSubgroup M
    have hKD : K ≤ D := by
      exact (section10_malphaSubgroup_le_msigmaSubgroup hM).trans
        (section10_msigmaSubgroup_le_derivedSubgroup hM)
    have hidx_mul : K.relIndex D * D.index = K.index :=
      Subgroup.relIndex_mul_index hKD
    have hp_dvd_prod : p.val ∣ K.relIndex D * D.index := by
      simpa [hidx_mul] using hp_dvd_index
    rcases p.property.dvd_or_dvd hp_dvd_prod with hp_rel | hp_Didx
    · have hrel_eq : K.relIndex D = (K.subgroupOf D).index := by
        calc
          K.relIndex D =
              (K.subgroupOf D).relIndex (D.subgroupOf D) :=
            (Subgroup.relIndex_subgroupOf
              (H := K) (K := D) (L := D) (hKL := le_rfl)).symm
          _ = (K.subgroupOf D).relIndex ⊤ := by rw [Subgroup.subgroupOf_self]
          _ = (K.subgroupOf D).index :=
            Subgroup.relIndex_top_right (H := K.subgroupOf D)
      exact section10_prime_not_dvd_derived_quotient_malpha_of_mem_alpha hM
        (by simpa [π] using hpα) (by
          change p.val ∣ Nat.card (D ⧸ K.subgroupOf D)
          rw [← (K.subgroupOf D).index_eq_card, ← hrel_eq]
          exact hp_rel)
    · exact (section10_sigma_not_dvd_quotient_derived hM
        (section10_alpha_subset_sigma hM (by simpa [π] using hpα))) (by
          simpa [D, Subgroup.index_eq_card] using hp_Didx)

public theorem CFSG.section10_prime_not_dvd_maximal_index_of_mem_alpha
    {M : Subgroup G} (hM : M ∈ section9MaximalSubgroups G) {p : Nat.Primes}
    (hpα : p ∈ section10AlphaPrimes M) :
    ¬ p.val ∣ M.index := by
  classical
  have : Fact p.val.Prime := ⟨p.property⟩
  intro hp_dvd_index
  let P : Sylow p.val M := Classical.choice (Sylow.nonempty (p := p.val) (G := M))
  let PG : Subgroup G := section10AmbientSylowSubgroup M P
  have hpσ : p ∈ section10SigmaPrimes M := section10_alpha_subset_sigma hM hpα
  have hPGp : IsPGroup p.val PG := by
    change IsPGroup p.val ((P : Subgroup M).map M.subtype)
    simpa using
      (IsPGroup.map (p := p.val) (H := (P : Subgroup M)) P.isPGroup' M.subtype)
  obtain ⟨S, hPGS⟩ := IsPGroup.exists_le_sylow (G := G) (p := p.val) hPGp
  have hS_eq_PG : (S : Subgroup G) = PG := by
    simpa [PG] using section10_sigma_ambient_sylow_eq_of_le_sylow hpσ P S hPGS
  have hPG_not_dvd_index : ¬ p.val ∣ PG.index := by
    simpa [hS_eq_PG] using S.not_dvd_index
  have hPG_index : PG.index = (P : Subgroup M).index * M.index := by
    simpa [PG, section10AmbientSylowSubgroup] using
      (Subgroup.index_map_subtype (H := M) (K := (P : Subgroup M)))
  exact hPG_not_dvd_index (by
    rw [hPG_index]
    exact dvd_mul_of_dvd_right hp_dvd_index (P : Subgroup M).index)

public theorem CFSG.section10_malpha_isHall
    {M : Subgroup G} (hM : M ∈ section9MaximalSubgroups G) :
    IsHallSubgroup (section10AlphaPrimes M) (section10Malpha M) := by
  classical
  let π : Set Nat.Primes := section10AlphaPrimes M
  let K : Subgroup M := section10MalphaSubgroup M
  have hKHall : IsHallSubgroup π K := section10_malphaSubgroup_isHall hM
  refine isHallSubgroup_of (G := G) (π := π) (H := section10Malpha M) ?_ ?_
  · intro p hp_dvd
    have hcard_eq : Nat.card (section10Malpha M) = Nat.card K := by
      simpa [section10Malpha, K] using
        (Subgroup.card_map_of_injective (K := K) (f := M.subtype) M.subtype_injective)
    exact hKHall.p_in_pi_of_p_dvd_card p (by simpa [hcard_eq] using hp_dvd)
  · intro p hpα hp_dvd_index
    have hidx : (section10Malpha M).index = K.index * M.index := by
      simpa [section10Malpha, K] using
        (Subgroup.index_map_subtype (H := M) (K := K))
    have hp_dvd_prod : p.val ∣ K.index * M.index := by
      simpa [hidx] using hp_dvd_index
    rcases p.property.dvd_or_dvd hp_dvd_prod with hpK | hpM
    · exact (hKHall.p_in_pi_of_p_dvd_index p hpK) hpα
    · exact section10_prime_not_dvd_maximal_index_of_mem_alpha hM
        (by simpa [π] using hpα) hpM

/-- Theorem 10.2(a). -/
public theorem CFSG.theorem_10_2_a
    {M : Subgroup G} (hM : M ∈ section9MaximalSubgroups G) :
    IsHallSubgroup (section10AlphaPrimes M) (section10Malpha M) ∧
      IsHallSubgroup (section10AlphaPrimes M) (section10MalphaSubgroup M) := by
  exact ⟨section10_malpha_isHall hM, section10_malphaSubgroup_isHall hM⟩

end Section10
