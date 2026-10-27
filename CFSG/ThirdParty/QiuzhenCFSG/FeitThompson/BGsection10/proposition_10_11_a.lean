module

public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.BGsection10.proposition_10_10_c
import Mathlib.GroupTheory.Schreier
import Mathlib.LinearAlgebra.Projectivization.Cardinality

namespace CFSG
end CFSG
open CFSG

open scoped Pointwise

/-!
# Statements from BG Section 10

This file records a statement-only scaffold for Section 10 of
`Local Analysis for the Odd Order Theorem`.

The local PDF extraction mangles the Greek letters used in the book. This
module imports the shared Section 10 notation from `FeitThompson.BGsection10.Defs`.
-/

section Section10

variable {G : Type*} [Group G] [Finite G] [IsMinCE G]

private theorem CFSG.section10_bot_not_unique
    {M : Subgroup G} (hM : M ∈ section9MaximalSubgroups G) :
    (⊥ : Subgroup G) ∉ section9UniqueSubgroups G := by
  classical
  obtain ⟨x, hxM⟩ : ∃ x : G, x ∉ M := by
    by_contra h
    have htop_le_M : (⊤ : Subgroup G) ≤ M := by
      intro x _hx
      by_contra hx
      exact (not_exists.mp h x) hx
    exact hM.1 (top_le_iff.mp htop_le_M)
  have hzx_proper : Subgroup.zpowers x ≠ (⊤ : Subgroup G) := by
    intro htop
    exact section10_not_isCyclic_min_ce
      ((isCyclic_iff_exists_zpowers_eq_top (α := G)).2 ⟨x, htop⟩)
  obtain ⟨H, hHcont⟩ :=
    section10_exists_maximalSubgroupsContaining_of_ne_top (G := G) hzx_proper
  have hH : H ∈ section9MaximalSubgroups G := hHcont.1
  have hz_le_H : Subgroup.zpowers x ≤ H := hHcont.2
  have hHM : H ≠ M := by
    intro hHM
    exact hxM (by simpa [hHM] using hz_le_H (Subgroup.mem_zpowers x))
  exact
    section10_not_unique_of_le_two_distinct_maximal
      (G := G) hM hH bot_le bot_le hHM

private theorem CFSG.section10_exists_hall_compl_sigma_containing
    {M K : Subgroup G} (hM : M ∈ section9MaximalSubgroups G) (hKle : K ≤ M)
    (hKσ : IsPiSubgroup (section10SigmaPrimes M)ᶜ K) :
    ∃ E : Subgroup M, IsHallSubgroup (section10SigmaPrimes M)ᶜ E ∧
      K.subgroupOf M ≤ E := by
  classical
  let Ksub : Subgroup M := K.subgroupOf M
  let : MulDistribMulAction PUnit.{1} M := {
    smul := fun _ x => x
    one_smul := by intro x; rfl
    mul_smul := by intro a b x; rfl
    smul_mul := by intro a x y; rfl
    smul_one := by intro a; rfl }
  have hMsolv : Group.IsSolvable M :=
    IsMinCE.proper_subgroups_solvable M (lt_top_iff_ne_top.2 hM.1)
  have hKsubσ : IsPiSubgroup (G := M) (section10SigmaPrimes M)ᶜ Ksub := by
    intro p hp
    have hcard : Nat.card Ksub = Nat.card K :=
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe (H := K) (K := M) hKle).toEquiv
    exact hKσ p (by rwa [hcard] at hp)
  have hKsub_inv : IsInvariant PUnit.{1} M Ksub := by
    refine ⟨?_⟩
    intro a x
    simp
  obtain ⟨E, hEHall, _hEinv, hKsubE⟩ :=
    exists_isHallSubgroup_isInvariant_of_isPiSubgroup
      (G := M) (A := PUnit.{1}) hMsolv (by simp) (section10SigmaPrimes M)ᶜ
      Ksub hKsubσ hKsub_inv
  exact ⟨E, hEHall, hKsubE⟩

public theorem CFSG.section10_hall_compl_sigma_groupRank_le_two
    {M : Subgroup G} (hM : M ∈ section9MaximalSubgroups G) {E : Subgroup M}
    (hEHall : IsHallSubgroup (section10SigmaPrimes M)ᶜ E) :
    groupRank E ≤ 2 := by
  classical
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
    have hthree_rank_E : 3 ≤ primeRank p.val E := hthree_n.trans hnq
    have hp_dvd_E : p.val ∣ Nat.card E :=
      section10_prime_dvd_card_of_three_le_primeRank_pre
        (p := p.val) (R := E) hthree_rank_E
    have hp_not_sigma : p ∉ section10SigmaPrimes M := by
      have hp_compl : p ∈ (section10SigmaPrimes M)ᶜ :=
        hEHall.p_in_pi_of_p_dvd_card p hp_dvd_E
      simpa using hp_compl
    have hrankE_le_M : primeRank p.val E ≤ primeRank p.val M := by
      simpa [p] using section8_primeRank_le_of_subgroup (G := M) E p.val
    have hp_dvd_M : p.val ∣ Nat.card M :=
      hp_dvd_E.trans (Subgroup.card_subgroup_dvd_card E)
    have hrankM_le_two : primeRank p.val M ≤ 2 := by
      by_contra hnot
      have hgt : 2 < primeRank p.val M := Nat.lt_of_not_ge hnot
      have hpα : p ∈ section10AlphaPrimes M := by
        simpa [section10AlphaPrimes, subgroupPrimeSet] using
          (show p ∈ section10AlphaPrimes M from ⟨hp_dvd_M, hgt⟩)
      exact hp_not_sigma (section10_alpha_subset_sigma hM hpα)
    exact hnq.trans (hrankE_le_M.trans hrankM_le_two)

omit [IsMinCE G] in
private theorem CFSG.section10_hall_compl_sylow_map_to_maximal_sylow
    {M : Subgroup G} {E : Subgroup M}
    (hEHall : IsHallSubgroup (section10SigmaPrimes M)ᶜ E)
    {p : Nat.Primes} (hpσ : p ∉ section10SigmaPrimes M) (P : Sylow p.val E) :
    ∃ PM : Sylow p.val M, (PM : Subgroup M) = (P : Subgroup E).map E.subtype := by
  classical
  have : Fact p.val.Prime := ⟨p.property⟩
  let Psub : Subgroup M := (P : Subgroup E).map E.subtype
  have hPsubp : IsPGroup p.val Psub :=
    IsPGroup.map (p := p.val) (H := (P : Subgroup E)) P.isPGroup' E.subtype
  have hnot_index : ¬ p.val ∣ Psub.index := by
    intro hpidx
    have hidx : Psub.index = (P : Subgroup E).index * E.index := by
      simpa [Psub] using
        (Subgroup.index_map_subtype (H := E) (K := (P : Subgroup E)))
    have hp_prod : p.val ∣ (P : Subgroup E).index * E.index := by
      simpa [hidx] using hpidx
    rcases p.property.dvd_or_dvd hp_prod with hpPidx | hpEidx
    · exact P.not_dvd_index hpPidx
    · exact (hEHall.p_in_pi_of_p_dvd_index p hpEidx) (by simpa using hpσ)
  let PM : Sylow p.val M := hPsubp.toSylow hnot_index
  exact ⟨PM, by simp [PM, Psub, IsPGroup.toSylow_coe]⟩

omit [Finite G] [IsMinCE G] in
private theorem CFSG.section10_map_subtype_le_normalizer_of_normal
    {H : Type*} [Group H] (K : Subgroup H) (L : Subgroup K) [L.Normal] :
    K ≤ Subgroup.normalizer (L.map K.subtype : Set H) := by
  intro k hk
  rw [Subgroup.mem_normalizer_iff]
  intro x
  constructor
  · intro hx
    rcases hx with ⟨l, hlL, rfl⟩
    exact Subgroup.mem_map_of_mem K.subtype
      (Subgroup.Normal.conj_mem inferInstance l hlL ⟨k, hk⟩)
  · intro hx
    rcases hx with ⟨l, hlL, hlx⟩
    refine ⟨(⟨k, hk⟩ : K)⁻¹ * l * ⟨k, hk⟩, ?_, ?_⟩
    · simpa using Subgroup.Normal.conj_mem inferInstance l hlL ((⟨k, hk⟩ : K)⁻¹)
    · calc
        (((⟨k, hk⟩ : K)⁻¹ * l * ⟨k, hk⟩ : K) : H) =
            k⁻¹ * ((l : K) : H) * k := by rfl
        _ = k⁻¹ * (k * x * k⁻¹) * k := by
          have hlx' : (l : H) = k * x * k⁻¹ := hlx
          rw [hlx']
        _ = x := by simp [mul_assoc]

omit [Finite G] [IsMinCE G] in
private theorem CFSG.section10_map_subtype_le_normalizer_map_of_le_normalizer
    {H : Subgroup G} {K L : Subgroup H}
    (hL_normK : L ≤ Subgroup.normalizer (K : Set H)) :
    L.map H.subtype ≤ Subgroup.normalizer ((K.map H.subtype : Subgroup G) : Set G) := by
  let : Subgroup.Normalizes L K := ⟨hL_normK⟩
  intro a ha
  rw [Subgroup.mem_normalizer_iff]
  intro x
  constructor
  · intro hx
    rcases Subgroup.mem_map.mp ha with ⟨b, hb, rfl⟩
    rcases Subgroup.mem_map.mp hx with ⟨k, hk, rfl⟩
    let kK : K := ⟨k, hk⟩
    have hkmap :
        H.subtype ((((⟨b, hb⟩ : L) • kK : K) : H)) ∈ K.map H.subtype :=
      Subgroup.mem_map_of_mem H.subtype (((⟨b, hb⟩ : L) • kK).2)
    simpa only [kK, Subgroup.conjMulDistribMulActionOfLeNormalizer_smul_coe, hL_normK,
      map_mul, map_inv] using hkmap
  · intro hx
    rcases Subgroup.mem_map.mp ha with ⟨b, hb, rfl⟩
    have hb_inv : b⁻¹ ∈ L := L.inv_mem hb
    rcases Subgroup.mem_map.mp hx with ⟨k, hk, hkx⟩
    let kK : K := ⟨k, hk⟩
    have hkmap :
        H.subtype ((((⟨b⁻¹, hb_inv⟩ : L) • kK : K) : H)) ∈ K.map H.subtype :=
      Subgroup.mem_map_of_mem H.subtype (((⟨b⁻¹, hb_inv⟩ : L) • kK).2)
    have hkx' :
        H.subtype ((((⟨b⁻¹, hb_inv⟩ : L) • kK : K) : H)) = x := by
      calc
        H.subtype ((((⟨b⁻¹, hb_inv⟩ : L) • kK : K) : H)) =
            (b : G)⁻¹ * (k : H) * (b : G) := by
          simp [kK, Subgroup.conjMulDistribMulActionOfLeNormalizer_smul_coe, mul_assoc]
        _ = (b : G)⁻¹ * ((b : G) * x * (b : G)⁻¹) * (b : G) := by
          simpa using congrArg (fun z : G => (b : G)⁻¹ * z * (b : G)) hkx
        _ = x := by simp [mul_assoc]
    exact hkx' ▸ hkmap

omit [Finite G] [IsMinCE G] in
private theorem CFSG.section10_hall_compl_normal_sylow_le_ambient_normalizer
    {M : Subgroup G} {E : Subgroup M} {p : Nat.Primes} (P : Sylow p.val E)
    (hPnormal : (P : Subgroup E).Normal) :
    E.map M.subtype ≤
      Subgroup.normalizer
        ((((P : Subgroup E).map E.subtype : Subgroup M).map M.subtype : Subgroup G) : Set G) := by
  classical
  let PsubM : Subgroup M := (P : Subgroup E).map E.subtype
  have hE_le_norm : E ≤ Subgroup.normalizer (PsubM : Set M) := by
    let : (P : Subgroup E).Normal := hPnormal
    simpa [PsubM] using
      section10_map_subtype_le_normalizer_of_normal E (P : Subgroup E)
  simpa [PsubM] using
    section10_map_subtype_le_normalizer_map_of_le_normalizer
      (G := G) (H := M) (K := PsubM) (L := E) hE_le_norm

/-- Proposition 10.11(a). -/
public theorem CFSG.proposition_10_11_a
    {M K : Subgroup G} (hM : M ∈ section9MaximalSubgroups G) (hKle : K ≤ M)
    (hKσ : IsPiSubgroup (section10SigmaPrimes M)ᶜ K) :
    K ∉ section9UniqueSubgroups G := by
  classical
  obtain ⟨E, hEHall, hKsubE⟩ :=
    section10_exists_hall_compl_sigma_containing (G := G) hM hKle hKσ
  by_cases hEbot : E = ⊥
  · have hKsub_bot : K.subgroupOf M = ⊥ := by
      exact le_bot_iff.mp (hKsubE.trans (le_of_eq hEbot))
    have hKmap : (K.subgroupOf M).map M.subtype = K := by
      simpa using
        (Subgroup.map_subgroupOf_eq_of_le (G := G) (H := K) (K := M) hKle)
    have hKbot : K = ⊥ := by
      calc
        K = (K.subgroupOf M).map M.subtype := hKmap.symm
        _ = (⊥ : Subgroup M).map M.subtype := by rw [hKsub_bot]
        _ = ⊥ := by simp
    simpa [hKbot] using section10_bot_not_unique (G := G) hM
  · have : Nontrivial E := (Subgroup.nontrivial_iff_ne_bot E).2 hEbot
    obtain ⟨p, hpLargest⟩ := section10_exists_largest_prime_divisor_of_nontrivial E
    have : Fact p.val.Prime := ⟨p.property⟩
    have hp_dvd_E : p.val ∣ Nat.card E := hpLargest.2.1
    have hpσ : p ∉ section10SigmaPrimes M := by
      have hp_compl : p ∈ (section10SigmaPrimes M)ᶜ :=
        hEHall.p_in_pi_of_p_dvd_card p hp_dvd_E
      simpa using hp_compl
    have hMsolv : Group.IsSolvable M :=
      IsMinCE.proper_subgroups_solvable M (lt_top_iff_ne_top.2 hM.1)
    have hEsolv : Group.IsSolvable E := by
      let : Group.IsSolvable M := hMsolv
      infer_instance
    have hModd : Odd (Nat.card M) :=
      odd_of_card_dvd IsMinCE.odd_order (Subgroup.card_subgroup_dvd_card M)
    have hEodd : Odd (Nat.card E) :=
      hModd.of_dvd_nat (Subgroup.card_subgroup_dvd_card E)
    have hErank : groupRank E ≤ 2 :=
      section10_hall_compl_sigma_groupRank_le_two (G := G) hM hEHall
    obtain ⟨PE, hPEnormal⟩ :=
      theorem_4_20_largest_prime_normal_sylow
        (G := E) hEsolv hEodd (Or.inl hErank) hpLargest
    obtain ⟨PM, hPM_eq⟩ :=
      section10_hall_compl_sylow_map_to_maximal_sylow
        (G := G) hEHall hpσ PE
    let PsubM : Subgroup M := (PE : Subgroup E).map E.subtype
    let PG : Subgroup G := PsubM.map M.subtype
    have hPG_eq_ambient : PG = section10AmbientSylowSubgroup M PM := by
      simpa [PG, PsubM, section10AmbientSylowSubgroup] using
        (congrArg (fun S : Subgroup M => S.map M.subtype) hPM_eq).symm
    have hPG_le_M : PG ≤ M := by
      intro x hx
      rcases Subgroup.mem_map.mp hx with ⟨y, _hy, rfl⟩
      exact y.property
    have hpM : p ∈ subgroupPrimeSet M := by
      exact hp_dvd_E.trans (Subgroup.card_subgroup_dvd_card E)
    have hnorm_not_le_M : ¬ Subgroup.normalizer (PG : Set G) ≤ M := by
      intro hnorm
      have hpσ' : p ∈ section10SigmaPrimes M := by
        refine ⟨hpM, PM, ?_⟩
        simpa [hPG_eq_ambient] using hnorm
      exact hpσ hpσ'
    have hp_dvd_PM : p.val ∣ Nat.card (PM : Subgroup M) :=
      Sylow.dvd_card_of_dvd_card PM hpM
    have hPG_card : Nat.card PG = Nat.card (PM : Subgroup M) := by
      simpa [hPG_eq_ambient] using section10AmbientSylowSubgroup_card (G := G) PM
    have hPGne : PG ≠ ⊥ := by
      intro hbot
      have hcard : Nat.card PG = 1 := by
        simp [hbot]
      have hp_dvd_PG : p.val ∣ Nat.card PG := by
        simpa [hPG_card] using hp_dvd_PM
      have hp_dvd_one : p.val ∣ 1 := by
        rw [hcard] at hp_dvd_PG
        exact hp_dvd_PG
      exact p.property.not_dvd_one hp_dvd_one
    have hnorm_proper : Subgroup.normalizer (PG : Set G) ≠ ⊤ :=
      section10_normalizer_ne_top_of_ne_bot_le_maximal' hM hPG_le_M hPGne
    obtain ⟨H, hHcont⟩ :=
      section10_exists_maximalSubgroupsContaining_of_ne_top (G := G) hnorm_proper
    have hH : H ∈ section9MaximalSubgroups G := hHcont.1
    have hN_le_H : Subgroup.normalizer (PG : Set G) ≤ H := hHcont.2
    have hE_le_norm :
        E.map M.subtype ≤ Subgroup.normalizer (PG : Set G) := by
      simpa [PG, PsubM] using
        section10_hall_compl_normal_sylow_le_ambient_normalizer
          (G := G) (M := M) (E := E) PE hPEnormal
    have hKleH : K ≤ H := by
      intro x hxK
      have hxM : x ∈ M := hKle hxK
      have hxE : (⟨x, hxM⟩ : M) ∈ E := hKsubE hxK
      have hxEmap : x ∈ E.map M.subtype :=
        Subgroup.mem_map.mpr ⟨⟨x, hxM⟩, hxE, rfl⟩
      exact hN_le_H (hE_le_norm hxEmap)
    have hHM : H ≠ M := by
      intro hHM
      exact hnorm_not_le_M (by simpa [hHM] using hN_le_H)
    exact
      section10_not_unique_of_le_two_distinct_maximal
        (G := G) hM hH hKle hKleH hHM

end Section10
