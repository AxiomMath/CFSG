module

public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.BGsection10.lemma_10_5
import Mathlib.GroupTheory.Schreier
import Mathlib.LinearAlgebra.Projectivization.Cardinality

namespace CFSG
end CFSG
open CFSG

open scoped Pointwise

/-!
# Lemma 10.4(b) from BG Section 10

This file records a statement-only scaffold for Section 10 of
`Local Analysis for the Odd Order Theorem`.

The local PDF extraction mangles the Greek letters used in the book. This
module imports the shared Section 10 notation from `FeitThompson.BGsection10.Defs`.
-/

section Section10

variable {G : Type*} [Group G] [Finite G] [IsMinCE G]

private theorem CFSG.section10_exists_sigma_prime_of_malpha_ne_bot
    {M : Subgroup G} (hM : M ∈ section9MaximalSubgroups G)
    (hMalpha : section10Malpha M ≠ ⊥) :
    ∃ q : Nat.Primes, q ∈ section10SigmaPrimes M := by
  classical
  let K : Subgroup M := section10MalphaSubgroup M
  have hKne : K ≠ ⊥ := by
    intro hKbot
    apply hMalpha
    simp [section10Malpha, K, hKbot]
  letI : Nontrivial K := (Subgroup.nontrivial_iff_ne_bot K).2 hKne
  obtain ⟨q, hq⟩ := section10_exists_largest_prime_divisor_of_nontrivial K
  have hqα : q ∈ section10AlphaPrimes M :=
    (section10_malphaSubgroup_isHall hM).p_in_pi_of_p_dvd_card q hq.2.1
  exact ⟨q, section10_alpha_subset_sigma hM hqα⟩

omit [IsMinCE G] in
private theorem CFSG.section10_omegaOneCenter_ne_bot_of_sylow_prime_mem
    {M : Subgroup G} {p : Nat.Primes} (hpM : p ∈ subgroupPrimeSet M)
    (P : Sylow p.val M) :
    section10OmegaOneCenter p (section10AmbientSylowSubgroup M P) ≠ ⊥ := by
  classical
  haveI : Fact p.val.Prime := ⟨p.property⟩
  let PG : Subgroup G := section10AmbientSylowSubgroup M P
  have hPne : (P : Subgroup M) ≠ ⊥ := P.ne_bot_of_dvd_card hpM
  have hPGne : PG ≠ ⊥ := by
    simpa [PG, section10AmbientSylowSubgroup] using
      section10_map_subtype_ne_bot_of_ne_bot (G := G) (M := M) hPne
  letI : Nontrivial PG := (Subgroup.nontrivial_iff_ne_bot PG).2 hPGne
  have hPGp : IsPGroup p.val PG := by
    change IsPGroup p.val ((P : Subgroup M).map M.subtype)
    exact IsPGroup.map (p := p.val) (H := (P : Subgroup M)) P.isPGroup' M.subtype
  have hZ_nontrivial : Nontrivial (Subgroup.center PG) := hPGp.center_nontrivial
  have hpdvd_center : p.val ∣ Nat.card (Subgroup.center PG) := by
    have hcenter_p : IsPGroup p.val (Subgroup.center PG) :=
      hPGp.to_subgroup (Subgroup.center PG)
    rcases (IsPGroup.nontrivial_iff_card
        (p := p.val) (G := Subgroup.center PG) (hG := hcenter_p)).1 hZ_nontrivial with
      ⟨n, hn, hcard⟩
    rw [hcard]
    exact dvd_pow_self p.val (Nat.ne_of_gt hn)
  have hΩlocal_ne_bot : Ω₁Z p.val PG ≠ ⊥ := by
    simpa [Ω₁Z] using
      omega₁_map_subtype_ne_bot (M := Subgroup.center PG) (p := p.val) hpdvd_center
  simpa [PG, section10OmegaOneCenter] using
    section10_map_subtype_ne_bot_of_ne_bot (G := G) (M := PG) hΩlocal_ne_bot

omit [IsMinCE G] in
private theorem CFSG.section10_exists_nontrivial_mem_omegaOneCenter_of_sylow_prime_mem
    {M : Subgroup G} {p : Nat.Primes} (hpM : p ∈ subgroupPrimeSet M)
    (P : Sylow p.val M) :
    ∃ x : G, x ∈ section10OmegaOneCenter p (section10AmbientSylowSubgroup M P) ∧ x ≠ 1 := by
  classical
  let Z : Subgroup G := section10OmegaOneCenter p (section10AmbientSylowSubgroup M P)
  have hZne : Z ≠ ⊥ :=
    section10_omegaOneCenter_ne_bot_of_sylow_prime_mem (G := G) hpM P
  letI : Nontrivial Z := (Subgroup.nontrivial_iff_ne_bot Z).2 hZne
  obtain ⟨z, hz_ne⟩ := exists_ne (1 : Z)
  exact ⟨z, z.property, by
    intro hz
    exact hz_ne (Subtype.ext hz)⟩

omit [Finite G] [IsMinCE G] in
public theorem CFSG.section10_mem_omegaOneCenter_le_ambient_sylow
    {p : Nat.Primes} {P : Subgroup G} {x : G}
    (hx : x ∈ section10OmegaOneCenter p P) :
    x ∈ P := by
  change x ∈ (Ω₁Z p.val P).map P.subtype at hx
  rw [Subgroup.mem_map] at hx
  rcases hx with ⟨xP, _hxΩ, rfl⟩
  exact xP.property

omit [Finite G] [IsMinCE G] in
public theorem CFSG.section10_omegaOneCenter_le
    {p : Nat.Primes} (P : Subgroup G) :
    section10OmegaOneCenter p P ≤ P := by
  intro x hx
  exact section10_mem_omegaOneCenter_le_ambient_sylow (G := G) (p := p) hx

omit [Finite G] [IsMinCE G] in
public theorem CFSG.section10_omegaOneCenter_le_centralizer
    {p : Nat.Primes} (P : Subgroup G) :
    section10OmegaOneCenter p P ≤ Subgroup.centralizer (P : Set G) := by
  intro x hx
  rw [Subgroup.mem_centralizer_iff]
  intro y hy
  change x ∈ (Ω₁Z p.val P).map P.subtype at hx
  rcases Subgroup.mem_map.mp hx with ⟨xP, hxΩ, rfl⟩
  let yP : P := ⟨y, hy⟩
  have hx_center : xP ∈ Subgroup.center P :=
    section10_omega1Z_le_center_pre p.val P hxΩ
  exact congrArg Subtype.val (Subgroup.mem_center_iff.mp hx_center yP)

omit [Finite G] [IsMinCE G] in
public theorem CFSG.section10_zpowers_card_eq_prime_of_mem_omegaOneCenter
    {p : Nat.Primes} {P : Subgroup G} {x : G}
    (hx : x ∈ section10OmegaOneCenter p P) (hxne : x ≠ 1) :
    Nat.card (Subgroup.zpowers x) = p.val := by
  classical
  haveI : Fact p.val.Prime := ⟨p.property⟩
  have hxΩ : x ∈ (Ω₁Z p.val P).map P.subtype := by
    simpa [section10OmegaOneCenter] using hx
  rcases Subgroup.mem_map.mp hxΩ with ⟨xP, hxPΩ, hx_eq⟩
  have hxP_ne : xP ≠ 1 := by
    intro hxP_one
    exact hxne (by rw [← hx_eq, hxP_one]; rfl)
  have hΩelem : IsElementaryAbelian p.val (Ω₁Z p.val P) :=
    section10_omega1Z_isElementaryAbelian_pre (p := p.val) P
  have hxPpow : xP ^ p.val = 1 := by
    letI : IsElementaryAbelian p.val (Ω₁Z p.val P) := hΩelem
    exact elemPow_eq_one_of_isElementaryAbelian xP hxPΩ
  have hxpow : x ^ p.val = 1 := by
    simpa [← hx_eq] using congrArg (fun z : P => (z : G)) hxPpow
  calc
    Nat.card (Subgroup.zpowers x) = orderOf x := by simp
    _ = p.val := orderOf_eq_prime hxpow hxne

omit [Finite G] [IsMinCE G] in
public theorem CFSG.section10_elementCentralizerIn_eq_subgroupCentralizerIn_zpowers
    (H : Subgroup G) (x : G) :
    elementCentralizerIn H x = subgroupCentralizerIn H (Subgroup.zpowers x) := by
  ext g
  constructor
  · intro hg
    refine ⟨hg.1, ?_⟩
    change g ∈ Subgroup.centralizer (Subgroup.zpowers x : Set G)
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    rcases hy with ⟨n, rfl⟩
    have hxg : x * g = g * x :=
      (Subgroup.mem_centralizer_iff.mp hg.2) x (by simp)
    exact (Commute.zpow_left (show Commute x g from hxg) n).eq
  · intro hg
    refine ⟨hg.1, ?_⟩
    change g ∈ Subgroup.centralizer ({x} : Set G)
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    have hyx : y = x := by simpa using hy
    subst y
    exact (Subgroup.mem_centralizer_iff.mp hg.2) x (Subgroup.mem_zpowers x)

omit [IsMinCE G] in
private theorem CFSG.section10_primeRank_le_groupRank_pre
    {H : Type*} [Group H] [Finite H] {q : ℕ} (hq : Nat.Prime q) :
    primeRank q H ≤ groupRank H := by
  rw [groupRank]
  refine le_csSup ?_ ?_
  · refine ⟨Nat.card H, ?_⟩
    intro n hn
    rcases hn with ⟨r, _hr, hnr⟩
    exact hnr.trans (section10_primeRank_le_natCard_pre (q := r) H)
  · exact ⟨q, hq, le_rfl⟩

public theorem CFSG.section10_isZGroup_of_subgroup_groupRank_le_one
    (K : Subgroup G) (hrank : groupRank K ≤ 1) :
    IsZGroup K := by
  classical
  rw [isZGroup_iff]
  intro q hq P
  haveI : Fact q.Prime := ⟨hq⟩
  by_cases hqdvd : q ∣ Nat.card K
  · have hqodd : q ≠ 2 :=
      Odd.ne_two_of_dvd_nat IsMinCE.odd_order
        (hqdvd.trans (Subgroup.card_subgroup_dvd_card K))
    let q' : Nat.Primes := ⟨q, hq⟩
    have hqrank : primeRank q K ≤ 1 :=
      (section10_primeRank_le_groupRank_pre (H := K) hq).trans hrank
    exact section10_sylow_isCyclic_of_primeRank_le_one
      (G := G) (M := K) (p := q') P hqodd hqrank
  · have hP_not_dvd : ¬ q ∣ Nat.card P := by
      intro hPdvd
      exact hqdvd (hPdvd.trans (Subgroup.card_subgroup_dvd_card (P : Subgroup K)))
    rcases P.isPGroup'.exists_card_eq with ⟨n, hcardP⟩
    have hn_zero : n = 0 := by
      by_contra hn_ne
      obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hn_ne
      apply hP_not_dvd
      rw [hcardP, pow_succ']
      exact dvd_mul_right q (q ^ m)
    have hcard_one : Nat.card P = 1 := by
      simpa [hn_zero] using hcardP
    haveI : Subsingleton P :=
      Finite.card_le_one_iff_subsingleton.mp (by omega)
    exact isCyclic_of_subsingleton (α := P)

private theorem CFSG.section10_one_lt_groupRank_of_not_isZGroup_subgroup
    {K : Subgroup G} (hnotZ : ¬ IsZGroup K) :
    1 < groupRank K := by
  by_contra hle'
  have hle : groupRank K ≤ 1 := by omega
  exact hnotZ (section10_isZGroup_of_subgroup_groupRank_le_one (G := G) K hle)

private theorem CFSG.section10_zpowers_isPiSubgroup_alpha_compl_of_not_sigma
    {M : Subgroup G} {p : Nat.Primes} (hM : M ∈ section9MaximalSubgroups G)
    (hpσ : p ∉ section10SigmaPrimes M) {x : G}
    (hxcard : Nat.card (Subgroup.zpowers x) = p.val) :
    IsPiSubgroup (section10AlphaPrimes M)ᶜ (Subgroup.zpowers x) := by
  intro q hq_dvd
  have hp_not_alpha : p ∉ section10AlphaPrimes M := by
    intro hpα
    exact hpσ (section10_alpha_subset_sigma hM hpα)
  have hq_dvd_p : q.val ∣ p.val := by
    simpa [hxcard] using hq_dvd
  have hq_eq_p_val : q.val = p.val :=
    (Nat.prime_dvd_prime_iff_eq q.property p.property).mp hq_dvd_p
  have hq_eq_p : q = p := Subtype.ext hq_eq_p_val
  rw [hq_eq_p]
  exact hp_not_alpha

private theorem CFSG.section10_centralizer_family_eq_singleton_of_not_zgroup_malpha
    {M : Subgroup G} {p : Nat.Primes}
    (hM : M ∈ section9MaximalSubgroups G) (hpσ : p ∉ section10SigmaPrimes M)
    (P : Sylow p.val M) {x : G}
    (hxΩ : x ∈ section10OmegaOneCenter p (section10AmbientSylowSubgroup M P))
    (hxne : x ≠ 1)
    (hnotZ : ¬ IsZGroup ↥(elementCentralizerIn (section10Malpha M) x)) :
    section10MaximalSubgroupsContainingCentralizer x = {M} := by
  classical
  let PG : Subgroup G := section10AmbientSylowSubgroup M P
  let X : Subgroup G := Subgroup.zpowers x
  have hPG_le_M : PG ≤ M := by
    intro y hy
    change y ∈ (P : Subgroup M).map M.subtype at hy
    rw [Subgroup.mem_map] at hy
    rcases hy with ⟨z, _hz, rfl⟩
    exact z.property
  have hxPG : x ∈ PG :=
    section10_mem_omegaOneCenter_le_ambient_sylow (G := G) (p := p) hxΩ
  have hxM : x ∈ M := hPG_le_M hxPG
  have hXleM : X ≤ M := by
    rintro y ⟨n, rfl⟩
    exact M.zpow_mem hxM n
  have hXcard : Nat.card X = p.val :=
    section10_zpowers_card_eq_prime_of_mem_omegaOneCenter (G := G) hxΩ hxne
  have hXpi : IsPiSubgroup (section10AlphaPrimes M)ᶜ X :=
    section10_zpowers_isPiSubgroup_alpha_compl_of_not_sigma hM hpσ hXcard
  have hcentRank :
      1 < groupRank (subgroupCentralizerIn (section10Malpha M) X) := by
    have hnotZ' : ¬ IsZGroup ↥(subgroupCentralizerIn (section10Malpha M) X) := by
      intro hZ
      exact hnotZ (by
        simpa [X] using
          (by
            rw [section10_elementCentralizerIn_eq_subgroupCentralizerIn_zpowers
              (section10Malpha M) x]
            exact hZ))
    exact section10_one_lt_groupRank_of_not_isZGroup_subgroup (G := G) hnotZ'
  have hDunique : subgroupCentralizerIn M X ∈ section9UniqueSubgroups G :=
    lemma_10_3 hM hXleM hXpi hcentRank
  let D : Subgroup G := subgroupCentralizerIn M X
  let Cx : Subgroup G := Subgroup.centralizer ({x} : Set G)
  have hDleM : D ≤ M := inf_le_left
  have hDleCx : D ≤ Cx := by
    intro g hg
    have hgcent : g ∈ Subgroup.centralizer (X : Set G) := hg.2
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    have hyx : y = x := by simpa using hy
    subst y
    exact (Subgroup.mem_centralizer_iff.mp hgcent) x (Subgroup.mem_zpowers x)
  have hDuniq_eq : section9MaximalSubgroupsContaining D = {M} :=
    section10_unique_overgroups_eq_of_contains_maximal' hDunique hM hDleM
  have hCx_proper : Cx ≠ ⊤ :=
    section8_centralizer_singleton_ne_top_of_ne_one (G := G) hxne
  have hCx_le_M : Cx ≤ M :=
    section10_le_unique_maximal_of_le' hDleCx hCx_proper hDuniq_eq
  ext N
  constructor
  · intro hN
    have hN_D : N ∈ section9MaximalSubgroupsContaining D :=
      ⟨hN.1, hDleCx.trans hN.2⟩
    have hN_eq : N = M := by
      have hsingle : N ∈ ({M} : Set (Subgroup G)) := by
        simpa [hDuniq_eq] using hN_D
      simpa using hsingle
    simp [hN_eq]
  · intro hN
    have hN_eq : N = M := by simpa using hN
    subst N
    exact ⟨hM, hCx_le_M⟩

/-- Lemma 10.4(b). -/
public theorem CFSG.lemma_10_4_b
    {M : Subgroup G} {p : Nat.Primes}
    (hM : M ∈ section9MaximalSubgroups G) (hpM : p ∈ subgroupPrimeSet M)
    (P : Sylow p.val M)
    (hpσ : p ∉ section10SigmaPrimes M) (hMalpha : section10Malpha M ≠ ⊥) :
    ∃ x : G, x ∈ section10OmegaOneCenter p (section10AmbientSylowSubgroup M P) ∧ x ≠ 1 ∧
      section10MaximalSubgroupsContainingCentralizer x ≠ {M} ∧
      IsZGroup ↥(elementCentralizerIn (section10Malpha M) x) := by
  classical
  let PG : Subgroup G := section10AmbientSylowSubgroup M P
  have hnot_norm_le_M : ¬ Subgroup.normalizer (PG : Set G) ≤ M := by
    intro hnorm_le
    exact hpσ ⟨hpM, P, by simpa [PG] using hnorm_le⟩
  obtain ⟨u, hu_norm, hu_notM⟩ := Set.not_subset.mp hnot_norm_le_M
  obtain ⟨y, hyΩ, hyne⟩ :=
    section10_exists_nontrivial_mem_omegaOneCenter_of_sylow_prime_mem
      (G := G) hpM P
  by_contra hno
  have hbad :
      ∀ z : G, z ∈ section10OmegaOneCenter p PG → z ≠ 1 →
        section10MaximalSubgroupsContainingCentralizer z = {M} := by
    intro z hzΩ hz_ne
    by_cases huniq : section10MaximalSubgroupsContainingCentralizer z = {M}
    · exact huniq
    · have hnotZ : ¬ IsZGroup ↥(elementCentralizerIn (section10Malpha M) z) := by
        intro hZ
        exact hno ⟨z, by simpa [PG] using hzΩ, hz_ne, huniq, hZ⟩
      exact
        section10_centralizer_family_eq_singleton_of_not_zgroup_malpha
          (G := G) hM hpσ P (by simpa [PG] using hzΩ) hz_ne hnotZ
  have hy_family : section10MaximalSubgroupsContainingCentralizer y = {M} :=
    hbad y (by simpa [PG] using hyΩ) hyne
  let y' : G := u⁻¹ * y * u
  have hΩchar : (Ω₁Z p.val PG).Characteristic :=
    section10_omega1Z_characteristic_pre p.val PG
  letI : (Ω₁Z p.val PG).Characteristic := hΩchar
  have hnormPG_le_normΩ :
      Subgroup.normalizer (PG : Set G) ≤
        Subgroup.normalizer (section10OmegaOneCenter p PG : Set G) := by
    have hnorm :=
      section10_normalizer_le_normalizer_map_subtype_of_characteristic_pre
        (G := G) PG (Ω₁Z p.val PG)
    simpa [section10OmegaOneCenter] using hnorm
  have hu_inv_normΩ : u⁻¹ ∈ Subgroup.normalizer (section10OmegaOneCenter p PG : Set G) :=
    hnormPG_le_normΩ ((Subgroup.normalizer (PG : Set G)).inv_mem hu_norm)
  have hy'Ω : y' ∈ section10OmegaOneCenter p PG := by
    have hmem :=
      (Subgroup.mem_normalizer_iff.mp hu_inv_normΩ y).1
        (by simpa [PG] using hyΩ)
    simpa [y', mul_assoc] using hmem
  have hy'ne : y' ≠ 1 := by
    intro hy'one
    apply hyne
    have h := congrArg (fun t : G => u * t * u⁻¹) hy'one
    simpa [y', mul_assoc] using h
  have hy'_family : section10MaximalSubgroupsContainingCentralizer y' = {M} :=
    hbad y' hy'Ω hy'ne
  let Cy : Subgroup G := Subgroup.centralizer ({y} : Set G)
  let Cy' : Subgroup G := Subgroup.centralizer ({y'} : Set G)
  have hCy'_le_M : Cy' ≤ M := by
    have hMmem : M ∈ section10MaximalSubgroupsContainingCentralizer y' := by
      simp [hy'_family]
    simpa [section10MaximalSubgroupsContainingCentralizer, Cy'] using hMmem.2
  have hCy_le_Mu : Cy ≤ M.conjBy u := by
    intro z hz
    rw [Subgroup.conjBy, Subgroup.mem_map]
    refine ⟨u⁻¹ * z * u, ?_, ?_⟩
    · apply hCy'_le_M
      rw [Subgroup.mem_centralizer_iff]
      intro t ht
      have hty' : t = y' := by simpa using ht
      subst t
      have hyz : y * z = z * y :=
        (Subgroup.mem_centralizer_iff.mp hz) y (by simp)
      calc
        y' * (u⁻¹ * z * u) = u⁻¹ * (y * z) * u := by
          simp [y', mul_assoc]
        _ = u⁻¹ * (z * y) * u := by rw [hyz]
        _ = (u⁻¹ * z * u) * y' := by
          simp [y', mul_assoc]
    · simp [MulAut.conj_apply, mul_assoc]
  have hMu_mem :
      M.conjBy u ∈ section10MaximalSubgroupsContainingCentralizer y := by
    exact ⟨section10_maximal_conjBy hM u, by simpa [Cy] using hCy_le_Mu⟩
  have hMu_eq_M : M.conjBy u = M := by
    have hsingle : M.conjBy u ∈ ({M} : Set (Subgroup G)) := by
      simpa [hy_family] using hMu_mem
    simpa using hsingle
  obtain ⟨q, hqσ⟩ := section10_exists_sigma_prime_of_malpha_ne_bot hM hMalpha
  have hMnorm : Subgroup.normalizer (M : Set G) = M :=
    section10_maximal_normalizer_eq_self_of_sigma hM hqσ
  have hu_norm_M : u ∈ Subgroup.normalizer (M : Set G) :=
    section10_mem_normalizer_of_conjBy_eq hMu_eq_M
  exact hu_notM (by simpa [hMnorm] using hu_norm_M)

end Section10
