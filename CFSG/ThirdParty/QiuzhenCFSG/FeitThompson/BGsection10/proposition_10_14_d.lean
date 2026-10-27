module

public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.BGsection10.proposition_10_14_c
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

omit [Finite G] [IsMinCE G] in
public theorem CFSG.section10_proper_of_le_maximal
    {H M : Subgroup G} (hHM : H ≤ M) (hM : M ∈ section9MaximalSubgroups G) :
    H ≠ ⊤ := by
  intro hHtop
  have htop_le_M : (⊤ : Subgroup G) ≤ M := by
    simpa [hHtop] using hHM
  exact hM.1 (top_le_iff.mp htop_le_M)

omit [Finite G] [IsMinCE G] in
private theorem CFSG.section10_unique_overgroups_eq_of_contains_maximal
    {H M : Subgroup G} (hH : H ∈ section9UniqueSubgroups G)
    (hM : M ∈ section9MaximalSubgroups G) (hHM : H ≤ M) :
    section9MaximalSubgroupsContaining H = {M} := by
  classical
  rcases hH with ⟨_hHproper, N, hNuniq⟩
  have hMcont : M ∈ section9MaximalSubgroupsContaining H := ⟨hM, hHM⟩
  have hMN : M = N := by
    have hsingle : M ∈ ({N} : Set (Subgroup G)) := by
      simpa [hNuniq] using hMcont
    simpa using hsingle
  simpa [hMN] using hNuniq

omit [IsMinCE G] in
private theorem CFSG.section10_le_unique_maximal_of_le
    {Y X M : Subgroup G} (hYX : Y ≤ X) (hXproper : X ≠ ⊤)
    (hMuniq : section9MaximalSubgroupsContaining Y = {M}) :
    X ≤ M := by
  classical
  rcases eq_top_or_exists_le_coatom X with hXtop | ⟨N, hNcoatom, hXN⟩
  · exact False.elim (hXproper hXtop)
  have hNmax : N ∈ section9MaximalSubgroups G := by
    exact hNcoatom
  have hNcont : N ∈ section9MaximalSubgroupsContaining Y := ⟨hNmax, hYX.trans hXN⟩
  have hNM : N = M := by
    have hNsingle : N ∈ ({M} : Set (Subgroup G)) := by
      simpa [hMuniq] using hNcont
    simpa using hNsingle
  simpa [hNM] using hXN

public theorem CFSG.section10_normalizer_ne_top_of_ne_bot_le_maximal
    {X M : Subgroup G} (hM : M ∈ section9MaximalSubgroups G)
    (hXM : X ≤ M) (hXne : X ≠ ⊥) :
    Subgroup.normalizer (X : Set G) ≠ ⊤ := by
  intro hnorm_top
  have hXnormal : X.Normal := Subgroup.normalizer_eq_top_iff.mp hnorm_top
  let : IsSimpleGroup G := IsMinCE.simple
  rcases (haveI := hXnormal; IsSimpleGroup.eq_bot_or_eq_top_of_normal X) with hXbot | hXtop
  · exact hXne hXbot
  · have htop_le_M : (⊤ : Subgroup G) ≤ M := by
      simpa [hXtop] using hXM
    exact hM.1 (top_le_iff.mp htop_le_M)

omit [IsMinCE G] in
public theorem CFSG.section10_normalizer_le_of_unique_le_maximal
    {D X M : Subgroup G} (hM : M ∈ section9MaximalSubgroups G)
    (hDunique : D ∈ section9UniqueSubgroups G) (hDM : D ≤ M)
    (hDX : D ≤ X) (hXproper : X ≠ ⊤) :
    X ≤ M := by
  have hMuniq : section9MaximalSubgroupsContaining D = {M} :=
    section10_unique_overgroups_eq_of_contains_maximal hDunique hM hDM
  exact section10_le_unique_maximal_of_le hDX hXproper hMuniq

private theorem CFSG.section10_pSubgroup_le_pCore_of_nilpotent
    {p : ℕ} [Fact p.Prime] {R : Type*} [Group R] [Finite R]
    [Group.IsNilpotent R] {B : Subgroup R} (hBp : IsPGroup p B) :
    B ≤ pCore p R := by
  obtain ⟨S, hB_le_S⟩ := IsPGroup.exists_le_sylow (G := R) (p := p) hBp
  have hS_normal : (S : Subgroup R).Normal :=
    Group.IsNilpotent.sylow_normal (p := p) inferInstance S
  exact hB_le_S.trans (le_sSup ⟨hS_normal, S.isPGroup'⟩)

public theorem CFSG.section10_pCore_ne_bot_of_dvd_card_nilpotent
    {H : Type*} [Group H] [Finite H] [Group.IsNilpotent H]
    {q : ℕ} [Fact q.Prime] (hq : q ∣ Nat.card H) :
    pCore q H ≠ ⊥ := by
  classical
  let S : Sylow q H := Classical.choice inferInstance
  have hS_le : (S : Subgroup H) ≤ pCore q H :=
    section10_pSubgroup_le_pCore_of_nilpotent (p := q) (R := H) S.isPGroup'
  have hqS : q ∣ Nat.card (S : Subgroup H) :=
    Sylow.dvd_card_of_dvd_card S hq
  intro hbot
  have hSbot : (S : Subgroup H) = ⊥ :=
    le_bot_iff.mp (hS_le.trans (le_of_eq hbot))
  have hcardS : Nat.card (S : Subgroup H) = 1 := by
    simp [hSbot]
  rw [hcardS] at hqS
  exact (Fact.out : Nat.Prime q).not_dvd_one hqS

omit [IsMinCE G] in
public theorem CFSG.section10_sylow_map_subtype_of_normalizer_le
    {p : ℕ} [Fact p.Prime] {M : Subgroup G} (P : Sylow p M)
    (hN : Subgroup.normalizer
        ((((P : Subgroup M).map M.subtype : Subgroup G)) : Set G) ≤ M) :
    ∃ P₀ : Sylow p G,
      (P₀ : Subgroup G) = (P : Subgroup M).map M.subtype := by
  classical
  let PG : Subgroup G := (P : Subgroup M).map M.subtype
  have hPGp : IsPGroup p PG := by
    exact IsPGroup.map (p := p) (H := (P : Subgroup M)) P.isPGroup' M.subtype
  suffices hnot : ¬ p ∣ PG.index by
    exact ⟨hPGp.toSylow hnot, rfl⟩
  intro hpidx
  rcases hPGp.exists_card_eq with ⟨n, hPGcard⟩
  have hdvdG : p ^ (n + 1) ∣ Nat.card G := by
    rcases hpidx with ⟨a, ha⟩
    refine ⟨a, ?_⟩
    calc
      Nat.card G = Nat.card PG * PG.index := by rw [PG.card_mul_index]
      _ = p ^ n * (p * a) := by rw [hPGcard, ha]
      _ = p ^ (n + 1) * a := by rw [pow_succ']; ac_rfl
  have hdvd_norm :
      p ^ (n + 1) ∣ Nat.card (Subgroup.normalizer (PG : Set G)) := by
    exact Sylow.prime_pow_dvd_card_normalizer (G := G) (p := p) (n := n)
      (H := PG) hdvdG hPGcard
  have hnorm_card_dvd_M :
      Nat.card (Subgroup.normalizer (PG : Set G)) ∣ Nat.card M := by
    let N : Subgroup G := Subgroup.normalizer (PG : Set G)
    have hcard_eq : Nat.card N = Nat.card (N.subgroupOf M) :=
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe (H := N) (K := M) (by
        simpa [N, PG] using hN)).toEquiv.symm
    rw [hcard_eq]
    exact Subgroup.card_subgroup_dvd_card (N.subgroupOf M)
  have hdvdM : p ^ (n + 1) ∣ Nat.card M := hdvd_norm.trans hnorm_card_dvd_M
  have hPGcard_eq_P : Nat.card PG = Nat.card (P : Subgroup M) := by
    simpa [PG] using
      (Subgroup.card_map_of_injective
        (K := (P : Subgroup M)) (f := M.subtype) M.subtype_injective)
  have hPcard : Nat.card (P : Subgroup M) = p ^ n := by
    rw [← hPGcard_eq_P]
    exact hPGcard
  have hp_dvd_P_index : p ∣ (P : Subgroup M).index := by
    have hdvd' : p ^ n * p ∣ p ^ n * (P : Subgroup M).index := by
      have hMcard : Nat.card M = p ^ n * (P : Subgroup M).index := by
        rw [← (P : Subgroup M).card_mul_index, hPcard]
      simpa [hMcard, pow_succ] using hdvdM
    exact Nat.dvd_of_mul_dvd_mul_left (pow_pos (Fact.out : Nat.Prime p).pos n) hdvd'
  exact P.not_dvd_index hp_dvd_P_index

omit [IsMinCE G] in
/-- An ideal prime in `σ(M)` lies in `β(M)`. -/
public theorem CFSG.section10_betaPrimes_of_idealPrime_of_sigma
    {M : Subgroup G} {p : Nat.Primes}
    (_hM : M ∈ section9MaximalSubgroups G)
    (hpIdeal : section10IdealPrime p G)
    (hpσ : p ∈ section10SigmaPrimes M) :
    p ∈ section10BetaPrimes M := by
  classical
  have : Fact p.val.Prime := ⟨p.property⟩
  rcases hpσ with ⟨hpM, P, hnormP⟩
  have hpα : p ∈ section10AlphaPrimes M := by
    by_contra hpα
    have hPnarrow : IsNarrowPGroup p.val (P : Subgroup M) :=
      section10_sylow_narrow_of_not_mem_alpha (G := G) (M := M) hpα P
    obtain ⟨PG, hPG_eq⟩ :=
      section10_sylow_map_subtype_of_normalizer_le
        (G := G) (M := M) P (by
          simpa [section10AmbientSylowSubgroup] using hnormP)
    let Pamb : Subgroup G := (P : Subgroup M).map M.subtype
    let ePamb : (P : Subgroup M) ≃* Pamb :=
      Subgroup.equivMapOfInjective
        (f := M.subtype) (P : Subgroup M) M.subtype_injective
    have hPambNarrow : IsNarrowPGroup p.val Pamb :=
      section10_isNarrowPGroup_of_equiv ePamb.symm hPnarrow
    have hPGnarrow : IsNarrowPGroup p.val (PG : Subgroup G) := by
      rw [hPG_eq]
      exact hPambNarrow
    exact hpIdeal.2 PG hPGnarrow
  exact ⟨hpα, hpIdeal⟩

public theorem CFSG.section10_alpha_sylow_normalizer_le
    {M : Subgroup G} (hM : M ∈ section9MaximalSubgroups G)
    {q : Nat.Primes} (hqα : q ∈ section10AlphaPrimes M)
    (P : Sylow q.val M) :
    Subgroup.normalizer ((((P : Subgroup M).map M.subtype : Subgroup G)) : Set G) ≤ M := by
  classical
  have : Fact q.val.Prime := ⟨q.2⟩
  let PG : Subgroup G := (P : Subgroup M).map M.subtype
  have hPG_le_M : PG ≤ M := by
    intro x hx
    rcases Subgroup.mem_map.mp hx with ⟨y, _hy, rfl⟩
    exact y.property
  have hqrankM : 3 ≤ primeRank q.val M :=
    Nat.succ_le_of_lt hqα.2
  have hPrank : 3 ≤ groupRank (P : Subgroup M) :=
    hqrankM.trans (section10_primeRank_le_groupRank_sylow (G := M) P)
  let ePG : (P : Subgroup M) ≃* PG :=
    Subgroup.equivMapOfInjective
      (f := M.subtype) (P : Subgroup M) M.subtype_injective
  have hPGrank : 3 ≤ groupRank PG :=
    hPrank.trans
      (section10_groupRank_le_of_equiv
        (R := PG) (S := (P : Subgroup M)) ePG.symm)
  have hPGproper : PG ≠ ⊤ :=
    section10_proper_of_le_maximal hPG_le_M hM
  have hPGunique : PG ∈ section9UniqueSubgroups G :=
    theorem_9_6 (K := PG) hPGproper (by omega) (Or.inl hPGrank)
  have hqP : q.val ∣ Nat.card (P : Subgroup M) :=
    Sylow.dvd_card_of_dvd_card P hqα.1
  have hPGcard_eq : Nat.card PG = Nat.card (P : Subgroup M) := by
    simpa [PG] using
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
  have hnormproper :
      Subgroup.normalizer (PG : Set G) ≠ ⊤ :=
    section10_normalizer_ne_top_of_ne_bot_le_maximal hM hPG_le_M hPGne
  have hPG_le_norm : PG ≤ Subgroup.normalizer (PG : Set G) :=
    Subgroup.le_normalizer
  have hnorm_le_M : Subgroup.normalizer (PG : Set G) ≤ M :=
    section10_normalizer_le_of_unique_le_maximal
      hM hPGunique hPG_le_M hPG_le_norm hnormproper
  simpa [PG] using hnorm_le_M

/-- Proposition 10.14(d). -/
public theorem CFSG.proposition_10_14_d
    {p : Nat.Primes} (_hpβG : section10IdealPrime p G) (_P : Sylow p.val G) :
    ∀ {M Y : Subgroup G}, M ∈ section9MaximalSubgroups G →
      Y ≤ M → Y ≠ ⊥ → IsPiSubgroup (section10BetaPrimes M) Y →
        Subgroup.normalizer (Y : Set G) ≤ M := by
  classical
  intro M Y hM hYM hYne hYπ
  have hYproper : Y ≠ ⊤ := section10_proper_of_le_maximal hYM hM
  have : Group.IsSolvable Y :=
    IsMinCE.proper_subgroups_solvable Y (lt_top_iff_ne_top.mpr hYproper)
  have hYcard_ne_one : Nat.card Y ≠ 1 := by
    intro hcard
    exact hYne ((Subgroup.card_eq_one (H := Y)).1 hcard)
  have hFne : fittingSubgroup Y ≠ ⊥ := by
    intro hFbot
    have hYcard : Nat.card Y = 1 :=
      (fitting_eq_bot_iff_card_eq_one_of_solvable Y).mp hFbot
    exact hYcard_ne_one hYcard
  let F : Subgroup Y := fittingSubgroup Y
  have hFcard_ne_one : Nat.card F ≠ 1 := by
    intro hcard
    have hFbot : F = ⊥ := (Subgroup.card_eq_one (H := F)).1 hcard
    exact hFne (by simpa [F] using hFbot)
  obtain ⟨q0, hq0prime, hq0dvdF⟩ := Nat.exists_prime_and_dvd hFcard_ne_one
  let q : Nat.Primes := ⟨q0, hq0prime⟩
  have : Fact q.val.Prime := ⟨q.2⟩
  let CoreF : Subgroup F := pCore q.val F
  let CoreY : Subgroup Y := CoreF.map F.subtype
  let X : Subgroup G := CoreY.map Y.subtype
  have hqF : q.val ∣ Nat.card F := by
    simpa [q] using hq0dvdF
  have hCoreF_ne : CoreF ≠ ⊥ := by
    simpa [CoreF] using
      section10_pCore_ne_bot_of_dvd_card_nilpotent (H := F) (q := q.val) hqF
  have hCoreY_ne : CoreY ≠ ⊥ := by
    intro hCoreYbot
    have hmap_bot :
        CoreF.map F.subtype = (⊥ : Subgroup F).map F.subtype := by
      simpa [CoreY] using hCoreYbot
    exact hCoreF_ne (Subgroup.map_injective F.subtype_injective hmap_bot)
  have hXne : X ≠ ⊥ := by
    intro hXbot
    have hmap_bot :
        CoreY.map Y.subtype = (⊥ : Subgroup Y).map Y.subtype := by
      simpa [X] using hXbot
    exact hCoreY_ne (Subgroup.map_injective Y.subtype_injective hmap_bot)
  have hX_le_Y : X ≤ Y := by
    intro x hx
    rcases Subgroup.mem_map.mp hx with ⟨y, _hy, rfl⟩
    exact y.property
  have hX_le_M : X ≤ M := hX_le_Y.trans hYM
  have hqY : q.val ∣ Nat.card Y :=
    hqF.trans (Subgroup.card_subgroup_dvd_card F)
  have hqβM : q ∈ section10BetaPrimes M := hYπ q hqY
  have hqαM : q ∈ section10AlphaPrimes M := hqβM.1
  have hqβG : section10IdealPrime q G := hqβM.2
  have hCoreYchar : CoreY.Characteristic := by
    have : F.Characteristic := fittingSubgroup_characteristic
    have : CoreF.Characteristic :=
      pCore_characteristic (G := F) (p := q.val)
    simpa [CoreY, CoreF, F] using
      characteristic_map_subtype_of_characteristic (G := Y) F CoreF
  let : CoreY.Characteristic := hCoreYchar
  have hnormY_le_normX :
      Subgroup.normalizer (Y : Set G) ≤ Subgroup.normalizer (X : Set G) := by
    simpa [X, CoreY] using
      section10_normalizer_le_normalizer_map_subtype_of_characteristic
        (G := G) Y CoreY
  have hCoreYp : IsPGroup q.val CoreY := by
    simpa [CoreY, CoreF] using
      IsPGroup.map (p := q.val) (H := CoreF)
        (pCore_isPGroup (G := F) (p := q.val)) F.subtype
  have hXp : IsPGroup q.val X := by
    simpa [X] using
      IsPGroup.map (p := q.val) (H := CoreY) hCoreYp Y.subtype
  have hXMp : IsPGroup q.val (X.subgroupOf M) :=
    hXp.of_equiv
      (Subgroup.subgroupOfEquivOfLe (H := X) (K := M) hX_le_M).symm
  obtain ⟨PM, hXM_le_PM⟩ :=
    IsPGroup.exists_le_sylow (G := M) (p := q.val) hXMp
  have hnormPM_le_M :
      Subgroup.normalizer ((((PM : Subgroup M).map M.subtype : Subgroup G)) : Set G) ≤ M :=
    section10_alpha_sylow_normalizer_le (G := G) hM hqαM PM
  obtain ⟨PG, hPG_eq⟩ :=
    section10_sylow_map_subtype_of_normalizer_le
      (G := G) (M := M) PM hnormPM_le_M
  have hX_le_PGmap : X ≤ (PM : Subgroup M).map M.subtype := by
    intro x hx
    let xM : M := ⟨x, hX_le_M hx⟩
    have hxM : xM ∈ X.subgroupOf M := hx
    have hxPM : xM ∈ (PM : Subgroup M) := hXM_le_PM hxM
    exact Subgroup.mem_map.mpr ⟨xM, hxPM, rfl⟩
  have hX_le_PG : X ≤ (PG : Subgroup G) := by
    simpa [hPG_eq] using hX_le_PGmap
  let D : Subgroup G := subgroupNormalizerIn (PG : Subgroup G) (X : Set G)
  have hDunique : D ∈ section9UniqueSubgroups G := by
    simpa [D] using proposition_10_14_c (G := G) hqβG PG hX_le_PG
  have hPG_le_M : (PG : Subgroup G) ≤ M := by
    rw [hPG_eq]
    intro x hx
    rcases Subgroup.mem_map.mp hx with ⟨y, _hy, rfl⟩
    exact y.property
  have hD_le_M : D ≤ M := by
    exact (section10_subgroupNormalizerIn_le
      (PG : Subgroup G) (X : Set G)).trans hPG_le_M
  have hD_le_normX : D ≤ Subgroup.normalizer (X : Set G) :=
    section10_subgroupNormalizerIn_le_normalizer (PG : Subgroup G) (X : Set G)
  have hnormXproper :
      Subgroup.normalizer (X : Set G) ≠ ⊤ :=
    section10_normalizer_ne_top_of_ne_bot_le_maximal hM hX_le_M hXne
  have hnormX_le_M : Subgroup.normalizer (X : Set G) ≤ M :=
    section10_normalizer_le_of_unique_le_maximal
      hM hDunique hD_le_M hD_le_normX hnormXproper
  exact hnormY_le_normX.trans hnormX_le_M

end Section10
