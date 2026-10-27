module

public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.BGsection10.corollary_10_9_a_3
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
public theorem CFSG.section10_not_unique_of_le_two_distinct_maximal
    {L M N : Subgroup G}
    (hM : M ∈ section9MaximalSubgroups G) (hN : N ∈ section9MaximalSubgroups G)
    (hLM : L ≤ M) (hLN : L ≤ N) (hNM : N ≠ M) :
    L ∉ section9UniqueSubgroups G := by
  classical
  intro hL
  rcases hL with ⟨_hLproper, U, hUuniq⟩
  have hMcont : M ∈ section9MaximalSubgroupsContaining L := ⟨hM, hLM⟩
  have hNcont : N ∈ section9MaximalSubgroupsContaining L := ⟨hN, hLN⟩
  have hMU : M = U := by
    have hsingle : M ∈ ({U} : Set (Subgroup G)) := by
      simpa [hUuniq] using hMcont
    simpa using hsingle
  have hNU : N = U := by
    have hsingle : N ∈ ({U} : Set (Subgroup G)) := by
      simpa [hUuniq] using hNcont
    simpa using hsingle
  exact hNM (hNU.trans hMU.symm)

/-- Corollary 10.9(b). -/
public theorem CFSG.corollary_10_9_b
    {M H : Subgroup G} (hM : M ∈ section9MaximalSubgroups G)
    (hH : H ∈ section9MaximalSubgroups G) (hHM : H ≠ M)
    (hS :
      ∃ p : Nat.Primes, ∃ S : Sylow p.val G,
        Subgroup.normalizer ((S : Subgroup G) : Set G) ≤ H ⊓ M) :
    H ⊓ M ⊔ section10Mbeta M = M ∧
      section10AlphaPrimes M = section10BetaPrimes M := by
  classical
  rcases hS with ⟨q, S, hNleHM⟩
  have : Fact q.val.Prime := ⟨q.property⟩
  let SG : Subgroup G := (S : Subgroup G)
  let U : Subgroup G := subgroupNormalizerIn M (SG : Set G)
  have hS_le_N : SG ≤ Subgroup.normalizer (SG : Set G) := by
    simpa [SG] using (Subgroup.le_normalizer : (S : Subgroup G) ≤
      Subgroup.normalizer (((S : Subgroup G) : Set G)))
  have hS_le_M : SG ≤ M := by
    intro x hx
    exact (hNleHM (hS_le_N hx)).2
  have hS_le_H : SG ≤ H := by
    intro x hx
    exact (hNleHM (hS_le_N hx)).1
  have hSne : SG ≠ ⊥ := by
    intro hbot
    have htop_le_M : (⊤ : Subgroup G) ≤ M := by
      intro x _hx
      have hxN : x ∈ Subgroup.normalizer (SG : Set G) := by
        rw [Subgroup.mem_normalizer_iff]
        intro y
        simp [hbot]
      exact (hNleHM hxN).2
    exact hM.1 (top_le_iff.mp htop_le_M)
  let SM : Sylow q.val M := S.subtype hS_le_M
  have hSMmap : (SM : Subgroup M).map M.subtype = SG := by
    change ((S : Subgroup G).subgroupOf M).map M.subtype = (S : Subgroup G)
    exact Subgroup.map_subgroupOf_eq_of_le (G := G) (H := (S : Subgroup G)) (K := M) hS_le_M
  have hq_dvd_S : q.val ∣ Nat.card SG := by
    rcases S.isPGroup'.card_eq_or_dvd with hcard | hdiv
    · exact False.elim (hSne ((Subgroup.card_eq_one (H := SG)).mp (by simpa [SG] using hcard)))
    · simpa [SG] using hdiv
  have hqM : q ∈ subgroupPrimeSet M := by
    simpa [subgroupPrimeSet] using hq_dvd_S.trans (Subgroup.card_dvd_of_le hS_le_M)
  have hqσ : q ∈ section10SigmaPrimes M := by
    refine ⟨hqM, SM, ?_⟩
    intro x hx
    exact (hNleHM (by simpa [section10AmbientSylowSubgroup, hSMmap, SG] using hx)).2
  have hSM_le_D : (SM : Subgroup M) ≤ derivedSubgroup M :=
    section10_sigma_sylow_le_derivedSubgroup hM hqσ SM
  let Dg : Subgroup G := ambientDerivedSubgroup M
  have hS_le_Dg : SG ≤ Dg := by
    intro x hx
    have hxmap : x ∈ (SM : Subgroup M).map M.subtype := by
      simpa [hSMmap] using hx
    rcases Subgroup.mem_map.mp hxmap with ⟨xM, hxSM, rfl⟩
    change ((xM : M) : G) ∈ ambientDerivedSubgroup M
    exact ⟨xM, hSM_le_D hxSM, rfl⟩
  let XD : Sylow q.val Dg := S.subtype hS_le_Dg
  have hXDmap : section10AmbientSylowSubgroup Dg XD = SG := by
    change ((S : Subgroup G).subgroupOf Dg).map Dg.subtype = (S : Subgroup G)
    exact Subgroup.map_subgroupOf_eq_of_le (G := G) (H := (S : Subgroup G)) (K := Dg) hS_le_Dg
  have hKUlocal :
      section10MbetaSubgroup M ⊔ (U.subgroupOf M) = ⊤ := by
    simpa [U, SG, Dg, hXDmap] using
      section10_mbeta_sup_ambient_normalizer_of_derived_sylow
        (G := G) hM XD
  have hU_le_M : U ≤ M := by
    simpa [U, SG] using section10_subgroupNormalizerIn_le M (SG : Set G)
  have hUmap : (U.subgroupOf M).map M.subtype = U := by
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      exact hy
    · intro hx
      exact ⟨⟨x, hU_le_M hx⟩, hx, rfl⟩
  have hMbetaU : section10Mbeta M ⊔ U = M := by
    calc
      section10Mbeta M ⊔ U =
          (section10MbetaSubgroup M ⊔ U.subgroupOf M).map M.subtype := by
        rw [Subgroup.map_sup]
        simp [section10Mbeta, hUmap]
      _ = (⊤ : Subgroup M).map M.subtype := by rw [hKUlocal]
      _ = M := by
        ext x
        constructor
        · rintro ⟨y, _hy, rfl⟩
          exact y.property
        · intro hx
          exact ⟨⟨x, hx⟩, trivial, rfl⟩
  have hU_le_HM : U ≤ H ⊓ M := by
    intro x hx
    exact hNleHM ((section10_mem_subgroupNormalizerIn.mp (by simpa [U, SG] using hx)).1)
  have hprod : H ⊓ M ⊔ section10Mbeta M = M := by
    apply le_antisymm
    · exact sup_le inf_le_right (by
        intro x hx
        rcases Subgroup.mem_map.mp hx with ⟨y, _hy, rfl⟩
        exact y.property)
    · intro x hxM
      have hx_sup : x ∈ section10Mbeta M ⊔ U := by
        simpa [hMbetaU] using hxM
      exact (sup_le le_sup_right (hU_le_HM.trans le_sup_left)) hx_sup
  have hUproper : U ≠ ⊤ := by
    intro hUtop
    have htop_le_M : (⊤ : Subgroup G) ≤ M := by
      intro x hx
      exact hU_le_M (by simp [hUtop])
    exact hM.1 (top_le_iff.mp htop_le_M)
  have hUnot_unique : U ∉ section9UniqueSubgroups G :=
    section10_not_unique_of_le_two_distinct_maximal
      (G := G) hM hH hU_le_M (hU_le_HM.trans inf_le_left) hHM
  have hq_not_alpha : q ∉ section10AlphaPrimes M := by
    intro hqα
    have hSMrank : 3 ≤ groupRank (SM : Subgroup M) := by
      have hprime : 3 ≤ primeRank q.val M := Nat.succ_le_of_lt hqα.2
      exact hprime.trans (section10_primeRank_le_groupRank_sylow_pre (G := M) SM)
    have hSrank : 3 ≤ groupRank SG := by
      let eS : (SM : Subgroup M) ≃* SG :=
        (Subgroup.equivMapOfInjective (SM : Subgroup M) M.subtype M.subtype_injective).trans
          (MulEquiv.subgroupCongr hSMmap)
      exact hSMrank.trans
        (section10_groupRank_le_of_equiv_pre (R := SG) (S := (SM : Subgroup M)) eS.symm)
    have hSproper : SG ≠ ⊤ := by
      intro htop
      have htop_le_M : (⊤ : Subgroup G) ≤ M := by
        intro x hx
        exact hS_le_M (by simp [htop])
      exact hM.1 (top_le_iff.mp htop_le_M)
    have hSunique : SG ∈ section9UniqueSubgroups G :=
      theorem_9_6 (K := SG) hSproper (by omega) (Or.inl hSrank)
    have hS_le_U : SG ≤ U := by
      simpa [U, SG] using section10_le_subgroupNormalizerIn hS_le_M
    exact hUnot_unique (section9_unique_of_le hS_le_U hUproper hSunique)
  have hqβ : q ∉ section10BetaPrimes M := by
    intro hqβ
    exact hq_not_alpha (section10_beta_subset_alpha (G := G) M hqβ)
  have hC_le_U :
      subgroupCentralizerIn M SG ≤ U := by
    intro x hx
    change x ∈ subgroupNormalizerIn M (SG : Set G)
    rw [section10_mem_subgroupNormalizerIn]
    exact ⟨centralizer_le_normalizer SG hx.2, hx.1⟩
  have halpha_subset_beta : section10AlphaPrimes M ⊆ section10BetaPrimes M := by
    intro r hrα
    by_contra hrβ
    by_cases hrq : r = q
    · exact hq_not_alpha (by simpa [hrq] using hrα)
    · have hCunique : subgroupCentralizerIn M SG ∈ section9UniqueSubgroups G :=
        corollary_10_9_a_2
          (G := G) (M := M) (X := SG) (p := r) (q := q)
          hM hrα.1 hqM hrβ hqβ hrq hS_le_M S.isPGroup'
          (Or.inl hS_le_Dg) hrα
      exact hUnot_unique (section9_unique_of_le hC_le_U hUproper hCunique)
  exact ⟨hprod, Set.Subset.antisymm halpha_subset_beta (section10_beta_subset_alpha (G := G) M)⟩
