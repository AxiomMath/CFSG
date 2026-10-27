module

public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.BGsection10.proposition_10_11_d
import Mathlib.GroupTheory.Schreier
import Mathlib.LinearAlgebra.Projectivization.Cardinality

namespace CFSG
end CFSG
open CFSG

open scoped Pointwise

/-!
# Lemma 10.12(a) from BG Section 10

This file contains Lemma 10.12(a) from BG Section 10.
-/

section Section10

variable {G : Type*} [Group G] [Finite G] [IsMinCE G]

private theorem CFSG.section10_alpha_sigma_primes_disjoint_of_nonconj
    {M H : Subgroup G} (hM : M ∈ section9MaximalSubgroups G)
    (hH : H ∈ section9MaximalSubgroups G) (hconj : ∀ g : G, H.conjBy g ≠ M) :
    Disjoint (section10AlphaPrimes M) (section10SigmaPrimes H) := by
  classical
  rw [Set.disjoint_left]
  intro p hpα hpσH
  haveI : Fact p.val.Prime := ⟨p.property⟩
  let P : Sylow p.val M := Classical.choice (Sylow.nonempty (p := p.val) (G := M))
  let PG : Subgroup G := section10AmbientSylowSubgroup M P
  have hPGp : IsPGroup p.val PG := by
    change IsPGroup p.val ((P : Subgroup M).map M.subtype)
    exact IsPGroup.map (p := p.val) (H := (P : Subgroup M)) P.isPGroup' M.subtype
  have hPG_le_M : PG ≤ M := by
    simpa [PG] using section10_ambient_sylow_le_base (G := G) P
  rcases section10_exists_conjBy_le_of_isPGroup_of_sigma
      (G := G) (M := H) (Y := PG) hpσH hPGp with
    ⟨a, hPG_le_Ha⟩
  have hHa : H.conjBy a ∈ section9MaximalSubgroups G :=
    section10_maximal_conjBy hH a
  have hPG_not_unique : PG ∉ section9UniqueSubgroups G :=
    section10_not_unique_of_le_two_distinct_maximal
      (G := G) hM hHa hPG_le_M hPG_le_Ha (hconj a)
  have hPrank : 3 ≤ groupRank (P : Subgroup M) := by
    have hprime : 3 ≤ primeRank p.val M := Nat.succ_le_of_lt hpα.2
    exact hprime.trans (section10_primeRank_le_groupRank_sylow_pre (G := M) P)
  let ePG : (P : Subgroup M) ≃* PG :=
    Subgroup.equivMapOfInjective
      (f := M.subtype) (P : Subgroup M) M.subtype_injective
  have hPGrank : 3 ≤ groupRank PG :=
    hPrank.trans
      (section10_groupRank_le_of_equiv_pre
        (R := PG) (S := (P : Subgroup M)) ePG.symm)
  have hPGproper : PG ≠ ⊤ := by
    intro htop
    have htop_le_M : (⊤ : Subgroup G) ≤ M := by
      intro x hx
      exact hPG_le_M (by simp [htop])
    exact hM.1 (top_le_iff.mp htop_le_M)
  have hPGunique : PG ∈ section9UniqueSubgroups G :=
    theorem_9_6 (K := PG) hPGproper (by omega) (Or.inl hPGrank)
  exact hPG_not_unique hPGunique

/-- Lemma 10.12(a). -/
public theorem CFSG.lemma_10_12_a
    {M H : Subgroup G} (hM : M ∈ section9MaximalSubgroups G)
    (hH : H ∈ section9MaximalSubgroups G) (hconj : ∀ g : G, H.conjBy g ≠ M) :
    Disjoint (section10Malpha M) (section10Msigma H) ∧
      Disjoint (section10AlphaPrimes M) (section10SigmaPrimes H) := by
  classical
  have hprimes : Disjoint (section10AlphaPrimes M) (section10SigmaPrimes H) :=
    section10_alpha_sigma_primes_disjoint_of_nonconj hM hH hconj
  exact
    ⟨section10_disjoint_of_hall_disjoint_primes
        (theorem_10_2_a (G := G) hM).1 (theorem_10_2_b (G := G) hH).1 hprimes,
      hprimes⟩

end Section10
