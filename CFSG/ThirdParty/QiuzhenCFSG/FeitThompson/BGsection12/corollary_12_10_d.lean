module

public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.BGsection12.corollary_12_10_c

namespace CFSG
end CFSG
open CFSG

open scoped Pointwise

/-!
# corollary_12_10_d
-/

section Section12

variable {G : Type*} [Group G] [Finite G] [IsMinCE G]

/-- Corollary 12.10(d). -/
public theorem CFSG.corollary_12_10_d
    {M P : Subgroup G} {p : Nat.Primes}
    (hM : M ∈ section9MaximalSubgroups G)
    (hp : p ∈ section10SigmaPrimes M)
    (hPp : IsPGroup p.val P) (hPle : P ≤ M) (hPnoncyc : ¬ IsCyclic P) :
    Subgroup.normalizer (P : Set G) ≤ M := by
  classical
  obtain ⟨A, hA_P⟩ :=
    section12_exists_rankTwo_in_noncyclic_pSubgroup (G := G) (P := P) (p := p)
      hPp hPnoncyc
  have hA_M : A ∈ section12RankTwoElementaryAbelianIn p M :=
    section12_rankTwo_mono hA_P hPle
  have hA_le_P : A ≤ P := section12_rankTwo_le hA_P
  have hCentP_le_M : Subgroup.centralizer (P : Set G) ≤ M :=
    (Subgroup.centralizer_le (show (A : Set G) ⊆ (P : Set G) from hA_le_P)).trans
      (proposition_12_4_a (G := G) (M := M) (A := A) (p := p) hM hA_M)
  have hPne : P ≠ ⊥ := by
    intro hPbot
    apply hPnoncyc
    subst P
    exact isCyclic_of_subsingleton (α := (⊥ : Subgroup G))
  have hnorm_eq :
      Subgroup.normalizer (P : Set G) =
        subgroupNormalizerIn M (P : Set G) ⊔ Subgroup.centralizer (P : Set G) :=
    theorem_10_1_c (G := G) (M := M) (X := P) (p := p) hM hp hPne hPp hPle
  rw [hnorm_eq]
  refine sup_le ?_ hCentP_le_M
  intro x hx
  have hx' : x ∈ Subgroup.normalizer (P : Set G) ⊓ M := by
    simpa [subgroupNormalizerIn] using hx
  exact hx'.2

end Section12
