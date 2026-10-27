module

public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.BGsection12.corollary_12_14

namespace CFSG
end CFSG
open CFSG

open scoped Pointwise

/-!
# proposition_12_15_a
-/

section Section12

variable {G : Type*} [Group G] [Finite G] [IsMinCE G]

/-- Proposition 12.15(a). -/
public theorem CFSG.proposition_12_15_a
    {M Mstar X : Subgroup G} {q : Nat.Primes}
    {S : Sylow q.val (M ⊓ Mstar : Subgroup G)}
    (hM : M ∈ section9MaximalSubgroups G)
    (hq : q ∈ section10SigmaPrimes M)
    (hX : X ≤ M) (hXne : X ≠ ⊥) (hXq : IsPGroup q.val X)
    (hMstar : Mstar ∈ section9MaximalSubgroupsContaining (Subgroup.normalizer (X : Set G)))
    (hMstar_ne : Mstar ≠ M)
    (_hXS : X ≤ section10AmbientSylowSubgroup (M ⊓ Mstar) S) :
    section12NotConjugate Mstar M := by
  exact lemma_12_2_b (G := G) (M := M) (Mstar := Mstar) (X := X) (p := q)
    hM hXq hXne hX hMstar (Or.inl ⟨hq, hMstar_ne.symm⟩)

end Section12
