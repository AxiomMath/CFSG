module

public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.SE.IG1114

namespace CFSG
end CFSG
open CFSG

/-!
# Normalizers of subgroup commutators

The source proof of Gorenstein--Walter Theorem 2.6 chooses an
`H`-invariant subgroup `P` with `H ≤ C_G(t)`.  This small interface records
that the commutator subgroup `[P, ⟨t⟩]` is again `H`-invariant.
-/

namespace CFSG.GorensteinWalter

universe u

/-- A subgroup normalizing both inputs normalizes their subgroup
commutator. -/
public theorem le_normalizer_commutator_of_le_normalizer
    {G : Type u} [Group G]
    (H P Q : Subgroup G)
    (hHP : H ≤ Subgroup.normalizer (P : Set G))
    (hHQ : H ≤ Subgroup.normalizer (Q : Set G)) :
    H ≤ Subgroup.normalizer ((⁅P, Q⁆ : Subgroup G) : Set G) := by
  intro h hh
  rw [Subgroup.mem_normalizer_iff_map_conj_eq]
  rw [Subgroup.map_commutator]
  rw [(Subgroup.mem_normalizer_iff_map_conj_eq.mp (hHP hh)),
    (Subgroup.mem_normalizer_iff_map_conj_eq.mp (hHQ hh))]

end CFSG.GorensteinWalter
