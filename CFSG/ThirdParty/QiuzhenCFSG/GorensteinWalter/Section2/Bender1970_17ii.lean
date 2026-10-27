module

public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section2.Bender1970API
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section2.ControlCore
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section2.FStarSubnormal
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section2.Bender1970_17i

namespace CFSG
end CFSG
open CFSG

/-!
# Bender (1970), Statement 1.7(ii)

The statement is the second conjunct of
`GorensteinWalter.Section2.Bender1970_17i.bender1970_1_7_residual_commutator_assembly`
(the paper-faithful two-conjunct form; the old unconditional `F*(B) ≤ A`
third conjunct was removed as false — see `tasks/gw-bender1970-17.md`,
R-statement-drift).
-/

noncomputable section

open scoped Pointwise commutatorElement

namespace CFSG.GorensteinWalter

universe u

/-- Bender [1], Statement 1.7(ii): for `p ∈ π(F(A))`,
`[O_p(B), O^p(F*(A))] = 1`. -/
public theorem bender1970_1_7_ii_commutator_pResidual
    {G : Type u} [Group G] [Finite G]
    (hsimple : IsSimpleGroup G)
    (A : Subgroup G) (hA : IsCoatom A)
    (S : Subgroup G)
    (hSF : S ≤ generalizedFittingSubgroupOf A)
    (hSsub : (S.subgroupOf (generalizedFittingSubgroupOf A)).IsSubnormal)
    (hCS : generalizedFittingSubgroupOf A ⊓ Subgroup.centralizer (S : Set G) ≤ S)
    {B : Subgroup G} (hSB : S ≤ B) :
    ∀ p : ℕ, p.Prime → p ∈ primesOfOrder (fittingSubgroupOf A) →
      ⁅qCoreOf B p, pResidualOf (generalizedFittingSubgroupOf A) p⁆ = ⊥ := by
  intro p hp hpin
  exact (bender1970_1_7_residual_commutator_assembly
    hsimple A hA S hSF hSsub hCS hSB).2 p hp hpin

end CFSG.GorensteinWalter
