module

public import CFSG.RankThree.PartOne.S11c.Sec66TFamily
public import CFSG.RankThree.PartOne.S11c.Sec66TModelsTw
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCatalogLargeReeModel

public section

namespace CFSG.RankThree.PartOne.Sec66T

open CFSG CFSG.Blueprint CFSG.LieType.Ree CFSG.LieType.Ree.ReeTag
open CFSG.ComponentClassification.OuterAutomorphisms (Outer)
open CFSG.ComponentClassification.UnbalancedCatalog
  (large_Ree_model_field_outer_group_and_inner_involutions)
open CFSG.Assembly.LowTwoRank (StatedLieTag StatedLieAdmissible)

@[expose] def LargeReeFieldAutCoset :
    Prop :=
  ∀ (a : ℕ), 1 ≤ a → ∀ (K : Type) [Field K] [Finite K] [CharP K F4.prime],
    Nat.card K = 2 ^ (2 * a + 1) → ∀ (p : ℕ), p.Prime → 5 ≤ p →
      ∀ β : K ≃+* K, orderOf β = p → ∀ α : MulAut (F4.reeGamma K a), α ^ p = 1 →
        (∃ x : F4.reeGamma K a, α = MulAut.conj x * F4.reeGammaFieldAut K a β) →
        ∃ g : F4.reeGamma K a,
          α = MulAut.conj g * F4.reeGammaFieldAut K a β * (MulAut.conj g)⁻¹

theorem sec66T_K2_twistedF4 :
    Sec66T_K2 .twistedF4 := by
  intro T _ _ p hp hp5 hmodel _ E hE hcard hEinn _hra
  obtain ⟨n, f, hadm, hM⟩ := hmodel
  have hR : ReeTitsModel T .twistedF4 2 f := (lieModel_twistedF4_iff.mp hM).2
  obtain ⟨-, -, -, hcyc, -⟩ := large_Ree_model_field_outer_group_and_inner_involutions T 2 f hR
  let π : MulAut T →* Outer T :=
    QuotientGroup.mk' (CFSG.ComponentClassification.OuterAutomorphisms.inner T)
  refine no_plane_of_cyclic_quotient hp π ?_ E hE hcard hEinn
  intro x hx _
  have hxi : x ∈ CFSG.ComponentClassification.OuterAutomorphisms.inner T :=
    (QuotientGroup.eq_one_iff x).mp hx
  exact hxi

end CFSG.RankThree.PartOne.Sec66T
