module

public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section4.SecondCaseLinearCardBound
import Mathlib.Tactic

namespace CFSG
end CFSG
open CFSG

/-!
# The numerical contradiction for the outer-involution branch

The source's proof that the ambient Sylow lies in the selected component ends
with an odd reflected subgroup `R` whose order is the odd complementary half
`k'`.  Equation (8) bounds the relative index of
`L := B ⊔ K ⊔ F(U)` in `U` by the prime `p`, while the preceding source
argument gives `R ≤ U` and `R ∩ L = 1`.  The cardinal lemma in the preceding
module then gives `|R| ≤ p`; the half-size inequalities give `p < k'`.
-/

noncomputable section

namespace CFSG.GorensteinWalter

universe u

/-- The order of the odd reflected subgroup cannot fit in the equation-(8)
index. -/
public theorem secondCase_linear_reflected_card_contradiction
    {G : Type u} [Group G] [Finite G]
    (U L R : Subgroup G) (p q k k' : ℕ)
    (hRleU : R ≤ U) (hdisj : Disjoint L R)
    (hrel : L.relIndex U ≤ p)
    (hRcard : Nat.card R = k')
    (hq : 7 ≤ q) (hk : k ≤ (q + 1) / 2)
    (hpk : 2 * p ≤ k) (hk' : (q - 1) / 2 ≤ k') :
    False := by
  have hRle : Nat.card R ≤ L.relIndex U :=
    secondCase_linear_card_le_relIndex_of_disjoint_normalizer
      U L R hRleU hdisj
  have hRlep : Nat.card R ≤ p := hRle.trans hrel
  rw [hRcard] at hRlep
  have hp_lt_k' : p < k' := by
    omega
  omega

end CFSG.GorensteinWalter
