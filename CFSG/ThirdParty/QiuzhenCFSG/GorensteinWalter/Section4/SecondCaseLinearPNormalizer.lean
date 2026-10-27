module

public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section4.SecondCaseLinearP0CentralizerTorus
import Mathlib.Tactic

namespace CFSG
end CFSG
open CFSG

/-!
# The normalizer of the selected order-`p` subgroup

The cyclic fixed factor `F` has normalizer `M`, and every order-`p`
subgroup `P ≤ F` is fixed by the normalizer of `F`.  The TI property of
`F` gives the converse inclusion, hence `N_G(P)=M`.
-/

noncomputable section

namespace CFSG.GorensteinWalter

universe u

/-- The selected order-`p` subgroup has the ambient normalizer `M`. -/
public theorem secondCase_linear_P_normalizer_eq_M
    {G : Type u} [Group G] [Finite G]
    (c : CentralizerSetup G) (w : SecondCaseWitness c)
    (d : SecondCaseComponentData w)
    (od : SecondCaseLinearOmegaData c w d) :
    Subgroup.normalizer (od.P : Set G) = w.M := by
  apply le_antisymm
  · intro g hg
    by_contra hnotM
    have hFconj : od.P ≤ conjugateSubgroup od.F g := by
      intro p hp
      have hpre : g⁻¹ * p * g ∈ od.P := by
        apply (Subgroup.mem_normalizer_iff.mp hg (g⁻¹ * p * g)).mpr
        have hconj : g * (g⁻¹ * p * g) * g⁻¹ = p := by group
        rw [hconj]
        exact hp
      exact Subgroup.mem_map.mpr ⟨g⁻¹ * p * g, od.P_le_F hpre, by
        simp [MulAut.conj_apply, mul_assoc]⟩
    have hPleInf : od.P ≤ od.F ⊓ conjugateSubgroup od.F g :=
      le_inf od.P_le_F hFconj
    have hPne : od.P ≠ ⊥ := by
      intro hbot
      have hcard : Nat.card od.P = 1 := by rw [hbot]; simp
      exact od.hp_prime.ne_one (od.P_card.symm.trans hcard)
    exact hPne (le_bot_iff.mp (by
      rw [od.F_TI g hnotM] at hPleInf
      exact hPleInf))
  · intro g hg
    exact prime_order_subgroup_fixed_by_normalizer_of_cyclic od.F_cyclic od.P_le_F
      od.hp_prime od.P_card ((le_normalizer_of_isNormalIn od.F_normal_M) hg)

end CFSG.GorensteinWalter
