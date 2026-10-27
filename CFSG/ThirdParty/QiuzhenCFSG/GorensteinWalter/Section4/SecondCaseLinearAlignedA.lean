module

public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section4.SecondCaseLinearAUniqueElementary
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section4.SecondCaseLinearEquationElevenAlignedStabilizesA
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section4.SecondCaseLinearPostNineData
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section4.SecondCaseLinearPInterE
import Mathlib.Tactic

namespace CFSG
end CFSG
open CFSG

/-!
# Stabilization of the equation-(11) plane

This owner supplies the concrete inputs to the aligned plane-stabilization
lemma.  The only source-specific exclusion left at this interface is that the
external order-`p` subgroup is not conjugate to the internal order-`p`
subgroup `P₀`.
-/

noncomputable section

open scoped Pointwise

namespace CFSG.GorensteinWalter

universe u

/-- An aligned conjugate of `P` stabilizes `A`, using the elementary (rather
than falsely unrestricted) uniqueness of the order-`p²` subgroup in
`F ⊔ K₀`. -/
public theorem secondCase_linear_aligned_A_conjugate_eq_A
    {G : Type u} [Group G] [Finite G]
    (hmin : IsMinimalCounterexample G)
    (c : CentralizerSetup G) (w : SecondCaseWitness c)
    (d : SecondCaseComponentData w)
    (K : Type u) [Field K] [Finite K]
    (hK : IsOddPrimePower (Nat.card K))
    (e : Nonempty ((d.E ⧸ Subgroup.center d.E) ≃* PSL2 K))
    (post : SecondCaseLinearPostNineData c w d K)
    (hP_notConjP0 : ¬ ∃ z : G, conjugateSubgroup post.od.P z = post.od.P0)
    {X : Subgroup G} {h : G}
    (hXleA : X ≤ post.od.A) (hXneP : X ≠ post.od.P)
    (hX : X = conjugateSubgroup post.od.P h)
    (hfix : h * c.t * h⁻¹ = c.t) :
    conjugateSubgroup post.od.A h = post.od.A := by
  have hPinterE : post.od.P ⊓ d.E = ⊥ :=
    secondCase_linear_P_inf_E_eq_bot hmin c w d K hK e post
  let : IsCyclic (↥post.od.K) := post.od.K_cyclic
  have hK0leE : post.od.K0 ≤ d.E := by
    rw [post.od.K0_eq]
    exact inf_le_right.trans post.od.K_le_E
  have hPLeCGE : post.od.P ≤ Subgroup.centralizer (d.E : Set G) :=
    post.od.P_le_F.trans post.od.F_centralizes_E
  have hF0 : post.od.F ⊓ post.od.K0 = ⊥ :=
    secondCase_linear_omega_F_cap_K0 c w d post.od
  have hFcomm : IsMulCommutative (↥post.od.F) := by
    let : IsCyclic (↥post.od.F) := post.od.F_cyclic
    exact IsCyclic.isMulCommutative
  have hK0comm : IsMulCommutative (↥post.od.K0) := by
    let : IsCyclic (↥post.od.K0) := by
      rw [post.od.K0_eq]
      exact Subgroup.isCyclic_of_le (H' := post.od.K) inf_le_right
    exact IsCyclic.isMulCommutative
  have hcross : ∀ f k, f ∈ post.od.F → k ∈ post.od.K0 → Commute f k := by
    intro f k hf hk
    have hfcent := post.od.F_centralizes_E hf
    exact (Subgroup.mem_centralizer_iff.mp hfcent) k (hK0leE hk) |>.symm
  have hFK0ab : IsMulCommutative (↥(post.od.F ⊔ post.od.K0)) :=
    subgroup_sup_isMulCommutative_of_commute_of_disjoint
      post.od.F post.od.K0 hF0 hcross hFcomm hK0comm
  have hCP : (Subgroup.centralizer (post.od.P : Set G)) ⊓ c.FU =
      post.od.F ⊔ post.od.K0 :=
    secondCase_linear_P_centralizer_FU_eq_sup c w d post.od
  have hAuniq : ∀ B : Subgroup G, B ≤ post.od.F ⊔ post.od.K0 →
      IsElementaryAbelian post.od.p B → Nat.card B = post.od.p ^ 2 → B = post.od.A :=
    secondCase_linear_A_unique_elementary c w d post.od
  exact secondCase_equation11_aligned_A_conjugate_eq_A
    c w d post.od.F post.od.K0 post.od.P post.od.P0 post.od.A X h
    post.od.hp_prime post.od.P_card post.od.P0_card hPLeCGE hPinterE
    post.od.P0_le_K0 hK0leE hXleA post.od.A_eq post.od.P_le_F hFK0ab hCP
    (secondCase_linear_conjugate_P_centralizer_FU_eq c w d post.od h hX hfix)
    post.od.A_elem_abelian hAuniq

end CFSG.GorensteinWalter
