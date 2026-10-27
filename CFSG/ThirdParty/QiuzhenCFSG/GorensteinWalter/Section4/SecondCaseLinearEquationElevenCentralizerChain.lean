module

public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section4.SecondCaseLinearEquationElevenAligned
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section4.SecondCaseLinearP0CentralizerTorus
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section4.SecondCaseLinearPInterE
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section4.SecondCaseLinearPNormalizer
import Mathlib.Tactic

namespace CFSG
end CFSG
open CFSG

/-!
# Equation (11): the exact `P₀`-centralizer chain

The original aligned-chain theorem names the internal subgroup as
`K ⊔ S₀` and consequently asks for the stronger ambient equality
`C_E(P₀) = K ⊔ S₀`.  The available PSL₂ endpoint proves the exact quotient
image of `C_E(P₀)`, but not that stronger preimage equality.  This adapter
instantiates the same proved chain with
`C := C_E(P₀)` and the trivial second factor.  It retains the exact
normalizer/intersection information while avoiding an unsupported lift.
-/

noncomputable section

namespace CFSG.GorensteinWalter

universe u

/-- The first aligned equation-(11) chain with the exact centralizer of `P₀`
used as the internal torus lift.  The hypotheses `hAh` and `hXh` are the
already-aligned conjugate data; no equality `C_E(P₀) = K ⊔ S₀` is assumed. -/
public theorem secondCase_linearEquation11_first_identity_chain_of_P0_centralizer
    {G : Type u} [Group G] [Finite G]
    (hmin : IsMinimalCounterexample G)
    (c : CentralizerSetup G) (w : SecondCaseWitness c)
    (d : SecondCaseComponentData w)
    (K : Type u) [Field K] [Finite K]
    (hK : IsOddPrimePower (Nat.card K))
    (e : Nonempty ((d.E ⧸ Subgroup.center d.E) ≃* PSL2 K))
    (post : SecondCaseLinearPostNineData c w d K)
    (hZ : Subgroup.center d.E = ⊥)
    {Xh : Subgroup G} (h : G)
    (hXh : Xh = conjugateSubgroup post.od.P h)
    (hXh_le_A : Xh ≤ post.od.A) (hXh_ne_P : Xh ≠ post.od.P)
    (hAh : conjugateSubgroup post.od.A h = post.od.A)
    (hP_notConjP0 : ¬ ∃ z : G, conjugateSubgroup post.od.P z = post.od.P0) :
    (conjugateSubgroup w.M h ⊓ (post.od.P ⊔ d.E) =
        (post.od.P ⊔ d.E) ⊓ Subgroup.normalizer (Xh : Set G)) ∧
      ((post.od.P ⊔ d.E) ⊓ Subgroup.normalizer (Xh : Set G) =
        post.od.P ⊔ (Subgroup.centralizer (post.od.P0 : Set G) ⊓ d.E)) ∧
      (post.od.P ⊔ (Subgroup.centralizer (post.od.P0 : Set G) ⊓ d.E) =
        (post.od.P ⊔ d.E) ⊓ Subgroup.centralizer (post.od.A : Set G)) ∧
      (d.E ⊓ Subgroup.normalizer (Xh : Set G) =
        Subgroup.centralizer (post.od.P0 : Set G) ⊓ d.E) := by
  classical
  let C : Subgroup G := Subgroup.centralizer (post.od.P0 : Set G) ⊓ d.E
  have hP0leE : post.od.P0 ≤ d.E := by
    exact post.od.P0_le_K0.trans (by
      rw [post.od.K0_eq]
      exact inf_le_right.trans post.od.K_le_E)
  have hCsubE : C ≤ d.E := by
    exact inf_le_right
  have hCmap : ((C.subgroupOf d.E).map
      (QuotientGroup.mk' (Subgroup.center d.E))) = post.torus.T := by
    exact secondCase_linear_P0_centralizer_eq_torus c w d K post hZ
  let q : d.E →* (d.E ⧸ Subgroup.center d.E) :=
    QuotientGroup.mk' (Subgroup.center d.E)
  have hqker : q.ker = ⊥ := by
    rw [show q = QuotientGroup.mk' (Subgroup.center d.E) by rfl,
      QuotientGroup.ker_mk', hZ]
  have hqinj : Function.Injective q :=
    (MonoidHom.ker_eq_bot_iff q).mp hqker
  have hCsubcyc : IsCyclic (↥(C.subgroupOf d.E)) := by
    let eC := Subgroup.equivMapOfInjective (C.subgroupOf d.E) q hqinj
    have himage : IsCyclic (↥((C.subgroupOf d.E).map q)) := by
      rw [hCmap]
      exact post.torus.T_cyclic
    exact (MulEquiv.isCyclic eC).mpr himage
  have hCcyc : IsCyclic C := by
    have eC : (C.subgroupOf d.E) ≃* C :=
      Subgroup.subgroupOfEquivOfLe inf_le_right
    exact (MulEquiv.isCyclic eC).mp hCsubcyc
  have hFleFU : post.od.F ≤ fittingSubgroupOf c.U := by
    intro x hx
    rw [post.od.F_fixed] at hx
    exact hx.1.1
  have hK0leFU : post.od.K0 ≤ fittingSubgroupOf c.U := by
    rw [post.od.K0_eq]
    exact inf_le_left
  have hPinterE : post.od.P ⊓ d.E = ⊥ :=
    secondCase_linear_P_inf_E_eq_bot hmin c w d K hK e post
  have hC0E : (Subgroup.centralizer (post.od.P0 : Set G)) ⊓ d.E =
      C ⊔ (⊥ : Subgroup G) := by
    simp [C]
  have hchain := secondCase_linearEquation11_first_identity_chain c w d
    C post.od.K0 post.od.F post.od.P post.od.P0 post.od.A (⊥ : Subgroup G)
    post.od.hp_prime post.od.P_card post.od.P0_card post.od.P_le_F hFleFU hK0leFU
    post.od.F_centralizes_E hPinterE post.od.P0_le_K0 (by
      rw [post.od.K0_eq]
      exact inf_le_right.trans post.od.K_le_E) hCsubE hCcyc
    (secondCase_linear_P_normalizer_eq_M c w d post.od)
    post.od.A_eq hC0E (by exact bot_le) (by exact bot_le) hP_notConjP0 Xh hXh
    hXh_le_A hXh_ne_P hAh
  simpa [C, sup_bot_eq] using hchain

end CFSG.GorensteinWalter
