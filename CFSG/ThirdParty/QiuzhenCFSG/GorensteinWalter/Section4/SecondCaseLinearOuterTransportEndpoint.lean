module

public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section4.SecondCasePSL2OuterInvolutionTransport
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section4.SecondCaseLinearOuterTransfer
import Mathlib.Tactic

namespace CFSG
end CFSG
open CFSG

/-!
# The reflected odd subgroup in the ambient odd core

This is the local source endpoint after the model pair has been aligned.  The
PSL₂ transport supplies the subgroup `R = [⟨t⟩, C_E(r)]`; a product-centralizer
conjugator transfers it to an odd subgroup of `U`, preserving its cardinality
and inversion by `r`.
-/

noncomputable section

namespace CFSG.GorensteinWalter

universe u

/-- Combine the PSL₂ reflected-commutator transport with the ambient
odd-subgroup transfer. -/
public theorem secondCase_linear_outer_transport_endpoint
    {G : Type u} [Group G] [Finite G]
    (hmin : IsMinimalCounterexample G)
    {c : CentralizerSetup G} (w : SecondCaseWitness c)
    (d : SecondCaseComponentData w)
    (K : Type u) [Field K] [Finite K]
    (ad : SecondCasePSL2ActionData w d K)
    (P : Sylow 2 (PGL2 K)) {m : ℕ}
    (eP : P ≃* DihedralGroup (2 ^ m))
    (T : PGL2LowReflectedToriData K P eP)
    (r : w.M) (hrI : IsInvolution (r : G))
    (hrE : (r : G) ∉ d.E) (htr : Commute c.t (r : G))
    (r0 t0 a : PGL2 K)
    (hr0 : ad.f r = SemidirectProduct.inl r0)
    (ht0 : ad.f ⟨c.t, d.E_component.1 d.t_mem_E⟩ =
      SemidirectProduct.inl t0)
    (hrT : r0 = a * T.s * a⁻¹)
    (htT : t0 = a * T.t * a⁻¹)
    (y : G) (hyconj : y * (r : G) * y⁻¹ = c.t)
    (hyC : y ∈ Subgroup.centralizer ({c.t * (r : G)} : Set G)) :
    let CE : Subgroup G :=
      Subgroup.centralizer ({(r : G)} : Set G) ⊓ d.E
    let R : Subgroup G := ⁅Subgroup.zpowers c.t, CE⁆
    let Ry : Subgroup G := R.map (MulAut.conj y).toMonoidHom
    IsCyclic R ∧ Odd (Nat.card R) ∧ Nat.card R = Nat.card T.U / 2 ∧
      Ry ≤ c.U ∧
        (∀ x : G, x ∈ Ry → (r : G) * x * (r : G)⁻¹ = x⁻¹) := by
  classical
  intro CE R Ry
  obtain ⟨hRcyc, hRodd, hRcard, hRinv, _hRmap⟩ :=
    secondCase_psl2_outer_involution_transport w d K ad P eP T r hrI hrE
      htr r0 t0 a hr0 ht0 hrT htT
  have htCE : Subgroup.zpowers c.t ≤ CE := by
    intro x hx
    rw [Subgroup.mem_inf]
    refine ⟨?_, ?_⟩
    · rw [Subgroup.mem_centralizer_singleton_iff]
      have hxt : Commute x (r : G) := by
        rcases Subgroup.mem_zpowers_iff.mp hx with ⟨n, rfl⟩
        exact htr.zpow_left n
      exact hxt.eq
    · rcases Subgroup.mem_zpowers_iff.mp hx with ⟨n, rfl⟩
      exact d.E.zpow_mem d.t_mem_E n
  have hRleCE : R ≤ CE := by
    apply Subgroup.commutator_le.mpr
    intro x hx y hy
    have hxCE : x ∈ CE := htCE hx
    change x * y * x⁻¹ * y⁻¹ ∈ CE
    exact CE.mul_mem (CE.mul_mem (CE.mul_mem hxCE hy) (CE.inv_mem hxCE))
      (CE.inv_mem hy)
  have hRcent : R ≤ Subgroup.centralizer ({(r : G)} : Set G) :=
    hRleCE.trans inf_le_left
  have hytr : Commute y (c.t * (r : G)) := by
    have h := Subgroup.mem_centralizer_singleton_iff.mp hyC
    change y * (c.t * (r : G)) = (c.t * (r : G)) * y
    exact h
  have htransfer := secondCase_linear_outer_subgroup_transfer hmin c R hRcent
    hRodd hyconj htr hytr hRinv
  refine ⟨hRcyc, hRodd, hRcard, htransfer.1, htransfer.2⟩

end CFSG.GorensteinWalter
