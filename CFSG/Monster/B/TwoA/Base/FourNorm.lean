module

public import CFSG.Monster.B.TwoA.Base.FourNormBase
public import CFSG.Monster.B.Co2.Simple


public section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.Monster.B.TwoA

open CFSG.Monster CFSG.Monster.Code CFSG.Monster.Spin CFSG.Monster.SpinLattice
  CFSG.Monster.Griess CFSG.Monster.Visible CFSG.Monster.Generated CFSG.Monster.B.Short
  CFSG.Monster.B CFSG.Monster.VisQuot CFSG.Monster.ScalarKernel CFSG.Monster.B.Co2

open scoped commutatorElement

theorem index_M_in :

    ((monoSub ceqHyp).subgroupOf (Kstab (phi0 (coordOf rStar)))).index =
    46575 := by
  have h := ((monoSub ceqHyp).subgroupOf (Kstab (phi0 (coordOf rStar)))).card_mul_index
  rw [natCard_M_in, show Nat.card (Kstab (phi0 (coordOf rStar))) = 42305421312000 by
    rw [← natCard_Kv]; exact congrArg (fun H : Subgroup OLq => Nat.card H) Kstab_rStar_eq] at h
  omega

theorem index_P2J :
    P2J.index = 46575 := by
  rw [P2J, Subgroup.index_comap_of_surjective _ jhatToKv_surjective, index_M_in]

attribute [local instance] vAction

theorem full_short_triality_four_group_normalizer :
    Vhat ≤ Ehat ∧ IsKleinFour Vhat ∧
    (∀ d, d ∈ Vhat ↔ d = 1 ∨ d = xhat ∨ d = xhat * yhat ∨ d = yhat) ∧
    tauhat ^ 2 * xhat * (tauhat ^ 2)⁻¹ = yhat ∧
    psiBar ⟨zbar, zbar_mem_Ebar⟩ =
      Multiplicative.ofAdd (Submodule.Quotient.mk ⟨twoΩCls, twoΩCls_mem_vPerp_rStar⟩) ∧
    iotaD zbar = yhat ∧
    Ptwo.subgroupOf Jhat =
      ((monoSub ceqHyp).subgroupOf (Kstab (phi0 (coordOf rStar)))).comap jhatToKv ∧
    jhatToKv.ker = Ehat.subgroupOf Jhat ∧
    Nonempty (P2J ⧸ (jhatToKv.ker.subgroupOf P2J) ≃* Mfr) ∧
    Nat.card Ptwo = 7619615580487680 ∧
    Ntwo = Subgroup.closure (insert tauhat (Ptwo : Set Dfull)) ∧ Ntwo ≤ Shat ∧
    (Ptwo.subgroupOf Ntwo).index = 3 ∧
    Nonempty (Ntwo ⧸ Ctwo.subgroupOf Ntwo ≃* Equiv.Perm (Fin 3)) ∧
    Nat.card Ntwo = 22858846741463040 ∧ Nat.card Ctwo = 3809807790243840 ∧
    (Ptwo.subgroupOf Jhat).index = 46575 :=
  ⟨Vhat_le_Ehat, isKleinFour_Vhat, mem_Vhat_iff, tauhat_sq_conj_xhat, psiBar_zbar, rfl,
    Ptwo_eq_comap, ker_jhatToKv, ⟨ptwoQuotEquiv⟩, natCard_Ptwo, Ntwo_eq_closure, Ntwo_le_Shat,
    index_Ptwo_Ntwo, ⟨ntwoQuotEquiv⟩, natCard_Ntwo, natCard_Ctwo,
    Ptwo_subgroupOf_eq ▸ index_P2J⟩

end CFSG.Monster.B.TwoA
