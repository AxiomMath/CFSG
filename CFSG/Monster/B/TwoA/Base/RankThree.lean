
module

public import CFSG.Monster.B.TwoA.Base.RankThreeBase

public import CFSG.Monster.B.TwoA.Base.Plane

public noncomputable section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.Monster.B.TwoA

open CFSG.Monster CFSG.Monster.Code CFSG.Monster.Spin CFSG.Monster.SpinLattice
  CFSG.Monster.Griess CFSG.Monster.Visible CFSG.Monster.Generated CFSG.Monster.B.Short
  CFSG.Monster.B CFSG.Monster.VisQuot CFSG.Monster.ScalarKernel CFSG.Monster.B.Co2
  CFSG.Monster.Lifts CFSG.Monster.VisCert

theorem NU_transitive :

    ∀ y ∈ Uplane, y ≠ 0 → ∃ k ∈ wSetStab Uplane, wAct v0 k wFr = y := by
  intro y hy hy0
  rcases (mem_Uplane_iff y).1 hy with rfl | rfl | rfl | rfl
  · exact absurd rfl hy0
  · exact ⟨1, (wSetStab Uplane).one_mem, by rw [wAct_one, Module.End.one_apply]⟩
  · refine ⟨alpha23K * sgnK, (wSetStab Uplane).mul_mem alpha23K_mem_NU sgnK_mem_NU, ?_⟩
    rw [wAct_mul, Module.End.mul_apply, alpha23K_wFr, map_add, sgnK_wFr, sgnK_sW, ← add_assoc,
      two_smul_W, zero_add]
  · exact ⟨alpha23K, alpha23K_mem_NU, alpha23K_wFr⟩

theorem natCard_H3 :
    Nat.card H3 = 98956046499840 := by
  rw [H3_eq, natCard_HU, show wSetStab Uplane = NU from rfl, natCard_NU]
  norm_num

theorem K3_eq_closure :
    K3 = Subgroup.closure (insert tauhat (H3 : Set Dfull)) := by
  rw [K3_eq, H3_eq]
  exact KU_eq_closure tauhat_mem_normalizer_EU NU_transitive

theorem K3_le_Shat :
    K3 ≤ Shat := by
  rw [K3_eq]
  exact KU_le_Shat tauhat_mem_normalizer_EU NU_transitive

theorem index_H3_K3 :
    (H3.subgroupOf K3).index = 7 := by
  have h := index_HU_KU tauhat_mem_normalizer_EU NU_transitive
  rw [← E3_eq_EU, natCard_E3] at h
  rw [H3_eq, K3_eq]
  exact h

theorem natCard_K3 :
    Nat.card K3 = 692692325498880 := by
  have h := natCard_KU tauhat_mem_normalizer_EU NU_transitive
  rw [← K3_eq, ← E3_eq_EU, ← H3_eq, natCard_E3, natCard_H3] at h
  rw [h]

theorem conjE_E3_surjective :
    Function.Surjective (conjE E3) := by
  refine conjE_surjective_of_card ?_
  change Nat.card K3 = Nat.card (MulAut E3) * Nat.card C3
  rw [natCard_K3, natCard_mulAut_E3, natCard_C3]

theorem actE3_surjective :
    Function.Surjective actE3 := by
  rw [actE3, MonoidHom.coe_comp]
  exact (MulEquiv.surjective _).comp conjE_E3_surjective

@[expose] noncomputable def k3QuotEquiv :
    K3 ⧸ C3.subgroupOf K3 ≃* GL (Fin 3) (ZMod 2) :=
  (QuotientGroup.quotientMulEquivOfEq ker_actE3.symm).trans
    (QuotientGroup.quotientKerEquivOfSurjective actE3 actE3_surjective)

attribute [local instance] vAction

attribute [local instance] l3Action

theorem index_K3_inf_Ntwo :
    ((K3 ⊓ Ntwo).subgroupOf K3).index = 7 := by
  have h := ((K3 ⊓ Ntwo).subgroupOf K3).card_mul_index
  rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe (inf_le_left : K3 ⊓ Ntwo ≤ K3)).toEquiv,
    natCard_K3_inf_Ntwo, natCard_K3] at h
  omega

theorem full_short_rank_three_normalizer :
    zhat = iotaD (kappa ⟨rhoEquiv (DQ (deltaPair 2 3)),
      rhoEquiv_mem_Cgen (DQ_mem_centralizer _)⟩) ∧
    CFSG.IsElementaryAbelian 2 E3 ∧ Nat.card E3 = 8 ∧ Vhat ≤ E3 ∧
    (∀ e : Ehat, psiW e = 0 ↔ e = 1 ∨ e = xhatE) ∧ psiW yhatE = wFr ∧ psiW zhatE = sW ∧
    (∀ d : Dfull, d ∈ E3 ↔ ∃ h : d ∈ Ehat, psiW ⟨d, h⟩ ∈ Uplane) ∧
    H3.subgroupOf Jhat = NU.comap jhatToKv0 ∧
    K3 = Subgroup.closure (insert tauhat (H3 : Set Dfull)) ∧ K3 ≤ Shat ∧
    Nat.card H3 = 98956046499840 ∧ Nat.card K3 = 692692325498880 ∧
    Function.Surjective actE3 ∧ actE3.ker = C3.subgroupOf K3 ∧
    Nonempty (K3 ⧸ C3.subgroupOf K3 ≃* GL (Fin 3) (ZMod 2)) ∧
    (H3.subgroupOf K3).index = 7 ∧ ((K3 ⊓ Ntwo).subgroupOf K3).index = 7 ∧
    xhat ∈ Vhat ∧
    (∀ g : K3, (g : Dfull) ∈ H3 ↔ conjE E3 g ⟨xhat, xhat_mem_E3⟩ = ⟨xhat, xhat_mem_E3⟩) ∧
    (∀ g : K3, (g : Dfull) ∈ Ntwo ↔
      ∀ v : E3, (v : Dfull) ∈ Vhat → ((conjE E3 g v : E3) : Dfull) ∈ Vhat) ∧
    (∀ g : C3, ((c3Proj g : CU) : Kstab v0) = jhatToKv0 ⟨g, C3_le_Jhat g.2⟩) ∧
    Function.Surjective c3Proj ∧ c3Proj.ker = (Ehat ⊓ C3).subgroupOf C3 ∧
    Nat.card ↥(Ehat ⊓ C3) = 2 ^ 21 :=
  ⟨rfl, isElementaryAbelian_E3, natCard_E3, Vhat_le_E3, psiW_eq_zero_iff, psiW_yhat,
    psiW_zhat, fun d => by rw [E3_eq_EU]; exact mem_EU, H3_subgroupOf_eq, K3_eq_closure,
    K3_le_Shat, natCard_H3, natCard_K3, actE3_surjective, ker_actE3, ⟨k3QuotEquiv⟩,
    index_H3_K3, index_K3_inf_Ntwo, xhat_mem_Vhat, mem_H3_iff, mem_Ntwo_iff_conjE,
    coe_c3Proj, c3Proj_surjective, ker_c3Proj, natCard_Ehat_inf_C3⟩

end CFSG.Monster.B.TwoA
