
module

public import CFSG.Monster.B.TwoA.Base.Par45BBase

public import CFSG.Monster.B.TwoA.Base.Par45A
public import CFSG.Monster.B.TwoA.Base.RankThree

public noncomputable section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.Monster.B.TwoA

open CFSG.Monster CFSG.Monster.Code CFSG.Monster.Spin CFSG.Monster.SpinLattice
  CFSG.Monster.Griess CFSG.Monster.Visible CFSG.Monster.Generated CFSG.Monster.B.Short
  CFSG.Monster.B CFSG.Monster.VisQuot CFSG.Monster.ScalarKernel CFSG.Monster.B.Co2
  CFSG.Monster.Lifts CFSG.Monster.VisCert

theorem pCore_K4_eq :
    CFSG.pCore 2 K4 = Z4.subgroupOf K4 :=
  pCore_normalizer_eq_centralizer (IsPGroup.of_card natCard_Z4)
    (by rw [natCard_E4]; decide) fun _ ha ha1 => exists_K4_conj_xhat ha ha1

theorem pCore_K5_eq :
    CFSG.pCore 2 K5 = Z5.subgroupOf K5 :=
  pCore_normalizer_eq_centralizer (IsPGroup.of_card natCard_Z5)
    (by rw [natCard_E5]; decide) fun _ ha ha1 => exists_K5_conj_xhat ha ha1

theorem Z4_eq_pCore :
    Z4 = (CFSG.pCore 2 K4).map K4.subtype := by
  rw [pCore_K4_eq, Subgroup.map_subgroupOf_eq_of_le Z4_le_K4]

theorem Z5_eq_pCore :
    Z5 = (CFSG.pCore 2 K5).map K5.subtype := by
  rw [pCore_K5_eq, Subgroup.map_subgroupOf_eq_of_le Z5_le_K5]

theorem E4_le_Z4 :
    E4 ≤ Z4 := fun _ ha => Subgroup.mem_centralizer_iff.2 fun _ hb =>
  EU_comm qV_U3 (E4_eq_EU ▸ hb) (E4_eq_EU ▸ ha)

theorem E5_le_Z5 :
    E5 ≤ Z5 := fun _ ha => Subgroup.mem_centralizer_iff.2 fun _ hb =>
  EU_comm qV_U4 (E5_eq_EU ▸ hb) (E5_eq_EU ▸ ha)

theorem index_E4_Z4 :
    (E4.subgroupOf Z4).index = 2 ^ 31 :=
  index_eq_of_natCard E4_le_Z4 natCard_E4 natCard_Z4 (by norm_num) (by norm_num)

theorem index_E5_Z5 :
    (E5.subgroupOf Z5).index = 2 ^ 25 :=
  index_eq_of_natCard E5_le_Z5 natCard_E5 natCard_Z5 (by norm_num) (by norm_num)

theorem E3_lt_E4 :
    E3 < E4 :=
  lt_of_le_of_natCard_eq E3_le_E4 natCard_E3_pow natCard_E4 (by norm_num)

theorem E4_lt_E5 :
    E4 < E5 :=
  lt_of_le_of_natCard_eq E4_le_E5 natCard_E4 natCard_E5 (by norm_num)

theorem chain_flags :
    ∀ j i : ℕ, 1 ≤ j → j < i → i ≤ 5 →
    (∀ g : Kchain i, (g : Dfull) ∈ Kchain j ↔
      ∀ e : Echain i, (e : Dfull) ∈ Echain j →
        ((conjE (Echain i) g e : Echain i) : Dfull) ∈ Echain j) ∧
    ((Kchain j ⊓ Kchain i).subgroupOf (Kchain i)).index =
      Nat.card (SubspaceDim (ZMod 2) (Fin i → ZMod 2) j) := by
  intro j i hj hji hi
  have hi2 : 2 ≤ i := by omega
  interval_cases i <;> interval_cases j
  · exact flag_pair (E := Vhat) (F := Subgroup.zpowers xhat) natCard_Vhat_pow
      natCard_zpowers_xhat (Subgroup.zpowers_le.2 xhat_mem_Vhat) conjE_Vhat_surjective
  · exact flag_pair (E := E3) (F := Subgroup.zpowers xhat) natCard_E3_pow
      natCard_zpowers_xhat (Subgroup.zpowers_le.2 xhat_mem_E3) conjE_E3_surjective
  · exact flag_pair (E := E3) (F := Vhat) natCard_E3_pow natCard_Vhat_pow Vhat_le_E3
      conjE_E3_surjective
  · exact flag_pair (E := E4) (F := Subgroup.zpowers xhat) natCard_E4
      natCard_zpowers_xhat (Subgroup.zpowers_le.2 xhat_mem_E4) conjE_E4_surjective
  · exact flag_pair (E := E4) (F := Vhat) natCard_E4 natCard_Vhat_pow
      (Vhat_le_E3.trans E3_le_E4) conjE_E4_surjective
  · exact flag_pair (E := E4) (F := E3) natCard_E4 natCard_E3_pow E3_le_E4
      conjE_E4_surjective
  · exact flag_pair (E := E5) (F := Subgroup.zpowers xhat) natCard_E5
      natCard_zpowers_xhat (Subgroup.zpowers_le.2 xhat_mem_E5) conjE_E5_surjective
  · exact flag_pair (E := E5) (F := Vhat) natCard_E5 natCard_Vhat_pow
      ((Vhat_le_E3.trans E3_le_E4).trans E4_le_E5) conjE_E5_surjective
  · exact flag_pair (E := E5) (F := E3) natCard_E5 natCard_E3_pow (E3_le_E4.trans E4_le_E5)
      conjE_E5_surjective
  · exact flag_pair (E := E5) (F := E4) natCard_E5 natCard_E4 E4_le_E5 conjE_E5_surjective

theorem full_short_four_five_parabolic_structures :
    dhat 4 5 = iotaD (kappa ⟨rhoEquiv (DQ (deltaPair 4 5)),
      rhoEquiv_mem_Cgen (DQ_mem_centralizer _)⟩) ∧
    dhat 8 9 = iotaD (kappa ⟨rhoEquiv (DQ (deltaPair 8 9)),
      rhoEquiv_mem_Cgen (DQ_mem_centralizer _)⟩) ∧
    E4 = Subgroup.closure (insert (dhat 4 5) (E3 : Set Dfull)) ∧
    E5 = Subgroup.closure (insert (dhat 8 9) (E4 : Set Dfull)) ∧
    CFSG.IsElementaryAbelian 2 E4 ∧ Nat.card E4 = 2 ^ 4 ∧
    CFSG.IsElementaryAbelian 2 E5 ∧ Nat.card E5 = 2 ^ 5 ∧
    Subgroup.zpowers xhat < Vhat ∧ Vhat < E3 ∧ E3 < E4 ∧ E4 < E5 ∧
    psiW (dhatE 4 5) = pairW 4 5 offPair45 0 ∧ psiW (dhatE 8 9) = pairW 8 9 offPair89 0 ∧
    (∀ d : Dfull, d ∈ E4 ↔ ∃ h : d ∈ Ehat, psiW ⟨d, h⟩ ∈ U3) ∧
    (∀ d : Dfull, d ∈ E5 ↔ ∃ h : d ∈ Ehat, psiW ⟨d, h⟩ ∈ U4) ∧
    H4.subgroupOf Jhat = (wSetStab U3).comap jhatToKv0 ∧
    H5.subgroupOf Jhat = (wSetStab U4).comap jhatToKv0 ∧
    K4 = Subgroup.closure (insert tauhat (H4 : Set Dfull)) ∧ K4 ≤ Shat ∧
    K5 = Subgroup.closure (insert tauhat (H5 : Set Dfull)) ∧ K5 ≤ Shat ∧
    Function.Surjective actE4 ∧ actE4.ker = Z4.subgroupOf K4 ∧
    Nonempty (K4 ⧸ Z4.subgroupOf K4 ≃* GL (Fin 4) (ZMod 2)) ∧
    Function.Surjective actE5 ∧ actE5.ker = Z5.subgroupOf K5 ∧
    Nonempty (K5 ⧸ Z5.subgroupOf K5 ≃* GL (Fin 5) (ZMod 2)) ∧
    Z4 = (CFSG.pCore 2 K4).map K4.subtype ∧ Nat.card Z4 = 2 ^ 35 ∧
    Z5 = (CFSG.pCore 2 K5).map K5.subtype ∧ Nat.card Z5 = 2 ^ 30 ∧
    Nat.card K4 = 692692325498880 ∧ Nat.card K5 = 10736731045232640 ∧
    (E4.subgroupOf K4).Normal ∧ (Z4.subgroupOf K4).Normal ∧ E4 ≤ Z4 ∧
    (E4.subgroupOf Z4).index = 2 ^ 31 ∧
    (E5.subgroupOf K5).Normal ∧ (Z5.subgroupOf K5).Normal ∧ E5 ≤ Z5 ∧
    (E5.subgroupOf Z5).index = 2 ^ 25 ∧
    Kchain 1 = Jhat ∧ Kchain 2 = Ntwo ∧
    (∀ j i : ℕ, 1 ≤ j → j < i → i ≤ 5 →
      (∀ g : Kchain i, (g : Dfull) ∈ Kchain j ↔
        ∀ e : Echain i, (e : Dfull) ∈ Echain j →
          ((conjE (Echain i) g e : Echain i) : Dfull) ∈ Echain j) ∧
      ((Kchain j ⊓ Kchain i).subgroupOf (Kchain i)).index =
        Nat.card (SubspaceDim (ZMod 2) (Fin i → ZMod 2) j)) ∧
    (∀ i j : ℕ, j ≤ i → Nat.card (SubspaceDim (ZMod 2) (Fin i → ZMod 2) j) = qBinom 2 i j) ∧
    [qBinom 2 2 1, qBinom 2 3 1, qBinom 2 3 2, qBinom 2 4 1, qBinom 2 4 2, qBinom 2 4 3,
      qBinom 2 5 1, qBinom 2 5 2, qBinom 2 5 3, qBinom 2 5 4] =
      [3, 7, 7, 15, 35, 15, 31, 155, 155, 31] :=
  ⟨rfl, rfl, rfl, rfl, isElementaryAbelian_E4, natCard_E4, isElementaryAbelian_E5, natCard_E5,
    zpowers_xhat_lt_Vhat, Vhat_lt_E3, E3_lt_E4, E4_lt_E5, psiW_d45, psiW_d89,
    fun d => by rw [E4_eq_EU]; exact mem_EU, fun d => by rw [E5_eq_EU]; exact mem_EU,
    H4_subgroupOf_eq, H5_subgroupOf_eq, K4_eq_closure, K4_le_Shat, K5_eq_closure, K5_le_Shat,
    actE4_surjective, ker_actE4, ⟨k4QuotEquiv⟩, actE5_surjective, ker_actE5, ⟨k5QuotEquiv⟩,
    Z4_eq_pCore, natCard_Z4, Z5_eq_pCore, natCard_Z5, natCard_K4, natCard_K5, inferInstance,
    inferInstance, E4_le_Z4, index_E4_Z4, inferInstance, inferInstance, E5_le_Z5, index_E5_Z5,
    Kchain_one, Kchain_two, chain_flags, fun _ _ h => natCard_subspaceDim_fin h, qBinom_values⟩

end CFSG.Monster.B.TwoA
