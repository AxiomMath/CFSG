module

public import CFSG.Quasithin.Vol2.Ch10SecQ4FS5

public section

namespace CFSG.Quasithin.Vol2.Ch10.SecF.C10P4F

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem relIndex_pCoreOf_le_four {K Y : Subgroup G} (hKa : IsAltType K 5) (hYK : Y ≤ K)
    (hQY : pCoreOf 2 K ≤ Y) (hY2 : IsPGroup 2 Y) : (pCoreOf 2 K).relIndex Y ≤ 4 := by
  obtain ⟨α, -, hαk, -⟩ := hKa
  have hker : (pCoreOf 2 K).subgroupOf K = α.ker := by
    rw [hαk, pCoreOf]
    exact Subgroup.comap_map_eq_self_of_injective K.subtype_injective _
  have h1 := Subgroup.relIndex_map_map α ⊥ (Y.subgroupOf K)
  rw [Subgroup.map_bot, Subgroup.relIndex_bot_left, bot_sup_eq, ← hker,
    sup_eq_left.mpr (Subgroup.subgroupOf_mono K hQY), Subgroup.relIndex_subgroupOf hYK] at h1
  rw [← h1]
  refine card_le_four_of_isPGroup ?_
  have hY2' : IsPGroup 2 ↥(Y.subgroupOf K) := hY2.of_equiv (Subgroup.subgroupOfEquivOfLe hYK).symm
  exact hY2'.map α

theorem relIndex_centralizer_le_sixteen {K : Subgroup G} (hKs : IsShort2 K)
    (hKa : IsAltType K 5) {q : G} (hqK : q ∈ K) (hq3 : orderOf q = 3) {Y : Subgroup G}
    (hYK : Y ≤ K) (hY2 : IsPGroup 2 Y) :
    (Subgroup.centralizer ({q} : Set G)).relIndex Y ≤ 16 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hq3' : q ^ 3 = 1 := by rw [← hq3]; exact pow_orderOf_eq_one q
  set Q := pCoreOf 2 K with hQ
  have hQ2 : IsPGroup 2 Q := CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 K
  have hKQ : K ≤ Subgroup.normalizer (Q : Set G) := CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 K
  have hQK : Q ≤ K := CFSG.LieType.BorelTits.pCoreOf_le 2 K
  have hYQ2 : IsPGroup 2 (Y ⊔ Q : Subgroup G) := IsPGroup.to_sup_of_normal_right' hY2 hQ2
    (hYK.trans hKQ)
  have hYQK : Y ⊔ Q ≤ K := sup_le hYK hQK
  have h1 : (Subgroup.centralizer ({q} : Set G)).relIndex Y ≤
      (Subgroup.centralizer ({q} : Set G)).relIndex (Y ⊔ Q) :=
    relIndex_centralizer_le_of_le le_sup_left
  have h2 := relIndex_centralizer_eq_mul (q := q) (le_sup_right : Q ≤ Y ⊔ Q)
    (inf_le_left.trans (hYQK.trans hKQ))
  have h3 : (Q ⊔ (Y ⊔ Q) ⊓ Subgroup.centralizer ({q} : Set G)).relIndex (Y ⊔ Q) ≤ 4 :=
    (Subgroup.relIndex_le_of_le_left le_sup_left Subgroup.index_ne_zero_of_finite).trans
      (relIndex_pCoreOf_le_four hKa hYQK le_sup_right hYQ2)
  have hUQ : blockU K ≤ Q := hKs.2.2.1.1.trans inf_le_left
  have h4 : (Subgroup.centralizer ({q} : Set G)).relIndex Q =
      (Subgroup.centralizer ({q} : Set G)).relIndex (blockU K) := by
    refine relIndex_centralizer_eq_of_commutator hq3' hQ2 hUQ
      (hQK.trans (le_normalizer_blockU K)) (le_normalizer_blockU K hqK) fun y hy => ?_
    rw [blockU, Subgroup.commutator_comm]
    have := Subgroup.commutator_mem_commutator hqK hy
    rwa [commutatorElement_def] at this
  have h5 := relIndex_centralizer_blockU_le hKs hKa hqK hq3
  rw [h2, h4] at h1
  calc (Subgroup.centralizer ({q} : Set G)).relIndex Y ≤ _ := h1
    _ ≤ 4 * 4 := Nat.mul_le_mul h5 h3
    _ = 16 := by norm_num

end CFSG.Quasithin.Vol2.Ch10.SecF.C10P4F
