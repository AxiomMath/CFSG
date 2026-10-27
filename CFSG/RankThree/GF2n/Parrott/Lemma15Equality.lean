module

public import CFSG.RankThree.GF2n.Parrott.Lemma13
public import CFSG.RankThree.GF2n.Parrott.A1LocalData

public section

namespace CFSG.RankThree.GF2n.Parrott

open CFSG CFSG.Open CFSG.GH74.KGroups
open CFSG.ComponentClassification.CatFactsSmall.PSp43

@[expose] def b5uvList : List (Fin 45) := [42, 0, 38, 22, 28, 10, 32, 13, 18, 31, 19, 5, 17, 8,
  33, 35, 1, 36, 43, 39, 41, 40, 44, 2, 37, 16, 6, 15, 12, 27, 9, 24, 20, 3, 29, 34, 4, 30, 21,
  11, 23, 26, 25, 7, 14]

@[expose] def b5uvFun (i : Fin 45) : Fin 45 := b5uvList.getD i.val 0

theorem b5uvFun_five : ∀ i : Fin 45, b5uvFun (b5uvFun (b5uvFun (b5uvFun (b5uvFun i)))) = i := by
  decide +kernel

@[expose] def b5uv : Equiv.Perm (Fin 45) :=
  ⟨b5uvFun, b5uvFun ∘ b5uvFun ∘ b5uvFun ∘ b5uvFun, fun i => b5uvFun_five i,
    fun i => b5uvFun_five i⟩

theorem b5uv_ne_one : b5uv ≠ 1 := by decide +kernel

theorem b5uv_pow_five : b5uv ^ 5 = 1 := by decide +kernel

theorem b5uv_commute_uv : b5uv * (u * v) = u * v * b5uv := by decide +kernel

theorem b5uv_mem_A : b5uv ∈ QA45.originalSubgroup :=
  (mem_iff_sift QA45 QA45_ok b5uv).2 (by decide +kernel)

variable {G : Type} [Group G] [Finite G] {z : G}
variable [hN : ((J z).subgroupOf (H z)).Normal]
variable (D : QuotientData (z := z) hN)

theorem exists_order_five_subgroup_conj_mem_uvJ (h : Tim79a.ParrottHyp z) :
    ∃ B : Subgroup G, B ≤ H z ∧ Nat.card B = 5 ∧
      ∀ b ∈ B, cosetJ (z := z) (uH D * vH D) (b * ((uH D * vH D : ↥(H z)) : G) * b⁻¹) := by
  classical
  have : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  have hker : IsPGroup 2 (qH D).ker := by
    have hk : (qH D).ker = (J z).subgroupOf (H z) := by
      ext x
      rw [MonoidHom.mem_ker, J_mem_iff]
    rw [hk]
    exact (isPGroup_J h).comap_of_injective (H z).subtype (H z).subtype_injective
  set bq : QA45.originalSubgroup := ⟨b5uv, b5uv_mem_A⟩ with hbq
  have hbq5 : orderOf bq = 5 := by
    refine orderOf_eq_prime (Subtype.ext ?_) fun h1 => b5uv_ne_one (congrArg Subtype.val h1)
    rw [SubgroupClass.coe_pow]
    exact b5uv_pow_five
  obtain ⟨n, hqn, hord⟩ := exists_pow_lift_orderOf_eq (qH D) hker (c := lift D bq) (m := 5)
    (by decide) (by norm_num) (by rw [qH_lift]; exact hbq5)
  obtain ⟨c, hc⟩ : ∃ c : ↥(H z), c = lift D bq ^ n := ⟨_, rfl⟩
  have hqc : qH D c = bq := by rw [hc, hqn, qH_lift]
  have hord' : orderOf c = 5 := by rw [hc, hord]
  obtain ⟨w, hw⟩ : ∃ w : ↥(H z), w = uH D * vH D := ⟨_, rfl⟩
  have hcomm : Commute bq (qH D w) := by
    apply Subtype.ext
    rw [hw, map_mul, qH_uH, qH_vH]
    exact b5uv_commute_uv
  rw [← hw]
  refine ⟨Subgroup.zpowers (c : G), Subgroup.zpowers_le.mpr c.2, ?_, ?_⟩
  · rw [Nat.card_zpowers, Subgroup.orderOf_coe, hord']
  · intro b hb
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hb
    obtain ⟨y, hy⟩ : ∃ y : ↥(H z), y = w⁻¹ * (c ^ k * w * (c ^ k)⁻¹) := ⟨_, rfl⟩
    have hy1 : qH D y = 1 := by
      rw [hy, map_mul, map_inv, map_mul, map_mul, map_inv, map_zpow, hqc,
        (hcomm.zpow_left k).eq, mul_inv_cancel_right, inv_mul_cancel]
    refine ⟨(y : G), Subgroup.mem_subgroupOf.mp ((J_mem_iff D y).mpr hy1), ?_⟩
    rw [hy]
    simp only [Subgroup.coe_mul, Subgroup.coe_inv, SubgroupClass.coe_zpow]
    group

end CFSG.RankThree.GF2n.Parrott
