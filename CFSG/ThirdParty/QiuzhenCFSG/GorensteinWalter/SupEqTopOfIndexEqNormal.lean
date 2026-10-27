module

public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.IndexNormalSup
import Mathlib.Tactic

namespace CFSG
end CFSG
open CFSG

/-! # Detecting a normal product from its index -/

noncomputable section

namespace CFSG.GorensteinWalter

universe u

/-- The converse of the normal-product index formula: equality of the ambient
index and the relative index in a normal subgroup forces the two subgroups to
generate the ambient group. -/
public theorem sup_eq_top_of_index_eq_relIndex_inf_of_normal
    {G : Type u} [Group G] [Finite G]
    (N K : Subgroup G) (hN : N.Normal)
    (hindex : K.index = (N ⊓ K).relIndex N) :
    N ⊔ K = ⊤ := by
  classical
  let S : Subgroup G := N ⊔ K
  have hNleS : N ≤ S := le_sup_left
  have hKleS : K ≤ S := le_sup_right
  let N0 : Subgroup S := N.subgroupOf S
  let K0 : Subgroup S := K.subgroupOf S
  have hN0normal : N0.Normal := by
    let : N.Normal := hN
    apply Subgroup.normal_subgroupOf_of_le_normalizer
    rw [Subgroup.normalizer_eq_top]
    exact le_top
  have hN0K0top : N0 ⊔ K0 = ⊤ := by
    rw [← Subgroup.subgroupOf_sup hNleS hKleS]
    exact Subgroup.subgroupOf_self S
  have hlocal :=
    index_eq_relIndex_inf_of_normal_sup N0 K0 hN0normal hN0K0top
  have hinf : N0 ⊓ K0 = (N ⊓ K).subgroupOf S := by
    ext x
    simp [N0, K0, Subgroup.mem_subgroupOf]
  have hright : (N0 ⊓ K0).relIndex N0 = (N ⊓ K).relIndex N := by
    rw [hinf]
    exact Subgroup.relIndex_subgroupOf hNleS
  have hKS : K.relIndex S = K.index := by
    calc
      K.relIndex S = K0.index := by rfl
      _ = (N0 ⊓ K0).relIndex N0 := hlocal
      _ = (N ⊓ K).relIndex N := hright
      _ = K.index := hindex.symm
  have hmul := Subgroup.relIndex_mul_index hKleS
  rw [hKS] at hmul
  have hKpos : 0 < K.index := Nat.card_pos
  have hSindex : S.index = 1 := by
    apply Nat.eq_of_mul_eq_mul_left hKpos
    simpa using hmul
  exact Subgroup.index_eq_one.mp hSindex

end CFSG.GorensteinWalter
