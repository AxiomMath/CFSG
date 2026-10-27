module

public import CFSG.CGT.Timmesfeld75.L2Pair
public import CFSG.GroupTheory.ElemAbelianClosure

public section

namespace CFSG.RankThree.GF2n.Stroth80

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open

theorem mem_of_isConj_of_mem_wc {G : Type} [Group G] {T : Subgroup G} (hT : IsWC T) {x t : G}
    (hx : x ∈ Subgroup.centralizer (T : Set G)) (hx1 : x ≠ 1) (htT : t ∈ T)
    (hconj : IsConj x t) : x ∈ T := by
  obtain ⟨c, hc⟩ := isConj_iff.1 hconj
  have hxT' : x ∈ conjSubgroup c⁻¹ T := by
    rw [mem_conjSubgroup]
    simpa [hc] using htT
  have hT' : IsWC (conjSubgroup c⁻¹ T) := hT.conj c⁻¹
  have hcc : conjSubgroup c (conjSubgroup c⁻¹ T) = T := by
    rw [conjSubgroup_conjSubgroup, mul_inv_cancel]
    ext y
    simp [mem_conjSubgroup]
  have hle : conjSubgroup c (conjSubgroup c⁻¹ T) ≤ Subgroup.centralizer ({x} : Set G) := by
    rw [hcc]
    intro y hy
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact Subgroup.mem_centralizer_iff.1 hx y hy
  have heq := (hT'.2 x hxT' hx1).2 c hle
  rw [hcc] at heq
  rw [heq]
  exact hxT'

theorem exists_isElemAbelian_gt {G : Type*} [Group G] {T : Subgroup G} (hT : IsElemAbelian 2 T)
    {x : G} (hx : x ∈ Subgroup.centralizer (T : Set G)) (hx2 : x * x = 1) (hxT : x ∉ T) :
    ∃ E : Subgroup G, T < E ∧ IsElemAbelian 2 E := by
  have hx2' : x ^ 2 = 1 := by rw [pow_two]; exact hx2
  have hc : ∀ a ∈ T, ∀ b ∈ Subgroup.zpowers x, a * b = b * a := by
    intro a ha b hb
    obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.1 hb
    have : Commute a x := Subgroup.mem_centralizer_iff.1 hx a ha
    exact (this.zpow_right n).eq
  refine ⟨T ⊔ Subgroup.zpowers x, lt_of_le_of_ne le_sup_left fun h => hxT ?_,
    IsElemAbelian.sup_of_commute hT (isElemAbelian_zpowers hx2') hc⟩
  rw [h]
  exact Subgroup.mem_sup_right (Subgroup.mem_zpowers x)

theorem mem_of_mul_self_eq_one_of_mulEquiv {G H : Type} [Group G] [Group H] (e : G ≃* H)
    (h : ∀ T : Subgroup H, IsWC T → 4 ≤ Nat.card T → ∀ x ∈ Subgroup.centralizer (T : Set H),
      x * x = 1 → x ∈ T)
    {T : Subgroup G} (hT : IsWC T) (h4 : 4 ≤ Nat.card T) {x : G}
    (hx : x ∈ Subgroup.centralizer (T : Set G)) (hx2 : x * x = 1) : x ∈ T := by
  have hmem := h (T.map e.toMonoidHom) (hT.map_mulEquiv e)
    (by rw [Subgroup.card_map_of_injective e.injective]; exact h4) (e x) (by
      rw [Subgroup.mem_centralizer_iff]
      rintro _ ⟨t, ht, rfl⟩
      show e t * e x = e x * e t
      rw [← map_mul, ← map_mul, Subgroup.mem_centralizer_iff.1 hx t ht]) (by
      rw [← map_mul, hx2, map_one])
  obtain ⟨t, ht, hte⟩ := hmem
  have : t = x := e.injective hte
  rwa [← this]

end CFSG.RankThree.GF2n.Stroth80
