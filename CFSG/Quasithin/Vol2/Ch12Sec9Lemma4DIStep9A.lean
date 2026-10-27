module

public import CFSG.Quasithin.Vol2.Ch12Sec9Lemma4DIGrp

public section

namespace CFSG.Quasithin.H13.C1294

variable {G : Type} [Group G] [Finite G]

theorem relIndex_sup_eq_of_normalizes {T K : Subgroup G}
    (hK : ∀ g ∈ K ⊔ T, ∀ k ∈ K, g * k * g⁻¹ ∈ K) :
    T.relIndex (K ⊔ T) = T.relIndex K := by
  let K' : Subgroup ↥(K ⊔ T) := K.subgroupOf (K ⊔ T)
  let T' : Subgroup ↥(K ⊔ T) := T.subgroupOf (K ⊔ T)
  haveI hKn : K'.Normal := ⟨fun n hn g => by
    rw [Subgroup.mem_subgroupOf] at hn ⊢
    have h := hK g.1 g.2 n.1 hn
    simpa using h⟩
  have hM : K ⊔ T ≤ (K' ⊔ T').map (K ⊔ T).subtype := by
    apply sup_le
    · intro k hk
      exact Subgroup.mem_map.2 ⟨⟨k, (le_sup_left : K ≤ K ⊔ T) hk⟩,
        Subgroup.mem_sup_left (Subgroup.mem_subgroupOf.2 hk), rfl⟩
    · intro t ht
      exact Subgroup.mem_map.2 ⟨⟨t, (le_sup_right : T ≤ K ⊔ T) ht⟩,
        Subgroup.mem_sup_right (Subgroup.mem_subgroupOf.2 ht), rfl⟩
  have hTop : K' ⊔ T' = ⊤ := by
    apply eq_top_iff.2
    intro x _
    obtain ⟨y, hy, hyx⟩ := Subgroup.mem_map.1 (hM x.2)
    have hxy : y = x := Subtype.ext hyx
    rw [← hxy]
    exact hy
  have h1 : K'.relIndex (K' ⊔ T') = K'.relIndex T' := Subgroup.relIndex_sup_left T' K'
  rw [hTop] at h1
  have h2 := Subgroup.relIndex_inf_mul_relIndex T' K' (⊤ : Subgroup ↥(K ⊔ T))
  have h3 := Subgroup.relIndex_inf_mul_relIndex K' T' (⊤ : Subgroup ↥(K ⊔ T))
  rw [inf_top_eq] at h2 h3
  rw [inf_comm T' K'] at h2
  have hK'pos : 0 < K'.relIndex ⊤ := by
    rw [h1]
    rcases Nat.eq_zero_or_pos (K'.relIndex T') with h0 | h0
    · exfalso
      have hm := Subgroup.relIndex_mul_card (H := K') (K := T')
      rw [h0, zero_mul] at hm
      exact absurd hm.symm (Nat.card_pos.ne')
    · exact h0
  have key : T'.relIndex K' = T'.relIndex ⊤ := by
    apply Nat.eq_of_mul_eq_mul_left hK'pos
    calc K'.relIndex ⊤ * T'.relIndex K' = T'.relIndex K' * K'.relIndex ⊤ := mul_comm _ _
      _ = (K' ⊓ T').relIndex ⊤ := by rw [h2, inf_comm]
      _ = K'.relIndex T' * T'.relIndex ⊤ := h3.symm
      _ = K'.relIndex ⊤ * T'.relIndex ⊤ := by rw [h1]
  have hT1 : T'.relIndex K' = T.relIndex K := Subgroup.relIndex_subgroupOf (le_sup_left : K ≤ K ⊔ T)
  have hT2 : T'.relIndex ⊤ = T.relIndex (K ⊔ T) := by
    have := Subgroup.relIndex_subgroupOf (H := T) (K := K ⊔ T) (L := K ⊔ T) le_rfl
    rw [Subgroup.subgroupOf_self] at this
    exact this
  rw [← hT1, ← hT2, key]

end CFSG.Quasithin.H13.C1294
