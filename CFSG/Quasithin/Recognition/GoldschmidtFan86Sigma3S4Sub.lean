module

public import CFSG.Quasithin.Recognition.GoldschmidtFan86Sigma3Off10
public import CFSG.Quasithin.Recognition.GoldschmidtFan86Sigma3S4Rec
public import CFSG.Quasithin.Recognition.GoldschmidtFan86Sigma3Off8

public section

namespace CFSG.Quasithin.Fan86.Sigma3

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique.Setup

theorem card_sup_of_inf_eq_bot {G : Type*} [Group G] [Finite G] (A B : Subgroup G) [B.Normal]
    (h : A ⊓ B = ⊥) : Nat.card ↥(A ⊔ B) = Nat.card A * Nat.card B := by
  have h1 := Subgroup.relIndex_sup_right A B
  have h2 : B.relIndex A = Nat.card A := by
    rw [← Subgroup.inf_relIndex_right B A, inf_comm, h, Subgroup.relIndex_bot_left]
  have h3 := Subgroup.card_mul_index (B.subgroupOf (A ⊔ B))
  have h4 : Nat.card ↥(B.subgroupOf (A ⊔ B)) = Nat.card B :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe le_sup_right).toEquiv
  rw [h4] at h3
  have h5 : (B.subgroupOf (A ⊔ B)).index = Nat.card A := by
    rw [← h2, ← h1]; rfl
  rw [h5] at h3
  rw [← h3, mul_comm]

abbrev permSub (H : Type*) [Group H] (t : H) : Subgroup H := oL H ⊔ Subgroup.zpowers t

variable {H : Type*} [Group H] [Finite H] {S : Subgroup H} {x t : H}

theorem Hyp3.t_not_mem_oL (h : Hyp3 H S x) (htQ : t ∉ oQ H) (ht2 : t * t = 1) : t ∉ oL H := by
  intro htL
  obtain ⟨ψ, -, hker⟩ := h.sig.exists_hom
  have hx3 : (ψ x) ^ 3 = 1 := by
    have : x ^ 3 = 1 := by rw [← h.ord]; exact pow_orderOf_eq_one x
    rw [← map_pow, this, map_one]
  have hle : oL H ≤ (Subgroup.zpowers (ψ x)).comap ψ := by
    rw [h.oL_eq]
    refine sup_le (fun n hn => ?_)
      (Subgroup.zpowers_le.2 (Subgroup.mem_comap.2 (Subgroup.mem_zpowers _)))
    have hnQ : n ∈ oQ H := oneCenter_le (nQ_le x hn)
    have : ψ n = 1 := by rw [← MonoidHom.mem_ker, hker]; exact hnQ
    rw [Subgroup.mem_comap, this]
    exact Subgroup.one_mem _
  obtain ⟨j, hj⟩ := Subgroup.mem_zpowers_iff.1 (Subgroup.mem_comap.1 (hle htL))
  have h3 : (ψ t) ^ 3 = 1 := by
    rw [← hj, ← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hx3, one_zpow]
  have h2 : (ψ t) * (ψ t) = 1 := by rw [← map_mul, ht2, map_one]
  have h1 : ψ t = 1 := by
    calc ψ t = ψ t ^ 3 * (ψ t * ψ t)⁻¹ := by group
      _ = 1 := by rw [h3, h2]; simp
  have h4 : t ∈ ψ.ker := MonoidHom.mem_ker.2 h1
  rw [hker] at h4
  exact htQ h4

omit [Finite H] in
theorem zpowers_of_sq {w : H} (ht2 : t * t = 1) (hw : w ∈ Subgroup.zpowers t) :
    w = 1 ∨ w = t := by
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hw
  have h2 : t ^ (2 : ℤ) = 1 := by rw [zpow_two]; exact ht2
  obtain ⟨m, hm | hm⟩ := Int.even_or_odd' k
  · left
    rw [hm, zpow_mul, h2, one_zpow]
  · right
    rw [hm, zpow_add_one, zpow_mul, h2, one_zpow, one_mul]

theorem Hyp3.inf_zpowers_eq_bot (h : Hyp3 H S x) (htQ : t ∉ oQ H) (ht2 : t * t = 1) :
    oL H ⊓ Subgroup.zpowers t = ⊥ := by
  rw [Subgroup.eq_bot_iff_forall]
  rintro w ⟨hwL, hwZ⟩
  rcases zpowers_of_sq ht2 hwZ with h1 | h1
  · exact h1
  · exact absurd (h1 ▸ hwL) (h.t_not_mem_oL htQ ht2)

theorem Hyp3.card_permSub (h : Hyp3 H S x) (htQ : t ∉ oQ H) (ht2 : t * t = 1) :
    Nat.card ↥(permSub H t) = 24 := by
  have : (oL H).Normal := oL_normal
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have ht1 : t ≠ 1 := fun h1 => htQ (h1 ▸ (oQ H).one_mem)
  have hZ : Nat.card (Subgroup.zpowers t) = 2 := by
    rw [Nat.card_zpowers]
    exact orderOf_eq_prime (by rw [pow_two]; exact ht2) ht1
  have h12 : Nat.card ↥(oL H) = 12 := h.card_oddOrder
  have h1 := card_sup_of_inf_eq_bot (Subgroup.zpowers t) (oL H)
    (by rw [inf_comm]; exact h.inf_zpowers_eq_bot htQ ht2)
  rw [sup_comm] at h1
  rw [h1, hZ, h12]

theorem Hyp3.x_mem_permSub (h : Hyp3 H S x) : x ∈ permSub H t :=
  Subgroup.mem_sup_left (odd_mem_oL (by rw [h.ord]; decide))

omit [Finite H] in
theorem mem_permSub_self : t ∈ permSub H t := Subgroup.mem_sup_right (Subgroup.mem_zpowers t)

theorem Hyp3.nQ_le_permSub (h : Hyp3 H S x) : nQ H x ≤ permSub H t :=
  (nQ_le_oL x h.ord).trans le_sup_left

theorem Hyp3.exists_moved_nQ (h : Hyp3 H S x) (htS : t ∈ S) (htQ : t ∉ oQ H) :
    ∃ n ∈ nQ H x, t * n * t⁻¹ ≠ n := by
  obtain ⟨-, a, -, haS, haQ, n, hn, hne⟩ := h.offender
  exact ⟨n, hn, by rw [h.conj_nQ haS haQ htS htQ hn]; exact hne⟩

theorem Hyp3.klein24 (h : Hyp3 H S x) (htS : t ∈ S) (htQ : t ∉ oQ H) (ht2 : t * t = 1) :
    Klein24 ↥(permSub H t) ((nQ H x).subgroupOf (permSub H t)) ⟨x, h.x_mem_permSub⟩
      ⟨t, mem_permSub_self⟩ := by
  have hx3 := mul_mul_eq_one_of_orderOf h.ord
  refine ⟨h.card_permSub htQ ht2, (h.sig.nQ_normal h.ord).subgroupOf _, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe h.nQ_le_permSub).toEquiv]
    exact h.offender.1
  · intro a ha b hb
    exact Subtype.ext (elem_comm (nQ_elem x) (Subgroup.mem_subgroupOf.1 ha)
      (Subgroup.mem_subgroupOf.1 hb))
  · rw [← Subgroup.orderOf_coe]
    exact h.ord
  · intro n hn hf
    exact Subtype.ext (nQ_fix hx3 (Subgroup.mem_subgroupOf.1 hn) (congrArg Subtype.val hf))
  · exact Subtype.ext ht2
  · obtain ⟨n, hn, hne⟩ := h.exists_moved_nQ htS htQ
    exact ⟨⟨n, h.nQ_le_permSub hn⟩, Subgroup.mem_subgroupOf.2 hn,
      fun hc => hne (congrArg Subtype.val hc)⟩

end CFSG.Quasithin.Fan86.Sigma3
