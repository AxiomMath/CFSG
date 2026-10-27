module

public import CFSG.Quasithin.Background.RonanH143QL2

public section

open scoped Pointwise

namespace CFSG.Quasithin.RonanH143

open CFSG.Monster.Code CFSG.Quasithin.H.Mathieu CFSG.Quasithin.H.Mathieu.H16Pf CFSG.Quasithin

theorem mem_conjSubg_sylw {c x : P24} {A : Subgroup P24} :
    x ∈ conjSubg c A ↔ c⁻¹ * x * c ∈ A := by
  unfold conjSubg
  rw [Subgroup.mem_map_equiv, MulAut.conj_symm_apply]

theorem P2_le_mog22plus_sylw : P2 ≤ mog22plus := by
  rintro x ⟨y, hy, rfl | rfl⟩
  · exact mog22_le_mog22plus (PO_le_mog22 hy)
  · exact mog22plus.mul_mem (mog22_le_mog22plus (PO_le_mog22 hy)) ePerm_mem_mog22plus

theorem relIndex_mul_card_sylw {H K : Subgroup P24} (hHK : H ≤ K) :
    H.relIndex K * Nat.card H = Nat.card K := by
  have h1 := (H.subgroupOf K).card_mul_index
  rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hHK).toEquiv] at h1
  show (H.subgroupOf K).index * Nat.card H = Nat.card K
  rw [mul_comm]
  exact h1

theorem notMem_PO_mul_ePerm_sylw {y : P24} (hy : y ∈ PO) : y * ePerm ∉ PO := by
  intro h
  have hPE : ePerm ∈ PO := by
    simpa using PO.mul_mem (PO.inv_mem hy) h
  exact ePerm_notMem_mog22 (PO_le_mog22 hPE)

theorem xor_mul_ePerm_mem_PO_sylw {x : P24} (hx : x ∈ P2) :
    Xor (x * ePerm ∈ PO) (x ∈ PO) := by
  obtain ⟨y, hy, hxy | hxy⟩ := mem_P2_iff.1 hx
  · subst hxy
    unfold Xor
    exact Or.inr ⟨hy, notMem_PO_mul_ePerm_sylw hy⟩
  · subst hxy
    unfold Xor
    refine Or.inl ⟨?_, notMem_PO_mul_ePerm_sylw hy⟩
    rw [mul_assoc, ePerm_sq, mul_one]
    exact hy

theorem index_PO_P2_sylw : (PO.subgroupOf P2).index = 2 := by
  rw [Subgroup.index_eq_two_iff]
  refine ⟨⟨ePerm, ePerm_mem_P2⟩, fun b => ?_⟩
  simp only [Subgroup.mem_subgroupOf, Subgroup.coe_mul]
  exact xor_mul_ePerm_mem_PO_sylw b.2

theorem card_P2 : Nat.card P2 = 256 := by
  have h1 := (PO.subgroupOf P2).card_mul_index
  rw [index_PO_P2_sylw, Nat.card_congr (Subgroup.subgroupOfEquivOfLe PO_le_P2).toEquiv,
    card_PO] at h1
  have h2 : 128 * 2 = Nat.card P2 := h1
  omega

theorem isSylowIn_PO :
    IsSylowIn 2 PO mog22 := by
  refine ⟨PO_le_mog22, IsPGroup.of_card (p := 2) (n := 7) (card_PO.trans (by norm_num)), ?_⟩
  have h := relIndex_mul_card_sylw PO_le_mog22
  rw [card_PO, card_mog22] at h
  omega

theorem isSylowIn_P2 :
    IsSylowIn 2 P2 mog22plus := by
  refine ⟨P2_le_mog22plus_sylw,
    IsPGroup.of_card (p := 2) (n := 8) (card_P2.trans (by norm_num)), ?_⟩
  have h := relIndex_mul_card_sylw P2_le_mog22plus_sylw
  rw [card_P2, card_mog22plus] at h
  omega

theorem exists_conj_of_isSylowIn_sylw {Γ T Q : Subgroup P24} (hT : IsSylowIn 2 T Γ)
    (hQ : IsSylowIn 2 Q Γ) : ∃ γ ∈ Γ, conjSubg γ T = Q := by
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq ↥Γ hT.toSylow hQ.toSylow
  have hA : MulAut.conj g • (T.subgroupOf Γ) = Q.subgroupOf Γ := by
    have h := congrArg (fun S : Sylow 2 ↥Γ => (S : Subgroup ↥Γ)) hg
    simpa only [Sylow.coe_subgroup_smul, IsSylowIn.coe_toSylow] using h
  refine ⟨(g : P24), g.2, ?_⟩
  ext x
  rw [mem_conjSubg_sylw]
  constructor
  · intro hx
    have e : (g : P24) * ((g : P24)⁻¹ * x * (g : P24)) * (g : P24)⁻¹ = x := by group
    have hxΓ : x ∈ Γ := by
      have h1 : (g : P24) * ((g : P24)⁻¹ * x * (g : P24)) * (g : P24)⁻¹ ∈ Γ :=
        Γ.mul_mem (Γ.mul_mem g.2 (hT.le hx)) (Γ.inv_mem g.2)
      rwa [e] at h1
    have hmem : (⟨x, hxΓ⟩ : ↥Γ) ∈ Q.subgroupOf Γ := by
      rw [← hA, Subgroup.mem_smul_pointwise_iff_exists]
      refine ⟨⟨(g : P24)⁻¹ * x * (g : P24), hT.le hx⟩, Subgroup.mem_subgroupOf.2 hx, ?_⟩
      apply Subtype.ext
      exact e
    exact Subgroup.mem_subgroupOf.1 hmem
  · intro hx
    have hmem : (⟨x, hQ.le hx⟩ : ↥Γ) ∈ Q.subgroupOf Γ := Subgroup.mem_subgroupOf.2 hx
    rw [← hA, Subgroup.mem_smul_pointwise_iff_exists] at hmem
    obtain ⟨w, hw, hwx⟩ := hmem
    have hwx' : (g : P24) * (w : P24) * (g : P24)⁻¹ = x := congrArg Subtype.val hwx
    have e : (g : P24)⁻¹ * x * (g : P24) = (w : P24) := by
      rw [← hwx']
      group
    rw [e]
    exact Subgroup.mem_subgroupOf.1 hw

theorem exists_conj_sylow_PO
    {T : Subgroup P24} (hT : IsSylowIn 2 T mog22) : ∃ γ ∈ mog22, conjSubg γ T = PO := by
  exact exists_conj_of_isSylowIn_sylw hT isSylowIn_PO

theorem exists_conj_sylow_P2
    {T : Subgroup P24} (hT : IsSylowIn 2 T mog22plus) : ∃ γ ∈ mog22plus, conjSubg γ T = P2 := by
  exact exists_conj_of_isSylowIn_sylw hT isSylowIn_P2

end CFSG.Quasithin.RonanH143
