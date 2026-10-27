
module

public import CFSG.Quasithin.Vol2.KGFactC31Hex

public section

namespace CFSG.Quasithin.KGC31.A7

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin.KGC31 CFSG.Quasithin.KGC31.Hex

theorem card_alt7 : Nat.card (alternatingGroup (Fin 7)) = 2520 := by
  rw [Nat.card_eq_fintype_card, card_alternatingGroup, Fintype.card_fin]
  decide

theorem eq_alt7_of_card {H : Subgroup (Equiv.Perm (Fin 7))} (h : Nat.card H = 2520) :
    H = alternatingGroup (Fin 7) := by
  have hi : H.index = 2 := by
    have h1 := H.card_mul_index
    rw [h, Nat.card_eq_fintype_card, Fintype.card_perm, Fintype.card_fin] at h1
    have : Nat.factorial 7 = 5040 := by decide
    omega
  have hle : alternatingGroup (Fin 7) ≤ H := by
    rw [← Equiv.Perm.closure_three_cycles_eq_alternating, Subgroup.closure_le]
    intro c hc
    have h3 : c ^ 3 = 1 := by rw [← hc.orderOf]; exact pow_orderOf_eq_one c
    have hc4 : c = (c ^ 2) ^ 2 := by
      rw [← pow_mul, show 2 * 2 = 3 + 1 by norm_num, pow_add, h3, one_mul, pow_one]
    rw [SetLike.mem_coe, hc4]
    exact Subgroup.sq_mem_of_index_two hi _
  exact (Subgroup.eq_of_le_of_card_ge hle (by rw [h, card_alt7])).symm

theorem alt7_simple : IsSimpleGroup (alternatingGroup (Fin 7)) :=
  alternatingGroup.isSimpleGroup (by simp)

theorem alt7_nonabelian : ∃ x y : alternatingGroup (Fin 7), x * y ≠ y * x := by
  refine ⟨⟨Equiv.swap 0 1 * Equiv.swap 1 2, Equiv.Perm.mem_alternatingGroup.mpr (by decide)⟩,
    ⟨Equiv.swap 1 2 * Equiv.swap 2 3, Equiv.Perm.mem_alternatingGroup.mpr (by decide)⟩,
    fun h => ?_⟩
  have := congrArg Subtype.val h
  revert this
  decide

variable {Γ : Type} [Group Γ] [Finite Γ] {v : Fin 4 → Γ} (hv : EBasis v)

theorem isExcA7Block_of {L : Subgroup Γ} (hperf : ⁅L, L⁆ = L) (hO : pCoreOf 2 L = eSub hv)
    (hcomm : ⁅eSub hv, L⁆ = eSub hv)
    (hC : L ⊓ Subgroup.centralizer (eSub hv : Set Γ) ≤ eSub hv)
    (α : ↥L →* alternatingGroup (Fin 7)) (hsurj : Function.Surjective α)
    (hker : α.ker = (eSub hv).subgroupOf L)
    (hirr : ∀ W : Subgroup Γ, W ≤ eSub hv → L ≤ Subgroup.normalizer (W : Set Γ) →
      W = ⊥ ∨ W = eSub hv) :
    IsExcA7Block L ∧ IsExt ↥L (fun N _ => IsE2 4 N) (fun Y _ => IsAlt 7 Y) := by
  have hVL : eSub hv ≤ L := hO ▸ CFSG.LieType.BorelTits.pCoreOf_le 2 L
  have hpL : Group.IsPerfect ↥L := Subgroup.isPerfect_iff.mpr hperf
  have hpk : α.ker = CFSG.pCore 2 ↥L := by rw [hker, ← hO, pCoreOf_subgroupOf']
  have hU : blockU L = eSub hv := by rw [blockU, blockQ, hO, hcomm]
  have hZ : blockZ L = ⊥ := by
    have hZV : blockZ L ≤ eSub hv := hU ▸ inf_le_left
    have hLZ : L ≤ Subgroup.normalizer (blockZ L : Set Γ) := by
      intro l hl
      rw [Subgroup.mem_normalizer_iff]
      intro z
      constructor
      · intro hz
        have hzl : l * z * l⁻¹ = z := by
          rw [Subgroup.mem_centralizer_iff.mp hz.2 l hl, mul_inv_cancel_right]
        rw [hzl]
        exact hz
      · intro hz
        have h1 := Subgroup.mem_centralizer_iff.mp hz.2 l hl
        have h2 : l⁻¹ * (l * z * l⁻¹) * l = l * z * l⁻¹ := by
          rw [mul_assoc, ← h1, ← mul_assoc, inv_mul_cancel, one_mul]
        have : z = l * z * l⁻¹ := by
          rw [← h2]
          group
        rw [this]
        exact hz
    rcases hirr _ hZV hLZ with h | h
    · exact h
    · exfalso
      have hLV : L ≤ eSub hv := by
        intro l hl
        refine hC ⟨hl, Subgroup.mem_centralizer_iff.mpr fun x hx => ?_⟩
        have hx' : x ∈ blockZ L := h ▸ hx
        exact (Subgroup.mem_centralizer_iff.mp hx'.2 l hl).symm
      obtain ⟨x, y, hxy⟩ := alt7_nonabelian
      obtain ⟨a, rfl⟩ := hsurj x
      have ha : α a = 1 := by
        rw [← MonoidHom.mem_ker, hker, Subgroup.mem_subgroupOf]
        exact hLV a.2
      exact hxy (by rw [ha, one_mul, mul_one])
  let eQ : ↥L ⧸ CFSG.pCore 2 ↥L ≃* alternatingGroup (Fin 7) :=
    (QuotientGroup.quotientMulEquivOfEq hpk.symm).trans
      (QuotientGroup.quotientKerEquivOfSurjective α hsurj)
  have hshort : IsShort2 L := by
    refine ⟨fun N _ hN => eq_top_of_isPGroup_quot' N hN, ?_, ⟨?_, ?_⟩, Or.inl ?_, ?_⟩
    · unfold CharTwo
      rw [hO]
      exact hC
    · rw [hU, blockQ, hO]
      exact le_inf le_rfl fun x hx => Subgroup.mem_centralizer_iff.mpr fun y hy =>
        eSub_comm hv _ _ hy hx
    · intro x hx
      rw [hU] at hx
      rw [sq]
      exact eSub_sq hv x hx
    · have hs : IsSimpleGroup (↥L ⧸ CFSG.pCore 2 ↥L) := by
        have := alt7_simple
        exact eQ.isSimpleGroup
      refine isQuasisimple_of_simple hs ?_
      obtain ⟨x, y, hxy⟩ := alt7_nonabelian
      refine ⟨eQ.symm x, eQ.symm y, fun h => hxy ?_⟩
      have := congrArg eQ h
      simpa using this
    · refine ⟨?_, fun W hZW hWV hLW => ?_⟩
      · rw [hZ, hU]
        refine bot_lt_iff_ne_bot.mpr fun h => ?_
        have := card_eSub hv
        rw [h, Subgroup.card_bot] at this
        norm_num at this
      · rw [hZ]
        rw [hU] at hWV ⊢
        exact hirr W hWV hLW
  refine ⟨⟨hshort, ⟨α, hsurj, hpk⟩, ?_⟩, ?_⟩
  · rw [hZ, Subgroup.bot_subgroupOf, Subgroup.index_bot, hU, card_eSub]
  · have hn : ((eSub hv).subgroupOf L).Normal := by rw [← hker]; exact α.normal_ker
    exact ⟨(eSub hv).subgroupOf L, hn, ⟨(Subgroup.subgroupOfEquivOfLe hVL).trans (coords hv)⟩,
      ⟨(QuotientGroup.quotientMulEquivOfEq hker.symm).trans
        (QuotientGroup.quotientKerEquivOfSurjective α hsurj)⟩⟩

end CFSG.Quasithin.KGC31.A7

end
