module

public import CFSG.Quasithin.Background.E217Full.LemmaQ
public import CFSG.Quasithin.Vol2.GoldschmidtSp4C2WireE217

public section

namespace CFSG.Quasithin.E217Full

open CFSG.Open CFSG.QuasithinUnique E2

theorem qhatOf_autI_le_one {Γ : Type} [Group Γ] [Finite Γ] {V K : Subgroup Γ}
    (hV : IsElemAbelian 2 V) (hV16 : Nat.card V = 2 ^ 4) (hK : IsPGroup 2 K)
    (hKN : K ≤ Subgroup.normalizer (V : Set Γ))
    (h8 : 8 ≤ (K ⊓ Subgroup.centralizer (V : Set Γ)).relIndex K) :
    qhatOf (autI hV K) ≤ ((1 : ℚ) : WithTop ℚ) := by
  have hp : IsPGroup 2 (autI hV K) := by
    rw [← range_convHom hV K hKN]
    exact hK.of_surjective (convHom hV K hKN).rangeRestrict
      (MonoidHom.rangeRestrict_surjective _)
  refine LemmaQ.qhatOf_le_one IntMod.sq_eq_one ?_ hp ?_
  · change Nat.card V = 16
    rw [hV16]
    norm_num
  · rw [card_autI_eq hV hKN]
    exact h8

theorem relIndex_lt_eight {Γ : Type} [Group Γ] [Finite Γ] {H T M V : Subgroup Γ}
    (h : Hyp28 H T M V) (hq : qhatOf (autI h.elem H) = (((3 : ℚ) / 2 : ℚ) : WithTop ℚ))
    (hV16 : Nat.card V = 2 ^ 4) : (T ⊓ Subgroup.centralizer (V : Set Γ)).relIndex T < 8 := by
  by_contra hlt
  push_neg at hlt
  have hQ := qhatOf_autI_le_one h.elem hV16 h.minParabolic.isSylow.2.1 h.normal_T hlt
  have hmono : qhatOf (autI h.elem H) ≤ qhatOf (autI h.elem T) :=
    kq_le_kq_of_le216 (autI_mono h.elem h.minParabolic.isSylow.1) 3
  have h32 := hmono.trans hQ
  rw [hq] at h32
  have h32' : ((3 : ℚ) / 2 : ℚ) ≤ 1 := WithTop.coe_le_coe.mp h32
  norm_num at h32'

theorem e217Nonsolvable :
    E2.E217Nonsolvable := by
  intro Γ _ _ H T M V h hchar hTI hq hres hV hns
  exact Or.inl (Ch3E213M.Sp4C2.e217NonsolvableNarrow_holds Γ H T M V h hchar hTI hq hres hV hns
    (relIndex_lt_eight h hq hV))

end CFSG.Quasithin.E217Full
