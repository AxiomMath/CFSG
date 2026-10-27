module

public import CFSG.LocalAnalysis.WeakClosure81.FiveTenLiftKer
public import CFSG.LocalAnalysis.WeakClosure81.FiveTenQuotSylow
import all CFSG.LocalAnalysis.WeakClosure81.FiveDefs

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.Quasithin CFSG.Open Subgroup

variable {G : Type} [Group G] [Finite G]

theorem isInvColl_kerQuotOmega {M H : Subgroup G} {Ω : Set (Subgroup G)}
    (hΩ : E1.IsInvColl H Ω) :
    E1.IsInvColl (⊤ : Subgroup (KerQuot M H)) (kerQuotOmega M H Ω) where
  le B _ := le_top
  isElemAbelian B hB := by
    obtain ⟨A, hA, rfl⟩ := hB
    exact isElemAbelian_kerQuotImg (hΩ.isElemAbelian A hA)
  conj B hB q _ := by
    obtain ⟨A, hA, rfl⟩ := hB
    obtain ⟨y, rfl⟩ := kerQuotMk_surjective M H q
    exact ⟨A1b.conjSub (y : G) A, hΩ.conj A hA y y.2, kerQuotImg_conjSub y.2⟩

theorem isSylowIn_kerQuotImg {M H T : Subgroup G} (hT : IsSylowIn 2 T H) :
    IsSylowIn 2 (kerQuotImg M H T) ⊤ := by
  refine ⟨le_top, ?_, ?_⟩
  · have h1 : IsPGroup 2 (T.subgroupOf H) :=
      hT.isPGroup.of_equiv (Subgroup.subgroupOfEquivOfLe hT.le).symm
    exact h1.map (kerQuotMk M H)
  · rw [Subgroup.relIndex_top_right]
    intro hd
    apply hT.not_dvd_relIndex
    refine hd.trans ?_
    exact Subgroup.index_map_dvd (T.subgroupOf H) (kerQuotMk_surjective M H)

theorem kerQuotImg_conjSub_weakClosure {M H T : Subgroup G} {Ω : Set (Subgroup G)}
    (hΩ : E1.IsInvColl H Ω) (hTH : T ≤ H) {y : G} (hy : y ∈ T ⊔ kerMOf M H) :
    kerQuotImg M H (A1b.conjSub y (E1.weakClosure T Ω)) =
      kerQuotImg M H (E1.weakClosure T Ω) := by
  have hyH : y ∈ H := sup_le hTH (kerMOf_le_group M H) hy
  have hyq : y ∈ kerQuotLift M H (kerQuotImg M H T) := by
    rw [kerQuotLift_kerQuotImg hTH]
    exact hy
  obtain ⟨hyH', hmem⟩ := mem_kerQuotLift_iff.1 hyq
  obtain ⟨t, ht, htq⟩ := hmem
  have htT : (t : G) ∈ T := ht
  have hnorm : (t : G) ∈ normalizer (E1.weakClosure T Ω : Set G) :=
    le_normalizer_weakClosure_of_isInvColl hΩ hTH htT
  have h1 : A1b.conjSub (t : G) (E1.weakClosure T Ω) = E1.weakClosure T Ω :=
    B6.conjSub_eq_self hnorm
  rw [kerQuotImg_conjSub hyH, ← htq, ← kerQuotImg_conjSub t.2, h1]

theorem weakClosure_kerQuotOmega {M H T : Subgroup G} {Ω : Set (Subgroup G)}
    (hΩ : E1.IsInvColl H Ω) (hT : IsSylowIn 2 T H) :
    E1.weakClosure (kerQuotImg M H T) (kerQuotOmega M H Ω) =
      kerQuotImg M H (E1.weakClosure T Ω) := by
  have hTH : T ≤ H := hT.le
  have hWT : E1.weakClosure T Ω ≤ T := E1.weakClosure_le
  have hWH : E1.weakClosure T Ω ≤ H := hWT.trans hTH
  refine le_antisymm ?_ ?_
  · refine iSup₂_le fun B hB => iSup_le fun hBT => ?_
    obtain ⟨A, hA, rfl⟩ := hB
    have hAH : A ≤ H := hΩ.le A hA
    have hAJ : A ≤ T ⊔ kerMOf M H := by
      rw [← kerQuotLift_kerQuotImg hTH]
      exact (le_kerQuotLift_iff hAH).2 hBT
    have hTJH : T ⊔ kerMOf M H ≤ H := sup_le hTH (kerMOf_le_group M H)
    have hTsyl : IsSylowIn 2 T (T ⊔ kerMOf M H) :=
      E1.isSylowIn_two_iff.2 (B6.isSylowTwoOf_mono (E1.isSylowIn_two_iff.1 hT)
        le_sup_left hTJH)
    obtain ⟨y, hy, hyA⟩ := exists_conjSub_le_of_isSylowIn hTsyl le_sup_left
      (hΩ.isElemAbelian A hA).isPGroup hAJ hAJ
    have hyJ : y ∈ T ⊔ kerMOf M H := (Subgroup.mem_inf.1 hy).1
    have hyH : y ∈ H := hTJH hyJ
    have hyW : A1b.conjSub y A ≤ E1.weakClosure T Ω :=
      E1.le_weakClosure (hΩ.conj A hA y hyH) hyA
    have hAW : A ≤ A1b.conjSub y⁻¹ (E1.weakClosure T Ω) := by
      have := A1b.conjSub_mono y⁻¹ hyW
      rwa [← A1b.conjSub_mul, inv_mul_cancel, A1b.conjSub_one] at this
    have hyinv : y⁻¹ ∈ T ⊔ kerMOf M H := Subgroup.inv_mem _ hyJ
    calc kerQuotImg M H A ≤ kerQuotImg M H (A1b.conjSub y⁻¹ (E1.weakClosure T Ω)) :=
          kerQuotImg_mono hAW
      _ = kerQuotImg M H (E1.weakClosure T Ω) :=
          kerQuotImg_conjSub_weakClosure hΩ hTH hyinv
  · refine (le_kerQuotLift_iff hWH).1 ?_
    refine iSup₂_le fun A hA => iSup_le fun hAT => ?_
    exact (le_kerQuotLift_iff (hΩ.le A hA)).2
      (E1.le_weakClosure ⟨A, hA, rfl⟩ (kerQuotImg_mono hAT))

theorem fiveTenHyp_kerQuot {H M T : Subgroup G} {Ω : Set (Subgroup G)}
    (h : FiveTenHyp H M T Ω) :
    FiveTenHyp (⊤ : Subgroup (KerQuot M H)) (kerQuotImg M H M) (kerQuotImg M H T)
      (kerQuotOmega M H Ω) where
  invColl := isInvColl_kerQuotOmega h.invColl
  sylow := isSylowIn_kerQuotImg h.sylow
  normalizer_le := by
    intro q hq
    have hqN := (Subgroup.mem_inf.1 hq).2
    rw [weakClosure_kerQuotOmega h.invColl h.sylow] at hqN
    obtain ⟨y, rfl⟩ := kerQuotMk_surjective M H q
    have hWH : E1.weakClosure T Ω ≤ H := E1.weakClosure_le.trans h.sylow.le
    have hyJ : (y : G) ∈ normalizer
        ((E1.weakClosure T Ω ⊔ kerMOf M H : Subgroup G) : Set G) := by
      have := mem_normalizer_kerQuotLift y.2 hqN
      rwa [kerQuotLift_kerQuotImg hWH] at this
    have hyM : (y : G) ∈ M := mem_of_mem_normalizer_weakClosure_sup h y.2 hyJ
    exact ⟨y, hyM, rfl⟩
  not_le := by
    intro htop
    apply h.not_le
    intro x hxH
    have hmem : kerQuotMk M H ⟨x, hxH⟩ ∈ kerQuotImg M H M := htop (Subgroup.mem_top _)
    have : x ∈ kerQuotLift M H (kerQuotImg M H M) := mem_kerQuotLift_iff.2 ⟨hxH, hmem⟩
    rw [kerQuotLift_kerQuotImg_left] at this
    exact (Subgroup.mem_inf.1 this).1

theorem card_kerQuot_lt {M H : Subgroup G} (hJ : kerMOf M H ≠ ⊥) :
    Nat.card (⊤ : Subgroup (KerQuot M H)) < Nat.card H := by
  rw [Subgroup.card_top]
  have h1 := Subgroup.card_eq_card_quotient_mul_card_subgroup (M.subgroupOf H).normalCore
  have hne : (M.subgroupOf H).normalCore ≠ ⊥ := by
    intro hbot
    apply hJ
    rw [eq_bot_iff]
    intro x hx
    have hxH : x ∈ H := kerMOf_le_group M H hx
    have hx' : (⟨x, hxH⟩ : ↥H) ∈ (M.subgroupOf H).normalCore := by
      rw [← subgroupOf_kerMOf M H]
      exact hx
    rw [hbot] at hx'
    have h2 : (⟨x, hxH⟩ : ↥H) = 1 := Subgroup.mem_bot.1 hx'
    exact Subgroup.mem_bot.2 (congrArg Subtype.val h2)
  have h2 : 1 < Nat.card ((M.subgroupOf H).normalCore) := (Subgroup.one_lt_card_iff_ne_bot _).2 hne
  have h3 : 0 < Nat.card (KerQuot M H) := Nat.card_pos
  calc Nat.card (KerQuot M H) = Nat.card (KerQuot M H) * 1 := (mul_one _).symm
    _ < Nat.card (KerQuot M H) * Nat.card ((M.subgroupOf H).normalCore) :=
        Nat.mul_lt_mul_of_pos_left h2 h3
    _ = Nat.card H := h1.symm

end CFSG.LocalAnalysis.WeakClosure81
