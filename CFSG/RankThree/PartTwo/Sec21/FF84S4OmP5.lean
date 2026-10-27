module

public import CFSG.RankThree.PartTwo.Sec21.FF84S4OmP2
public import CFSG.RankThree.PartTwo.Sec21.FF84S4OmP4

public section

namespace CFSG.RankThree.PartTwo.Sec21.FF84.S4

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

open CFSG.ComponentClassification.AS81 CFSG.ComponentClassification.AS81.Sec2Omega
  CFSG.ClassicalGroups.Orthogonal MulAction

theorem nlU_span_perp : ∀ x : F6, polarMinus x tau0 = 0 →
    ∃ c : ZMod 2, ∃ a ∈ (0 :: nlU), ∃ a' ∈ (0 :: nlU), x = c • tau0 + a + a' := by
  decide +kernel

theorem projT_perp : ∀ w : F6, polarMinus w tau0 = 0 →
    polarMinus (w + polarMinus w sig0 • tau0) sig0 = 0 ∧
      polarMinus (w + polarMinus w sig0 • tau0) tau0 = 0 := by
  decide +kernel

theorem projT_zero : ∀ w : F6, polarMinus w tau0 = 0 →
    w + polarMinus w sig0 • tau0 = 0 → w = 0 ∨ w = tau0 := by
  decide +kernel

theorem eichVec_one : ∀ z w : F6, polarMinus z tau0 = 1 →
    eichVec z w = w + (polarMinus z w + qMinus w) • tau0 := by
  decide +kernel

theorem polarMinus_add_tau0 : ∀ x z : F6, polarMinus x tau0 = 1 → polarMinus z tau0 = 1 →
    polarMinus (x + z) tau0 = 0 := by
  decide +kernel

theorem zmod_two_eq_one_of_ne_zero : ∀ c : ZMod 2, c ≠ 0 → c = 1 := by decide

theorem stab_inv_subspace {W : Submodule (ZMod 2) F6} (ht : tau0 ∈ W)
    (hW : ∀ g : OmG, g • tau0 = tau0 → ∀ w ∈ W, g • w ∈ W) :
    W = Submodule.span (ZMod 2) {tau0} ∨ (∀ x, x ∈ W ↔ polarMinus x tau0 = 0) ∨ W = ⊤ := by
  by_cases hperp : ∀ w ∈ W, polarMinus w tau0 = 0
  · by_cases hsmall : ∀ w ∈ W, w = 0 ∨ w = tau0
    · left
      refine le_antisymm (fun w hw => ?_) (Submodule.span_le.mpr ?_)
      · rcases hsmall w hw with rfl | rfl
        · exact Submodule.zero_mem _
        · exact Submodule.mem_span_singleton_self _
      · intro x hx
        rw [Set.mem_singleton_iff] at hx
        rw [hx]
        exact ht
    · right
      left
      push Not at hsmall
      obtain ⟨w, hwW, hw0, hwt⟩ := hsmall
      have hwp := hperp w hwW
      have hrr : ∀ a ∈ nlU, ∀ b ∈ nlU, ∀ x ∈ W, transv a (transv b x) ∈ W := by
        intro a ha b hb x hx
        have ha' := nlU_spec a ha
        have hb' := nlU_spec b hb
        have h := hW (rrOm ha'.1 hb'.1) (by rw [rrOm_smul]; exact (nlU_fix a ha b hb).2) x hx
        rwa [rrOm_smul] at h
      have hyW : w + polarMinus w sig0 • tau0 ∈ W := W.add_mem hwW (W.smul_mem _ ht)
      have hy0 : w + polarMinus w sig0 • tau0 ≠ 0 := fun h =>
        (projT_zero w hwp h).elim hw0 hwt
      have hall := nlU_all_mem hrr hyW (projT_perp w hwp).1 (projT_perp w hwp).2 hy0
      have hall0 : ∀ a' ∈ (0 :: nlU), a' ∈ W := by
        intro a' ha'
        rcases List.mem_cons.mp ha' with rfl | h
        · exact W.zero_mem
        · exact hall a' h
      intro x
      refine ⟨hperp x, fun hx => ?_⟩
      obtain ⟨c, a₁, ha₁, a₂, ha₂, rfl⟩ := nlU_span_perp x hx
      exact W.add_mem (W.add_mem (W.smul_mem _ ht) (hall0 _ ha₁)) (hall0 _ ha₂)
  · right
    right
    push Not at hperp
    obtain ⟨z, hzW, hz⟩ := hperp
    have hz1 := zmod_two_eq_one_of_ne_zero _ hz
    have hperpW : ∀ w : F6, polarMinus w tau0 = 0 → w ∈ W := by
      intro w hw
      have h1 := hW (eichOm w) (eichOm_smul_tau0 w) z hzW
      have h2 := W.sub_mem h1 hzW
      rw [eichOm_smul_sub hw z, eichVec_one z w hz1] at h2
      have h3 := W.sub_mem h2 (W.smul_mem (polarMinus z w + qMinus w) ht)
      rwa [add_sub_cancel_right] at h3
    rw [eq_top_iff]
    intro x _
    rcases (by decide : ∀ c : ZMod 2, c = 0 ∨ c = 1) (polarMinus x tau0) with h | h
    · exact hperpW x h
    · have h2 := hperpW (x + z) (polarMinus_add_tau0 x z h hz1)
      have h3 := W.sub_mem h2 hzW
      rwa [add_sub_cancel_right] at h3

end CFSG.RankThree.PartTwo.Sec21.FF84.S4

end
