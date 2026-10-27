module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.HJ12Objects
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.HJ12Spec
public import CFSG.Sporadic.He.Setup

@[expose] public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719

open CFSG.Quasithin Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22
open CFSG.GF2Type.Smith1979.GammaU (vecOf)
open HJ12 (wordR)

theorem hjX7_facts :
    hjX7 ∈ hjL0 ∧ orderOf hjX7 = 7 ∧ fixV (Subgroup.zpowers hjX7) = ⊥ := by
  have h : HJ12.hjX7Check = true := HJ12.hjX7Check_eq
  simp only [HJ12.hjX7Check, Bool.and_eq_true, beq_iff_eq,
    CFSG.GF2Type.Smith1979.GammaU.StepA.native_mulR,
    CFSG.GF2Type.Smith1979.GammaU.StepA.native_idR] at h
  obtain ⟨⟨h7, -⟩, hfix⟩ := h
  have hr : HJBridge.RowsOf hjX7 (wordR HJ12.hj_x7Word) := HJBridge.rowsOf_hjWord _
  have hcard : Nat.card (fixV (Subgroup.zpowers hjX7)) = 1 := by
    rw [HJBridge.card_fixV_zpowers hr (HJBridge.wordR_canon _).2]
    exact congrArg List.length hfix
  have hbot : fixV (Subgroup.zpowers hjX7) = ⊥ := Subgroup.eq_bot_of_card_eq _ hcard
  refine ⟨hjWord_mem _, orderOf_eq_prime ?_ ?_, hbot⟩
  · have e : hjX7 ^ 7 = hjX7 * hjX7 * (hjX7 * hjX7) * (hjX7 * hjX7 * hjX7) := by
      simp only [pow_succ, pow_zero, one_mul, mul_assoc]
    rw [e]
    have h' := HJBridge.rowsOf_mul
      (HJBridge.rowsOf_mul (HJBridge.rowsOf_mul hr hr) (HJBridge.rowsOf_mul hr hr))
      (HJBridge.rowsOf_mul (HJBridge.rowsOf_mul hr hr) hr)
    rw [h7] at h'
    exact HJBridge.rowsOf_unique h' HJBridge.rowsOf_one
  · intro h1
    have hmem : Multiplicative.ofAdd (vecOf 1) ∈ fixV (Subgroup.zpowers hjX7) :=
      (HJBridge.mem_fixV_zpowers_iff _ _).2 (by rw [h1]; rfl)
    rw [hbot, Subgroup.mem_bot] at hmem
    exact absurd (congrArg (fun w : W12 => Multiplicative.toAdd w 0) hmem) (by decide)

theorem hjP3_facts :
    hjP3 ≤ hjL0 ∧ Nat.card hjP3 = 27 ∧
      ∀ c ∈ Subgroup.zpowers hjOmega, ∀ p ∈ hjP3, c * p ≠ 1 →
        4 ≤ rk (commSub (⊤ : Subgroup W12) (Subgroup.zpowers (c * p))) := by
  classical
  have h : HJ12.hjP3Check = true := HJ12.hjP3Check_eq
  simp only [HJ12.hjP3Check, Bool.and_eq_true, beq_iff_eq, gensOKN_eq,
    CFSG.GF2Type.Smith1979.GammaU.StepA.native_closedCheck,
    CFSG.GF2Type.Smith1979.GammaU.native_enumGrp,
    CFSG.GF2Type.Smith1979.GammaU.StepA.native_mulR,
    CFSG.GF2Type.Smith1979.GammaU.StepA.native_idR] at h
  obtain ⟨⟨⟨⟨hg, hc⟩, h27⟩, -⟩, hall⟩ := h
  have hle : hjP3 ≤ hjL0 := by
    rw [hjP3, HJBridge.grpOf_words, Subgroup.closure_le]
    rintro _ ⟨w, -, rfl⟩
    exact hjWord_mem w
  refine ⟨hle, by rw [hjP3, HJBridge.card_grpOf_eq hg hc, h27], ?_⟩
  intro c hc' p hp hcp
  have hJlt : ∀ y ∈ HJ12.hjJc, y < 4096 := by decide
  have hcr : ∃ cr ∈ [CFSG.GF2Type.Smith1979.GammaU.StepA.idR, HJ12.hjJc,
      CFSG.GF2Type.Smith1979.GammaU.StepA.mulR HJ12.hjJc HJ12.hjJc],
      HJBridge.RowsOf c cr ∧ ∀ y ∈ cr, y < 4096 := by
    have hk := (mem_zpowers_iff_mem_range_orderOf (x := hjOmega)).1 hc'
    rw [Finset.mem_image] at hk
    obtain ⟨k, hk, rfl⟩ := hk
    rw [Finset.mem_range, orderOf_hjOmega] at hk
    interval_cases k
    · exact ⟨_, List.mem_cons_self, by rw [pow_zero]; exact HJBridge.rowsOf_one, by decide⟩
    · exact ⟨_, List.mem_cons_of_mem _ List.mem_cons_self, by rw [pow_one]; exact rowsOf_hjOmega,
        hJlt⟩
    · refine ⟨_, List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self), ?_,
        mulR_lt hJlt⟩
      rw [pow_two]
      exact HJBridge.rowsOf_mul rowsOf_hjOmega rowsOf_hjOmega
  obtain ⟨cr, hcrm, hcrR, hcrlt⟩ := hcr
  obtain ⟨r, hr, hpr⟩ := (HJBridge.mem_grpOf_iff hg hc p).1 hp
  have hcpr := HJBridge.rowsOf_mul hcrR hpr
  have h1 := List.all_eq_true.1 hall cr hcrm
  have h2 := List.all_eq_true.1 h1 r hr
  simp only [Bool.or_eq_true, beq_iff_eq] at h2
  rcases h2 with h2 | h2
  · exact absurd (HJBridge.rowsOf_unique (h2 ▸ hcpr) HJBridge.rowsOf_one) hcp
  · apply four_le_rk_of_card_fixV_le
    rw [HJBridge.card_fixV_zpowers hcpr (mulR_lt hcrlt)]
    exact of_decide_eq_true h2

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719
