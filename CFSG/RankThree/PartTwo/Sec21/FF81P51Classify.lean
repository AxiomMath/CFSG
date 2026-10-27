module

public import CFSG.RankThree.PartTwo.Sec21.FF81P51Checks

@[expose] public section

namespace CFSG.RankThree.PartTwo.Sec21.FF81.P51


theorem exists_mem_map_iff {α β : Type*} {f : α → β} {l : List α} {P : β → Prop} :
    (∃ b ∈ l.map f, P b) ↔ ∃ a ∈ l, P (f a) := by
  simp

theorem memOm_toV (c : CfgD) (x : V4) : memOm (toCfg c) x.toV = memOmD c x := by
  have : (x.toV ≠ 0) ↔ (x ≠ V4.zero) := not_congr V4.toV_eq_zero_iff
  simp only [memOm, memOmD, tab_toV, toCfg, decide_eq_decide.2 this]

theorem psiC_toV (c : CfgD) (x : V4) : psiC (toCfg c) x.toV = (psiCD c x).toV := by
  simp only [psiC, psiCD, tab_toV, toCfg, mv_eq, M16.toV_mulV]

theorem rC_toV (c : CfgD) (x : V4) : rC (toCfg c) x.toV = (rCD c x).toM := by
  simp only [rC, rCD, psiC_toV, refl_eq, M16.toM_refl]

theorem C1_iff (c : CfgD) : C1 (toCfg c) ↔ C1D c := by
  simp only [C1, C1D, nonzeroL_eq, List.forall_mem_map, rC_toV, mv_eq, ← M16.toV_mulV, memOm_toV,
    psiC_toV, vmm_eq, ← V4.toV_vmul, V4.toV_inj_iff]

theorem C3_iff (c : CfgD) : C3 (toCfg c) ↔ C3D c := by
  simp only [C3, C3D, nonzeroL_eq, exists_mem_map_iff, memOm_toV]
  rfl

theorem C4_iff (c : CfgD) (k : ℕ) : C4 (toCfg c) k ↔ C4D c k := by
  simp only [C4, C4D, C4a, C4aD, C4b, C4bD, nonzeroL_eq, List.forall_mem_map, rC_toV, mpow_eq,
    mm_eq, memOm_toV, T0_eqD, ← M16.toM_mul, ← M16.toM_pow, M16.toM_eq_one_iff]

theorem W_iff (c : CfgD) : W (toCfg c) ↔ WD c := by
  simp only [W, WD, nonzeroL_eq, exists_mem_map_iff, rC_toV, mm_eq, memOm_toV, Sig01_eqD,
    ← M16.toM_mul, toM_mem_H0L_iff]

theorem Good_iff (c : CfgD) : Good (toCfg c) ↔ GoodD c := by
  simp only [Good, GoodD, W_iff]
  rfl

theorem mkCfg_toV (m₁ m₂ m₄ m₅ m₆ : Bool) (p₁ p₂ p₄ p₅ p₆ : V4) :
    mkCfg m₁ m₂ m₄ m₅ m₆ p₁.toV p₂.toV p₄.toV p₅.toV p₆.toV =
      toCfg (mkCfgD m₁ m₂ m₄ m₅ m₆ p₁ p₂ p₄ p₅ p₆) := by
  refine Prod.ext rfl (funext fun k => ?_)
  fin_cases k
  all_goals first
    | rfl
    | exact V4.toV_zero.symm

theorem mem_optL {k : Fin 7} {m : Bool} {p : V} (h : p ∈ optL k m) :
    ∃ q ∈ optLD k m, q.toV = p := by
  cases m
  · simp only [optL, optLD, Bool.false_eq_true, if_false, List.mem_singleton] at h ⊢
    exact ⟨V4.zero, rfl, h ▸ V4.toV_zero⟩
  · simp only [optL, optLD, if_true, okL_eq, List.mem_map] at h ⊢
    exact h

theorem classify : ∀ m₁ m₂ m₄ m₅ m₆ : Bool, ∀ p₁ ∈ optL 1 m₁, ∀ p₂ ∈ optL 2 m₂,
    ∀ p₄ ∈ optL 4 m₄, ∀ p₅ ∈ optL 5 m₅, ∀ p₆ ∈ optL 6 m₆,
    C1 (mkCfg m₁ m₂ m₄ m₅ m₆ p₁ p₂ p₄ p₅ p₆) → C3 (mkCfg m₁ m₂ m₄ m₅ m₆ p₁ p₂ p₄ p₅ p₆) →
    C4 (mkCfg m₁ m₂ m₄ m₅ m₆ p₁ p₂ p₄ p₅ p₆) 2 → C4 (mkCfg m₁ m₂ m₄ m₅ m₆ p₁ p₂ p₄ p₅ p₆) 4 →
    Good (mkCfg m₁ m₂ m₄ m₅ m₆ p₁ p₂ p₄ p₅ p₆) := by
  intro m₁ m₂ m₄ m₅ m₆ p₁ h₁ p₂ h₂ p₄ h₄ p₅ h₅ p₆ h₆
  obtain ⟨q₁, hq₁, rfl⟩ := mem_optL h₁
  obtain ⟨q₂, hq₂, rfl⟩ := mem_optL h₂
  obtain ⟨q₄, hq₄, rfl⟩ := mem_optL h₄
  obtain ⟨q₅, hq₅, rfl⟩ := mem_optL h₅
  obtain ⟨q₆, hq₆, rfl⟩ := mem_optL h₆
  rw [mkCfg_toV, C1_iff, C3_iff, C4_iff, C4_iff, Good_iff]
  have hb : ∀ m : Bool, m ∈ [false, true] := by decide
  have h := classify_allD
  simp only [List.all_eq_true, decide_eq_true_eq] at h
  exact h m₁ (hb m₁) m₂ (hb m₂) m₄ (hb m₄) m₅ (hb m₅) m₆ (hb m₆) q₁ hq₁ q₂ hq₂ q₄ hq₄ q₅ hq₅ q₆ hq₆

end CFSG.RankThree.PartTwo.Sec21.FF81.P51
