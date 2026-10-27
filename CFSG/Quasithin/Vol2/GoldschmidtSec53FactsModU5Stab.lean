module

public import CFSG.LocalAnalysis.EvenBN.U5.ModelSylow

public section

namespace CFSG.Quasithin.H13.Sec53F.Unit

open scoped Pointwise
open Matrix CFSG.ClassicalGroups.UnitaryFlag CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher CFSG.RankThree.PartOne.U5K.Hyp
  CFSG.LocalAnalysis.EvenBN.U5

variable {p f : ℕ} {K : Type} [Field K] {r ε : ℕ}

theorem mem_isoStabilizer_posFlag_iff (h : UnitaryFieldData p f K) (g : hypSU h r ε) (i : ℕ) :
    g ∈ isoStabilizer h r ε (posFlag r ε K i) ↔ ∀ a b : HypIndex r ε, fullPos b < i →
      i ≤ fullPos a → ((g : GL (HypIndex r ε) K) : Matrix (HypIndex r ε) (HypIndex r ε) K) a b
        = 0 := by
  rw [mem_isoStabilizer]
  constructor
  · intro hg a b hb ha
    have hs : (Pi.single b 1 : HypIndex r ε → K) ∈ posFlag r ε K i := by
      intro c hc
      have : c ≠ b := by
        rintro rfl
        omega
      simp [this]
    have h1 : (g : GL (HypIndex r ε) K) • (Pi.single b 1 : HypIndex r ε → K) ∈
        (g : GL (HypIndex r ε) K) • posFlag r ε K i :=
      Submodule.smul_mem_pointwise_smul _ _ _ hs
    rw [← Subgroup.smul_def, hg] at h1
    have h2 := h1 a ha
    change (((g : GL (HypIndex r ε) K) : Matrix (HypIndex r ε) (HypIndex r ε) K) *ᵥ
      Pi.single b 1) a = 0 at h2
    rwa [mulVec_single_one, col_apply] at h2
  · intro hg
    have hle : g • posFlag r ε K i ≤ posFlag r ε K i := by
      intro x hx
      obtain ⟨y, hy, rfl⟩ := (Submodule.mem_smul_pointwise_iff_exists x _ (posFlag r ε K i)).mp hx
      intro a ha
      change (((g : GL (HypIndex r ε) K) : Matrix (HypIndex r ε) (HypIndex r ε) K) *ᵥ y) a = 0
      rw [mulVec, dotProduct]
      refine Finset.sum_eq_zero fun c _ => ?_
      by_cases hc : i ≤ fullPos c
      · rw [hy c hc, mul_zero]
      · rw [hg a c (not_le.mp hc) ha, zero_mul]
    exact Submodule.eq_of_le_of_finrank_eq hle (finrank_smul g _)

variable {h : UnitaryFieldData 2 f K}

noncomputable abbrev u5PtStab (h : UnitaryFieldData 2 f K) : Subgroup (hypSU h 2 1) :=
  isoStabilizer h 2 1 (hypFlag h 2 1 1)

noncomputable abbrev u5LnStab (h : UnitaryFieldData 2 f K) : Subgroup (hypSU h 2 1) :=
  isoStabilizer h 2 1 (hypFlag h 2 1 2)

theorem mem_u5PtStab_iff (g : hypSU h 2 1) :
    g ∈ u5PtStab h ↔ ∀ a, a ≠ ιe₁ → mat g a ιe₁ = 0 := by
  have hF : hypFlag h 2 1 1 = posFlag 2 1 K 1 := hypFlag_eq_posFlag h le_rfl (by norm_num)
  rw [u5PtStab, hF, mem_isoStabilizer_posFlag_iff]
  constructor
  · intro hg a ha
    exact hg a ιe₁ (by simp [ιe₁]) (by
      revert a ha
      decide)
  · intro hg a b hb ha
    have : b = ιe₁ := by
      revert b hb
      decide
    subst this
    exact hg a (by
      rintro rfl
      simp [ιe₁] at ha)

theorem mem_u5LnStab_iff (g : hypSU h 2 1) : g ∈ u5LnStab h ↔
    ∀ a b : HypIndex 2 1, (b = ιe₁ ∨ b = ιe₂) → (a = ιz ∨ a = ιf₂ ∨ a = ιf₁) →
      mat g a b = 0 := by
  have hF : hypFlag h 2 1 2 = posFlag 2 1 K 2 := hypFlag_eq_posFlag h le_rfl (by norm_num)
  rw [u5LnStab, hF, mem_isoStabilizer_posFlag_iff]
  have hb : ∀ b : HypIndex 2 1, fullPos b < 2 ↔ (b = ιe₁ ∨ b = ιe₂) := by decide
  have ha : ∀ a : HypIndex 2 1, 2 ≤ fullPos a ↔ (a = ιz ∨ a = ιf₂ ∨ a = ιf₁) := by decide
  simp only [hb, ha]
  rfl

theorem hypIndex_cases (a : HypIndex 2 1) :
    a = ιe₁ ∨ a = ιe₂ ∨ a = ιz ∨ a = ιf₂ ∨ a = ιf₁ := by
  revert a
  decide

theorem two_lt_two_pow {f : ℕ} (hf : 2 ≤ f) : 2 < 2 ^ f :=
  lt_of_lt_of_le (by norm_num) (Nat.pow_le_pow_right (by norm_num) hf : 2 ^ 2 ≤ 2 ^ f)

theorem zpow_val_ne_of_le {ω : Kˣ} (hω : orderOf ω = (2 ^ f) ^ 2 - 1) (hf : 2 ≤ f) {m n : ℤ}
    (h0 : m ≠ n) (h1 : m - n ≤ 2 * ((2 ^ f : ℕ) : ℤ)) (h2 : n - m ≤ 2 * ((2 ^ f : ℕ) : ℤ)) :
    ((ω ^ m : Kˣ) : K) ≠ ((ω ^ n : Kˣ) : K) := by
  have hq := four_le_q hf
  refine zpow_val_ne hω 0 ?_ ?_ ?_
  · simpa [sub_eq_zero] using h0
  · simp only [zero_mul, sub_zero]
    nlinarith
  · simp only [zero_mul, sub_zero]
    nlinarith

theorem bar_eq_of_mem_ZPsub {z : hypSU h 2 1} (hz : z ∈ ZPsub h) :
    h.bar (mat z ιe₁ ιf₁) = mat z ιe₁ ιf₁ := by
  obtain ⟨hzU, a1, a2, a3, a4, a5, a6, a7, a8, a9⟩ := mem_ZPsub.1 hz
  obtain ⟨-, -, -, -, -, r6⟩ := U_rel hzU
  rw [a1, a3, a7] at r6
  exact bar_eq_of_add_eq_zero h (by simpa using r6)

end CFSG.Quasithin.H13.Sec53F.Unit
