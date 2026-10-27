module

public import CFSG.LocalAnalysis.StandardType.FF81.ConstructYSix
import CFSG.ClassicalInvolution.WeakCT.SpCharts
import CFSG.ClassicalInvolution.WeakCT.Blocks
import CFSG.ClassicalInvolution.WeakCT.Standard

public section

namespace CFSG.StandardType.FF81

open CFSG.ClassicalInvolution.WeakCT
open scoped MatrixGroups

variable {G : Type} [Group G]

omit [Group G] in
private theorem lbsp_symm {X : Type} [Group X] {W U V : Subgroup X}
    (h : LinearBlockStandardPair (ZMod 2) W U V) : LinearBlockStandardPair (ZMod 2) W V U := by
  obtain ⟨θ, c, h1, h2, h3 | h3⟩ := h
  · exact ⟨θ, c, h1, h2, Or.inr ⟨h3.1, h3.2⟩⟩
  · exact ⟨θ, c, h1, h2, Or.inl ⟨h3.1, h3.2⟩⟩

private theorem blockSL_index_congr {K : Type} [Field K] {m k i i' : ℕ} (h : i + k ≤ m)
    (hii : i = i') (A : SL(k, K)) :
    blockSL K m k i h A = blockSL K m k i' (hii ▸ h) A := by
  subst hii
  rfl

theorem exists_injective_of_two_charts {M : ℕ} (hM : 2 ≤ M) (ψ₁ ψ₂ : SL(M + 2, ZMod 2) →* G)
    (h₁ : Function.Injective ψ₁) (h₂ : Function.Injective ψ₂)
    (hov : ∀ z : SL(M, ZMod 2), ψ₂ (blockSL (ZMod 2) (M + 2) M 0 (by omega) z) =
      ψ₁ (blockSL (ZMod 2) (M + 2) M 2 (by omega) z))
    (hcross : ∀ i j : Fin (M + 1), i.val ≤ 1 → M - 1 ≤ j.val → ∀ A B : SL(2, ZMod 2),
      ψ₁ (blockSL2 (ZMod 2) (M + 1) i A) * ψ₂ (blockSL2 (ZMod 2) (M + 1) j B) =
        ψ₂ (blockSL2 (ZMod 2) (M + 1) j B) * ψ₁ (blockSL2 (ZMod 2) (M + 1) i A)) :
    ∃ Ψ : SL(M + 4, ZMod 2) →* G, Function.Injective Ψ ∧ Ψ.range = ψ₁.range ⊔ ψ₂.range := by
  classical
  have hroot : ∀ (k : ℕ) (hk : 2 ≤ k) (hkM : k ≤ M) (A : SL(2, ZMod 2)),
      ψ₁ (blockSL2 (ZMod 2) (M + 1) ⟨k, by omega⟩ A) =
        ψ₂ (blockSL2 (ZMod 2) (M + 1) ⟨k - 2, by omega⟩ A) := by
    intro k hk hkM A
    have e1 : blockSL2 (ZMod 2) (M + 1) ⟨k, by omega⟩ A =
        blockSL (ZMod 2) (M + 2) M 2 (by omega) (blockSL (ZMod 2) M 2 (k - 2) (by omega) A) := by
      rw [blockSL_comp_apply]
      exact blockSL_index_congr _ (by simp only; omega) A
    have e2 : blockSL2 (ZMod 2) (M + 1) ⟨k - 2, by omega⟩ A =
        blockSL (ZMod 2) (M + 2) M 0 (by omega) (blockSL (ZMod 2) M 2 (k - 2) (by omega) A) := by
      rw [blockSL_comp_apply]
      exact blockSL_index_congr _ (by simp only; omega) A
    rw [e1, e2, hov]
  set U : Fin (M + 3) → Subgroup G := fun j =>
    if hj : j.val < 2 then (ψ₁.comp (blockSL2 (ZMod 2) (M + 1) ⟨j.val, by omega⟩)).range
    else (ψ₂.comp (blockSL2 (ZMod 2) (M + 1) ⟨j.val - 2, by omega⟩)).range with hUdef
  have hU1 : ∀ j : Fin (M + 3), (hj : j.val ≤ M) →
      U j = (ψ₁.comp (blockSL2 (ZMod 2) (M + 1) ⟨j.val, by omega⟩)).range := by
    intro j hj
    by_cases h2 : j.val < 2
    · simp only [hUdef, dif_pos h2]
    · simp only [hUdef, dif_neg h2]
      ext x
      simp only [MonoidHom.mem_range, MonoidHom.comp_apply]
      constructor
      · rintro ⟨A, rfl⟩
        exact ⟨A, hroot j.val (by omega) hj A⟩
      · rintro ⟨A, rfl⟩
        exact ⟨A, (hroot j.val (by omega) hj A).symm⟩
  have hU2 : ∀ j : Fin (M + 3), (hj : 2 ≤ j.val) →
      U j = (ψ₂.comp (blockSL2 (ZMod 2) (M + 1) ⟨j.val - 2, by omega⟩)).range := by
    intro j hj
    simp only [hUdef, dif_neg (show ¬ j.val < 2 by omega)]
  have hker₁ : ψ₁.ker ≤ Subgroup.center SL(M + 2, ZMod 2) := by
    rw [(MonoidHom.ker_eq_bot_iff ψ₁).mpr h₁]
    exact bot_le
  have hker₂ : ψ₂.ker ≤ Subgroup.center SL(M + 2, ZMod 2) := by
    rw [(MonoidHom.ker_eq_bot_iff ψ₂).mpr h₂]
    exact bot_le
  have hcommU : ∀ i j : Fin (M + 3), i.val + 2 ≤ j.val → ∀ a ∈ U i, ∀ c ∈ U j, a * c = c * a := by
    intro i j hij a ha c hc
    by_cases hi : 2 ≤ i.val
    · rw [hU2 i hi] at ha
      rw [hU2 j (by omega)] at hc
      obtain ⟨A, rfl⟩ := ha
      obtain ⟨B, rfl⟩ := hc
      simp only [MonoidHom.comp_apply]
      rw [← map_mul, ← map_mul, blockSL2_comm (K := ZMod 2) (M + 1) ⟨i.val - 2, by omega⟩
        ⟨j.val - 2, by omega⟩ (by simp only; omega)]
    · by_cases hj : j.val ≤ M
      · rw [hU1 i (by omega)] at ha
        rw [hU1 j hj] at hc
        obtain ⟨A, rfl⟩ := ha
        obtain ⟨B, rfl⟩ := hc
        simp only [MonoidHom.comp_apply]
        rw [← map_mul, ← map_mul, blockSL2_comm (K := ZMod 2) (M + 1) ⟨i.val, by omega⟩
          ⟨j.val, by omega⟩ (by simp only; omega)]
      · rw [hU1 i (by omega)] at ha
        rw [hU2 j (by omega)] at hc
        obtain ⟨A, rfl⟩ := ha
        obtain ⟨B, rfl⟩ := hc
        exact hcross ⟨i.val, by omega⟩ ⟨j.val - 2, by omega⟩ (by simp only; omega)
          (by simp only; omega) A B
  have hpairU : ∀ i j : Fin (M + 3), i.val + 1 = j.val →
      ∃ W : Subgroup G, LinearBlockStandardPair (ZMod 2) W (U i) (U j) := by
    intro i j hij
    by_cases hj : j.val ≤ M
    · set V : Fin (M + 2) → Subgroup G := fun k =>
        if hk : k.val < M + 1 then (ψ₁.comp (blockSL2 (ZMod 2) (M + 1) ⟨k.val, hk⟩)).range
        else ⊥ with hV
      have hVc : ∀ k : Fin (M + 1), V (Fin.castSucc k) =
          (ψ₁.comp (blockSL2 (ZMod 2) (M + 1) k)).range := by
        intro k
        simp only [hV, Fin.coe_castSucc, dif_pos k.isLt]
      obtain ⟨W, hW⟩ := exists_linearBlockStandardPair_of_blockSL2_frame ψ₁ hker₁ V hVc
        ⟨i.val, by omega⟩ ⟨j.val, by omega⟩ (by simp only; omega) (by simp only; omega)
      refine ⟨W, ?_⟩
      have e1 : V ⟨i.val, by omega⟩ = U i := by
        rw [hU1 i (by omega)]
        simp only [hV, dif_pos (show i.val < M + 1 by omega)]
      have e2 : V ⟨j.val, by omega⟩ = U j := by
        rw [hU1 j hj]
        simp only [hV, dif_pos (show j.val < M + 1 by omega)]
      rwa [e1, e2] at hW
    · set V : Fin (M + 2) → Subgroup G := fun k =>
        if hk : k.val < M + 1 then (ψ₂.comp (blockSL2 (ZMod 2) (M + 1) ⟨k.val, hk⟩)).range
        else ⊥ with hV
      have hVc : ∀ k : Fin (M + 1), V (Fin.castSucc k) =
          (ψ₂.comp (blockSL2 (ZMod 2) (M + 1) k)).range := by
        intro k
        simp only [hV, Fin.coe_castSucc, dif_pos k.isLt]
      obtain ⟨W, hW⟩ := exists_linearBlockStandardPair_of_blockSL2_frame ψ₂ hker₂ V hVc
        ⟨i.val - 2, by omega⟩ ⟨j.val - 2, by omega⟩ (by simp only; omega) (by simp only; omega)
      refine ⟨W, ?_⟩
      have e1 : V ⟨i.val - 2, by omega⟩ = U i := by
        rw [hU2 i (by omega)]
        simp only [hV, dif_pos (show i.val - 2 < M + 1 by omega)]
      have e2 : V ⟨j.val - 2, by omega⟩ = U j := by
        rw [hU2 j (by omega)]
        simp only [hV, dif_pos (show j.val - 2 < M + 1 by omega)]
      rwa [e1, e2] at hW
  have hsys : A2System adjA U (ψ₁.range ⊔ ψ₂.range) := by
    refine ⟨fun j => ?_, ?_, ?_, ?_⟩
    · by_cases hj : j.val < 2
      · rw [hU1 j (by omega)]
        exact ⟨MonoidHom.ofInjective (h₁.comp (blockSL2_injective (K := ZMod 2) _ _))⟩
      · rw [hU2 j (by omega)]
        exact ⟨MonoidHom.ofInjective (h₂.comp (blockSL2_injective (K := ZMod 2) _ _))⟩
    · refine le_antisymm (iSup_le fun j => ?_) (sup_le ?_ ?_)
      · by_cases hj : j.val < 2
        · rw [hU1 j (by omega), MonoidHom.range_comp]
          exact le_sup_of_le_left (Subgroup.map_le_range _ _)
        · rw [hU2 j (by omega), MonoidHom.range_comp]
          exact le_sup_of_le_right (Subgroup.map_le_range _ _)
      · rw [MonoidHom.range_eq_map, ← iSup_range_blockSL2 (K := ZMod 2) (M + 1),
          Subgroup.map_iSup]
        refine iSup_le fun k => ?_
        rw [← MonoidHom.range_comp, ← hU1 ⟨k.val, by omega⟩ (by simp only; omega)]
        exact le_iSup U _
      · rw [MonoidHom.range_eq_map, ← iSup_range_blockSL2 (K := ZMod 2) (M + 1),
          Subgroup.map_iSup]
        refine iSup_le fun k => ?_
        rw [← MonoidHom.range_comp]
        have e : (ψ₂.comp (blockSL2 (ZMod 2) (M + 1) k)).range = U ⟨k.val + 2, by omega⟩ := by
          rw [hU2 ⟨k.val + 2, by omega⟩ (by simp only; omega)]
          congr
        rw [e]
        exact le_iSup U _
    · intro i j hij hadj a ha c hc
      simp only [adjA, not_or] at hadj
      rcases lt_or_gt_of_ne (Fin.val_ne_of_ne hij) with h | h
      · exact hcommU i j (by omega) a ha c hc
      · exact (hcommU j i (by omega) c hc a ha).symm
    · intro i j hadj
      rcases hadj with h | h
      · exact hpairU i j h
      · obtain ⟨W, hW⟩ := hpairU j i h
        exact ⟨W, lbsp_symm hW⟩
  obtain ⟨Ψ, hΨ, hrange, -⟩ := A2System.exists_injective_marking (by omega) hsys
  exact ⟨Ψ, hΨ, hrange⟩

end CFSG.StandardType.FF81

end
