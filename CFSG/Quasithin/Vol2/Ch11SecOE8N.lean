module

public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.A312ListBasic
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.A312ListL3Block
public import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.L2_5_7FinMaxL3

public section

namespace CFSG.Quasithin.Vol2.Ch11.SecE3.Lie3

namespace L3T

open CFSG.Open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.LinearFlag
  CFSG.LocalAnalysis.ComponentInitial.LinearFieldFour CFSG.QuasithinUnique.Fin257
  CFSG.QuasithinUnique.Fin257.L3 CFSG.QuasithinUnique.Setup.X7a
  CFSG.QuasithinUnique.Vol2Native.A312L
open scoped MatrixGroups

variable {F : Type} [Field F] [CharP F 2]

omit [CharP F 2] in
theorem xMat_eq_embSL (a : F) :
    xMat a = embSL 1 ⟨!![1, a; 0, 1], by simp [Matrix.det_fin_two]⟩ := by
  apply Subtype.ext
  change xM a = embMat 1 !![1, a; 0, 1]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [xM, embMat]

omit [CharP F 2] in
theorem yMat_eq_embSL (b : F) :
    yMat b = embSL 0 ⟨!![1, b; 0, 1], by simp [Matrix.det_fin_two]⟩ := by
  apply Subtype.ext
  change yM b = embMat 0 !![1, b; 0, 1]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [yM, embMat]

omit [CharP F 2] in
theorem conj_mem_perfectCore {G : Type*} [Group G] {H : Subgroup G} {h x : G} (hh : h ∈ H)
    (hx : x ∈ perfectCore H) : h * x * h⁻¹ ∈ perfectCore H :=
  (Subgroup.mem_normalizer_iff.mp
    (normalizer_le_normalizer_perfectCore H (Subgroup.le_normalizer hh)) x).mp hx

omit [CharP F 2] in
theorem xMat_mul_wMat_mem (hK : ∃ s : Finset F, s.card = 4) (a c : F) :
    xMat a * wMat c ∈ perfectCore (Q3 F 1) := by
  have hx : ∀ a : F, xMat a ∈ perfectCore (Q3 F 1) := fun a => by
    rw [xMat_eq_embSL]
    exact embSL_mem_perfectCore hK 1 _
  have hy : yMat c ∈ Q3 F 1 := by
    refine mem_stabilizer_of_entries fun k l hk hl => ?_
    change yM c k l = 0
    fin_cases k <;> fin_cases l <;> simp [yM] at hk hl ⊢
  have hw : wMat c = xMat 1 * (yMat c * (xMat 1)⁻¹ * (yMat c)⁻¹) := by
    have h := xMat_mul_yMat (1 : F) c
    rw [one_mul] at h
    calc wMat c = wMat c * yMat c * xMat 1 * (xMat 1)⁻¹ * (yMat c)⁻¹ := by group
      _ = xMat 1 * yMat c * (xMat 1)⁻¹ * (yMat c)⁻¹ := by rw [← h]
      _ = _ := by group
  rw [hw]
  exact mul_mem (hx a) (mul_mem (hx 1) (conj_mem_perfectCore hy (inv_mem (hx 1))))

omit [CharP F 2] in
theorem yMat_mul_wMat_mem (hK : ∃ s : Finset F, s.card = 4) (b c : F) :
    yMat b * wMat c ∈ perfectCore (Q3 F 0) := by
  have hy : ∀ b : F, yMat b ∈ perfectCore (Q3 F 0) := fun b => by
    rw [yMat_eq_embSL]
    exact embSL_mem_perfectCore hK 0 _
  have hx : xMat c ∈ Q3 F 0 := by
    refine mem_stabilizer_of_entries fun k l hk hl => ?_
    change xM c k l = 0
    fin_cases k <;> fin_cases l <;> simp [xM] at hk hl ⊢
  have hw : wMat c = xMat c * yMat 1 * (xMat c)⁻¹ * (yMat 1)⁻¹ := by
    have h := xMat_mul_yMat c (1 : F)
    rw [mul_one] at h
    calc wMat c = wMat c * yMat 1 * xMat c * (xMat c)⁻¹ * (yMat 1)⁻¹ := by group
      _ = xMat c * yMat 1 * (xMat c)⁻¹ * (yMat 1)⁻¹ := by rw [← h]
  rw [hw]
  exact mul_mem (hy b) (mul_mem (conj_mem_perfectCore hx (hy 1)) (inv_mem (hy 1)))

omit [CharP F 2] in
theorem blk3_xMat_mul_wMat [Finite F] (a c : F) (h : xMat a * wMat c ∈ perfectCore (Q3 F 1)) :
    ((blk3 1 ⟨xMat a * wMat c, h⟩ : SL(2, F)) : Matrix (Fin 2) (Fin 2) F) = !![1, a; 0, 1] := by
  rw [blk3_coe, Matrix.SpecialLinearGroup.coe_mul]
  change blkAt _ 2 _ (xM a * wM c) = _
  ext i j
  fin_cases i <;> fin_cases j <;> simp [blkAt, xM, wM, Matrix.mul_apply, Fin.sum_univ_three]

omit [CharP F 2] in
theorem blk3_yMat_mul_wMat [Finite F] (b c : F) (h : yMat b * wMat c ∈ perfectCore (Q3 F 0)) :
    ((blk3 0 ⟨yMat b * wMat c, h⟩ : SL(2, F)) : Matrix (Fin 2) (Fin 2) F) = !![1, b; 0, 1] := by
  rw [blk3_coe, Matrix.SpecialLinearGroup.coe_mul]
  change blkAt _ 2 _ (yM b * wM c) = _
  ext i j
  fin_cases i <;> fin_cases j <;> simp [blkAt, yM, wM, Matrix.mul_apply, Fin.sum_univ_three]

theorem card_Wg : Nat.card (Wg : Subgroup (projectiveSL 3 F)) = Nat.card F := by
  have e : F ≃ (Wg : Subgroup (projectiveSL 3 F)) :=
    Equiv.ofBijective (fun c => ⟨wP c, c, rfl⟩)
      ⟨fun p q h => wP_injective (congrArg Subtype.val h), fun g => by
        obtain ⟨c, hg⟩ := mem_Wg.mp g.2
        exact ⟨c, Subtype.ext hg.symm⟩⟩
  exact (Nat.card_congr e).symm

theorem card_sq_le_center [Finite F] {B : Subgroup (projectiveSL 3 F)}
    (hB : B ≤ (Wg : Subgroup (projectiveSL 3 F))) {θ : MulAut (projectiveSL 3 F)}
    (hθ : θ ∈ semilinearAutGroup 3 F) (hθD : θ ∉ linearAutGroup 3 F)
    (hfix : ∀ g ∈ B, θ g = g) : Nat.card B ^ 2 ≤ Nat.card F := by
  obtain ⟨σ, m₁₁, m₁₂, m₂₁, m₂₂, hσ, hsub⟩ := fixes_type0 hθ hθD
  have hv₀ : ((0 : F), (1 : F)) ≠ 0 := by
    intro h
    exact one_ne_zero (congrArg Prod.snd h)
  have h1 : Nat.card B ≤ Nat.card {v : F × F | Semilin.InS σ m₁₁ m₁₂ m₂₁ m₂₂ v ∧
      ∃ t : F, v = (t * ((0 : F), (1 : F)).1, t * ((0 : F), (1 : F)).2)} := by
    refine card_le_of_pairs (hB.trans Wg_le_V1) _ fun a c h => ⟨hsub (hfix _ h), c, ?_⟩
    have haz : a = 0 := by
      by_contra ha
      obtain ⟨c', hc'⟩ := hB h
      exact xP_wP_ne a c c' ha hc'
    simp [haz]
  have h2 := h1.trans (Semilin.card_inS_line_le σ m₁₁ m₁₂ m₂₁ m₂₂ hv₀)
  calc Nat.card B ^ 2 ≤ Nat.card (Semilin.FixSet σ) ^ 2 := Nat.pow_le_pow_left h2 2
    _ ≤ Nat.card F := Semilin.card_fixSet_sq_le σ hσ

theorem exists_inner_V_of_le_semilinear [Finite F] {n : ℕ} (hn : 2 ≤ n)
    (hF : Nat.card F = 2 ^ n) (E : Subgroup (MulAut (projectiveSL 3 F)))
    (h2 : ∀ α ∈ E, α * α = 1) (hc : ∀ α ∈ E, ∀ β ∈ E, α * β = β * α)
    (hU : ∀ α ∈ E, ∀ u ∈ projUnitriangular 3 F, α u ∈ projUnitriangular 3 F)
    (hEs : E ≤ semilinearAutGroup 3 F) (hcard : Nat.card F < Nat.card E) :
    ∃ u : projectiveSL 3 F, MulAut.conj u ∈ E ∧ u ∉ (Wg : Subgroup (projectiveSL 3 F)) ∧
      (u ∈ (V1 : Subgroup (projectiveSL 3 F)) ∨ u ∈ (V2 : Subgroup (projectiveSL 3 F))) := by
  set c : projectiveSL 3 F →* MulAut (projectiveSL 3 F) := MulAut.conj with hcdef
  have hinj : Function.Injective c := conj_injective_of_center center_trivial_M
  set B := E.comap c with hB
  obtain ⟨hB2, hBU⟩ := comap_conj_le_U (modelData_L3 hn hF) E h2 hU
  have hBV : B ≤ V1 ∨ B ≤ V2 := elem_le_V1_or_V2 hBU hB2
  by_contra hno
  push Not at hno
  have hBW : B ≤ (Wg : Subgroup (projectiveSL 3 F)) := by
    intro u hu
    by_contra huW
    obtain ⟨h1, h1'⟩ := hno u hu huW
    rcases hBV with h | h
    · exact h1 (h hu)
    · exact h1' (h hu)
  set E₀ := E ⊓ c.range with hE₀
  have hEB : B.map c = E₀ := by rw [hB, Subgroup.map_comap_eq, inf_comm]
  have hcardB : Nat.card E₀ = Nat.card B := by
    rw [← hEB]
    exact Subgroup.card_map_of_injective hinj
  have hi : E₀.relIndex E ≤ 2 := by
    have := relIndex_inner_le E h2
    rwa [inf_eq_left.mpr hEs] at this
  have hc1 : Nat.card E = E₀.relIndex E * Nat.card E₀ := by
    have := Subgroup.relIndex_mul_card (H := E₀) (K := E)
    rw [inf_of_le_left inf_le_left] at this
    exact this.symm
  have hBq : Nat.card B ≤ Nat.card F := (Subgroup.card_le_of_le hBW).trans card_Wg.le
  by_cases hEI : E ≤ c.range
  · have hE0 : E₀ = E := inf_eq_left.mpr hEI
    have : Nat.card E = Nat.card B := by rw [← hcardB, hE0]
    omega
  · obtain ⟨θ₁, hθ₁E, hθ₁I⟩ : ∃ θ₁ ∈ E, θ₁ ∉ c.range := by
      by_contra h
      push Not at h
      exact hEI h
    have hθ₁D : θ₁ ∉ linearAutGroup 3 F := by
      intro hD'
      have : θ₁ ∈ E ⊓ linearAutGroup 3 F := ⟨hθ₁E, hD'⟩
      rw [inf_linear_eq_inf_inner E h2] at this
      exact hθ₁I this.2
    have hfix : ∀ g ∈ B, θ₁ g = g := fun g hg => fixes_of_comm hinj (hc θ₁ hθ₁E _ hg)
    have hsq := card_sq_le_center hBW (hEs hθ₁E) hθ₁D hfix
    have h4 : 4 ≤ Nat.card F := by
      rw [hF]
      calc 4 = 2 ^ 2 := by norm_num
        _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn
    have hEle : Nat.card E ≤ 2 * Nat.card B := by
      rw [hc1, hcardB]
      exact Nat.mul_le_mul_right _ hi
    nlinarith

end L3T

end CFSG.Quasithin.Vol2.Ch11.SecE3.Lie3
