module

import CFSG.RankThree.SubgroupLists.SymplecticTransvections
import CFSG.ClassicalGroups.SpecialLinear.Transitive
public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.K328.Matrix

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.K328

open CFSG.Open CFSG.RankThree.SubgroupLists
open scoped Matrix

private theorem k328r2g_exists_blk {F : Type} [Field F] {X Y : Matrix (Fin 3) (Fin 3) F}
    (h : Xᵀ * Y = 1) :
    ∃ A : GL (Fin 3 ⊕ Fin 3) F,
      (A : Matrix (Fin 3 ⊕ Fin 3) (Fin 3 ⊕ Fin 3) F) = Matrix.fromBlocks X 0 0 Y := by
  have hY : Y * Xᵀ = 1 := mul_eq_one_comm.mp h
  have hX : X * Yᵀ = 1 := by
    simpa [Matrix.transpose_mul] using congrArg Matrix.transpose hY
  have hYX : Yᵀ * X = 1 := mul_eq_one_comm.mp hX
  refine ⟨⟨Matrix.fromBlocks X 0 0 Y, Matrix.fromBlocks Yᵀ 0 0 Xᵀ, ?_, ?_⟩, rfl⟩
  · simp [Matrix.fromBlocks_multiply, hX, hY]
  · simp [Matrix.fromBlocks_multiply, hYX, h]

private theorem k328r2g_mem_sp {F : Type} [Field F] {A : GL (Fin 3 ⊕ Fin 3) F}
    {X Y : Matrix (Fin 3) (Fin 3) F}
    (hA : (A : Matrix (Fin 3 ⊕ Fin 3) (Fin 3 ⊕ Fin 3) F) = Matrix.fromBlocks X 0 0 Y)
    (h : Xᵀ * Y = 1) : A ∈ StatedSp 3 F := by
  rw [StatedAPI.mem_statedSp_iff, hA]
  have hYX : Yᵀ * X = 1 := by simpa [Matrix.transpose_mul] using congrArg Matrix.transpose h
  simp [Matrix.fromBlocks_transpose, Matrix.fromBlocks_multiply, h, hYX]

private theorem k328r2g_comm_z {F : Type} [Field F] {ω : F} {z A : GL (Fin 3 ⊕ Fin 3) F}
    (hz : (z : Matrix (Fin 3 ⊕ Fin 3) (Fin 3 ⊕ Fin 3) F) =
      Matrix.diagonal (Sum.elim ![ω, ω, ω] ![ω ^ 2, ω ^ 2, ω ^ 2]))
    {X Y : Matrix (Fin 3) (Fin 3) F}
    (hA : (A : Matrix (Fin 3 ⊕ Fin 3) (Fin 3 ⊕ Fin 3) F) = Matrix.fromBlocks X 0 0 Y) :
    A ∈ Subgroup.centralizer {z} := by
  rw [Subgroup.mem_centralizer_iff]
  intro g hg
  rw [Set.mem_singleton_iff] at hg
  subst hg
  have hz' : (g : Matrix (Fin 3 ⊕ Fin 3) (Fin 3 ⊕ Fin 3) F) =
      Matrix.fromBlocks (Matrix.scalar (Fin 3) ω) 0 0 (Matrix.scalar (Fin 3) (ω ^ 2)) := by
    rw [hz, ← Matrix.fromBlocks_diagonal]
    congr 2 <;> (funext i; fin_cases i <;> rfl)
  apply Units.ext
  rw [Units.val_mul, Units.val_mul, hz', hA, Matrix.fromBlocks_multiply, Matrix.fromBlocks_multiply]
  simp only [Matrix.zero_mul, Matrix.mul_zero, add_zero]
  rw [(Matrix.scalar_commute ω (fun r => Commute.all ω r) X).eq,
    (Matrix.scalar_commute (ω ^ 2) (fun r => Commute.all (ω ^ 2) r) Y).eq]

private theorem k328r2g_diag_mem {F : Type} [Field F] {D : GL (Fin 3 ⊕ Fin 3) F}
    {d e : Fin 3 → F}
    (hD : (D : Matrix (Fin 3 ⊕ Fin 3) (Fin 3 ⊕ Fin 3) F) = Matrix.diagonal (Sum.elim d e))
    (h : ∀ i, d i * e i = 1) : D ∈ StatedSp 3 F := by
  refine k328r2g_mem_sp (X := Matrix.diagonal d) (Y := Matrix.diagonal e) ?_ ?_
  · rw [hD, Matrix.fromBlocks_diagonal]
  · rw [Matrix.diagonal_transpose, Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
    congr 1
    funext i
    exact h i

private theorem k328r2g_fix {F : Type} [Field F] {s : GL (Fin 3 ⊕ Fin 3) F}
    (hs : s ∈ StatedSp 3 F) {a : Fin 3 ⊕ Fin 3 → F}
    (ha : (s : Matrix (Fin 3 ⊕ Fin 3) (Fin 3 ⊕ Fin 3) F) *ᵥ a = a) (c : F) :
    spTrans a c ∈ StatedSp 3 F ⊓ Subgroup.centralizer {s} := by
  refine Subgroup.mem_inf.mpr ⟨spTrans_mem_statedSp a c, ?_⟩
  rw [Subgroup.mem_centralizer_iff]
  intro h hh
  rw [Set.mem_singleton_iff] at hh
  subst hh
  have := conj_spTrans hs a c
  rw [ha] at this
  exact mul_inv_eq_iff_eq_mul.mp this

private theorem k328r2g_push {F : Type} [Field F] {L : Subgroup (GL (Fin 3 ⊕ Fin 3) F)}
    (hLH : L ≤ StatedSp 3 F) {g : GL (Fin 3 ⊕ Fin 3) F} (hg : g ∈ L)
    {a : Fin 3 ⊕ Fin 3 → F} (ha : ∀ c, spTrans a c ∈ L) :
    ∀ c, spTrans ((g : Matrix (Fin 3 ⊕ Fin 3) (Fin 3 ⊕ Fin 3) F) *ᵥ a) c ∈ L := fun c => by
  rw [← conj_spTrans (hLH hg) a c]
  exact L.mul_mem (L.mul_mem hg (ha c)) (L.inv_mem hg)

private theorem k328r2g_pull {F : Type} [Field F] {L : Subgroup (GL (Fin 3 ⊕ Fin 3) F)}
    (hLH : L ≤ StatedSp 3 F) {g : GL (Fin 3 ⊕ Fin 3) F} (hg : g ∈ L)
    {v b : Fin 3 ⊕ Fin 3 → F}
    (hv : (g : Matrix (Fin 3 ⊕ Fin 3) (Fin 3 ⊕ Fin 3) F) *ᵥ v = b)
    (hb : ∀ c, spTrans b c ∈ L) : ∀ c, spTrans v c ∈ L := by
  have h : ((g⁻¹ : GL (Fin 3 ⊕ Fin 3) F) : Matrix (Fin 3 ⊕ Fin 3) (Fin 3 ⊕ Fin 3) F) *ᵥ b = v := by
    rw [← hv, Matrix.mulVec_mulVec, Units.inv_mul, Matrix.one_mulVec]
  rw [← h]
  exact k328r2g_push hLH (L.inv_mem hg) hb

private theorem k328r2g_form {F : Type} [Field F] (x₁ x₂ y₁ y₂ : Fin 3 → F) :
    spForm 3 F (Sum.elim x₁ x₂) (Sum.elim y₁ y₂) = x₁ ⬝ᵥ y₂ - x₂ ⬝ᵥ y₁ := by
  rw [spForm_eq_dotProduct, spGram, Matrix.fromBlocks_mulVec]
  simp [sumElim_dotProduct_sumElim, sub_eq_add_neg, Matrix.neg_mulVec, dotProduct_neg]

private theorem k328r2g_W {F : Type} [Field F] {ω : F} {z₀ : GL (Fin 3 ⊕ Fin 3) F}
    (hz : (z₀ : Matrix (Fin 3 ⊕ Fin 3) (Fin 3 ⊕ Fin 3) F) =
      Matrix.diagonal (Sum.elim ![ω, ω, ω] ![ω ^ 2, ω ^ 2, ω ^ 2]))
    {L : Subgroup (GL (Fin 3 ⊕ Fin 3) F)} (hLH : L ≤ StatedSp 3 F)
    (hC : StatedSp 3 F ⊓ Subgroup.centralizer {z₀} ≤ L)
    (he : ∀ c, spTrans (Sum.elim (Pi.single 0 1) 0) c ∈ L) {w : Fin 3 → F} (hw : w ≠ 0) :
    ∀ c, spTrans (Sum.elim w 0) c ∈ L := by
  obtain ⟨A, -, hA⟩ := CFSG.ClassicalGroups.SpecialLinear.exists_statedSL_mulVec_eq (m := 3)
    (by norm_num) (x := Pi.single 0 1) (y := w) (Pi.single_ne_zero_iff.mpr one_ne_zero) hw
  have h1 : (A : Matrix (Fin 3) (Fin 3) F)ᵀ * ((A⁻¹ : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F)ᵀ =
      1 := by
    rw [← Matrix.transpose_mul, Units.inv_mul, Matrix.transpose_one]
  obtain ⟨D, hD⟩ := k328r2g_exists_blk h1
  have hDL : D ∈ L :=
    hC (Subgroup.mem_inf.mpr ⟨k328r2g_mem_sp hD h1, k328r2g_comm_z hz hD⟩)
  have hDv : (D : Matrix (Fin 3 ⊕ Fin 3) (Fin 3 ⊕ Fin 3) F) *ᵥ Sum.elim (Pi.single 0 1) 0 =
      Sum.elim w (0 : Fin 3 → F) := by
    rw [hD, Matrix.fromBlocks_mulVec, Sum.elim_comp_inl, Sum.elim_comp_inr]
    simp only [Matrix.zero_mulVec, Matrix.mulVec_zero, add_zero, hA]
  rw [← hDv]
  exact k328r2g_push hLH hDL he

private theorem k328r2g_Wd {F : Type} [Field F] {ω : F} {z₀ : GL (Fin 3 ⊕ Fin 3) F}
    (hz : (z₀ : Matrix (Fin 3 ⊕ Fin 3) (Fin 3 ⊕ Fin 3) F) =
      Matrix.diagonal (Sum.elim ![ω, ω, ω] ![ω ^ 2, ω ^ 2, ω ^ 2]))
    {L : Subgroup (GL (Fin 3 ⊕ Fin 3) F)} (hLH : L ≤ StatedSp 3 F)
    (hC : StatedSp 3 F ⊓ Subgroup.centralizer {z₀} ≤ L)
    (hf : ∀ c, spTrans (Sum.elim 0 (Pi.single 0 1)) c ∈ L) {w : Fin 3 → F} (hw : w ≠ 0) :
    ∀ c, spTrans (Sum.elim 0 w) c ∈ L := by
  obtain ⟨B, -, hB⟩ := CFSG.ClassicalGroups.SpecialLinear.exists_statedSL_mulVec_eq (m := 3)
    (by norm_num) (x := Pi.single 0 1) (y := w) (Pi.single_ne_zero_iff.mpr one_ne_zero) hw
  have h1 : ((B⁻¹ : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F)ᵀᵀ * (B : Matrix (Fin 3) (Fin 3) F) =
      1 := by
    rw [Matrix.transpose_transpose, Units.inv_mul]
  obtain ⟨D, hD⟩ := k328r2g_exists_blk h1
  have hDL : D ∈ L :=
    hC (Subgroup.mem_inf.mpr ⟨k328r2g_mem_sp hD h1, k328r2g_comm_z hz hD⟩)
  have hDv : (D : Matrix (Fin 3 ⊕ Fin 3) (Fin 3 ⊕ Fin 3) F) *ᵥ Sum.elim 0 (Pi.single 0 1) =
      Sum.elim (0 : Fin 3 → F) w := by
    rw [hD, Matrix.fromBlocks_mulVec, Sum.elim_comp_inl, Sum.elim_comp_inr]
    simp only [Matrix.zero_mulVec, Matrix.mulVec_zero, add_zero, zero_add, hB]
  rw [← hDv]
  exact k328r2g_push hLH hDL hf

private theorem k328r2g_mixed_a {F : Type} [Field F] {L : Subgroup (GL (Fin 3 ⊕ Fin 3) F)}
    (hLH : L ≤ StatedSp 3 F)
    (hW : ∀ w : Fin 3 → F, w ≠ 0 → ∀ c, spTrans (Sum.elim w (0 : Fin 3 → F)) c ∈ L)
    (hWd : ∀ w : Fin 3 → F, w ≠ 0 → ∀ c, spTrans (Sum.elim (0 : Fin 3 → F) w) c ∈ L)
    {w f : Fin 3 → F} (hβ : f ⬝ᵥ w ≠ 0) : ∀ c, spTrans (Sum.elim w f) c ∈ L := by
  have hw : w ≠ 0 := fun h => hβ (by rw [h, dotProduct_zero])
  have hf : f ≠ 0 := fun h => hβ (by rw [h, zero_dotProduct])
  refine k328r2g_pull hLH (hW w hw (f ⬝ᵥ w)⁻¹) ?_ (hWd f hf)
  have h1 : (f ⬝ᵥ w)⁻¹ * spForm 3 F (Sum.elim w f) (Sum.elim w (0 : Fin 3 → F)) = -1 := by
    rw [k328r2g_form, dotProduct_zero, zero_sub, mul_neg, inv_mul_cancel₀ hβ]
  rw [spTrans_mulVec, h1]
  funext x
  rcases x with i | i <;> simp

private theorem k328r2g_mixed {F : Type} [Field F] {L : Subgroup (GL (Fin 3 ⊕ Fin 3) F)}
    (hLH : L ≤ StatedSp 3 F)
    (hW : ∀ w : Fin 3 → F, w ≠ 0 → ∀ c, spTrans (Sum.elim w (0 : Fin 3 → F)) c ∈ L)
    (hWd : ∀ w : Fin 3 → F, w ≠ 0 → ∀ c, spTrans (Sum.elim (0 : Fin 3 → F) w) c ∈ L)
    {w f : Fin 3 → F} (hf : f ≠ 0) : ∀ c, spTrans (Sum.elim w f) c ∈ L := by
  by_cases hβ : f ⬝ᵥ w = 0
  · obtain ⟨i, hi⟩ : ∃ i, f i ≠ 0 := by
      by_contra h
      push Not at h
      exact hf (funext h)
    have hδ : f ⬝ᵥ (Pi.single i 1 : Fin 3 → F) = f i := by rw [dotProduct_single, mul_one]
    have hβ' : f ⬝ᵥ (w + Pi.single i 1) ≠ 0 := by
      rw [dotProduct_add, hβ, hδ, zero_add]
      exact hi
    refine k328r2g_pull hLH (hW (Pi.single i 1) (Pi.single_ne_zero_iff.mpr one_ne_zero)
      (-(f i)⁻¹)) ?_ (k328r2g_mixed_a hLH hW hWd hβ')
    have h1 : (-(f i)⁻¹) * spForm 3 F (Sum.elim w f)
        (Sum.elim (Pi.single i 1) (0 : Fin 3 → F)) = 1 := by
      rw [k328r2g_form, dotProduct_zero, zero_sub, hδ, neg_mul_neg, inv_mul_cancel₀ hi]
    rw [spTrans_mulVec, h1]
    funext x
    rcases x with j | j <;> simp [Pi.single_apply]
  · exact k328r2g_mixed_a hLH hW hWd hβ

private theorem k328r2g_all {F : Type} [Field F] {L : Subgroup (GL (Fin 3 ⊕ Fin 3) F)}
    (hLH : L ≤ StatedSp 3 F)
    (hW : ∀ w : Fin 3 → F, w ≠ 0 → ∀ c, spTrans (Sum.elim w (0 : Fin 3 → F)) c ∈ L)
    (hWd : ∀ w : Fin 3 → F, w ≠ 0 → ∀ c, spTrans (Sum.elim (0 : Fin 3 → F) w) c ∈ L)
    (a : Fin 3 ⊕ Fin 3 → F) : ∀ c, spTrans a c ∈ L := by
  obtain ⟨w, f, rfl⟩ : ∃ w f : Fin 3 → F, a = Sum.elim w f :=
    ⟨fun i => a (Sum.inl i), fun i => a (Sum.inr i), by funext x; rcases x with i | i <;> rfl⟩
  by_cases hf : f = 0
  · by_cases hw : w = 0
    · intro c
      have h0 : (Sum.elim w f : Fin 3 ⊕ Fin 3 → F) = 0 := by
        funext x; rcases x with i | i <;> simp [hw, hf]
      rw [h0, spTrans_zero_vec]
      exact L.one_mem
    · rw [hf]
      exact hW w hw
  · exact k328r2g_mixed hLH hW hWd hf

private theorem k328r2g_fixed {F : Type} [Field F] {ω : F} (h3 : ω ^ 3 = 1)
    {z₀ t₀ : GL (Fin 3 ⊕ Fin 3) F}
    (hz : (z₀ : Matrix (Fin 3 ⊕ Fin 3) (Fin 3 ⊕ Fin 3) F) =
      Matrix.diagonal (Sum.elim ![ω, ω, ω] ![ω ^ 2, ω ^ 2, ω ^ 2]))
    (ht : (t₀ : Matrix (Fin 3 ⊕ Fin 3) (Fin 3 ⊕ Fin 3) F) =
      Matrix.diagonal (Sum.elim ![ω, ω ^ 2, 1] ![ω ^ 2, ω, 1])) :
    ((z₀ * t₀ ^ 2 : GL (Fin 3 ⊕ Fin 3) F) : Matrix (Fin 3 ⊕ Fin 3) (Fin 3 ⊕ Fin 3) F) *ᵥ
        Sum.elim (Pi.single 0 1) (0 : Fin 3 → F) = Sum.elim (Pi.single 0 1) (0 : Fin 3 → F) ∧
    ((z₀ * t₀ ^ 2 : GL (Fin 3 ⊕ Fin 3) F) : Matrix (Fin 3 ⊕ Fin 3) (Fin 3 ⊕ Fin 3) F) *ᵥ
        Sum.elim (0 : Fin 3 → F) (Pi.single 0 1) = Sum.elim (0 : Fin 3 → F) (Pi.single 0 1) := by
  have hs : ((z₀ * t₀ ^ 2 : GL (Fin 3 ⊕ Fin 3) F) : Matrix (Fin 3 ⊕ Fin 3) (Fin 3 ⊕ Fin 3) F) =
      Matrix.diagonal (fun x => Sum.elim ![ω, ω, ω] ![ω ^ 2, ω ^ 2, ω ^ 2] x *
        Sum.elim ![ω, ω ^ 2, 1] ![ω ^ 2, ω, 1] x ^ 2) := by
    rw [Units.val_mul, Units.val_pow_eq_pow_val, hz, ht, Matrix.diagonal_pow,
      Matrix.diagonal_mul_diagonal]
    rfl
  refine ⟨?_, ?_⟩
  · funext x
    rw [hs, Matrix.mulVec_diagonal]
    rcases x with i | i
    · fin_cases i
      · simp
        linear_combination h3
      · simp
      · simp
    · simp
  · funext x
    rw [hs, Matrix.mulVec_diagonal]
    rcases x with i | i
    · simp
    · fin_cases i
      · simp
        linear_combination (ω ^ 3 + 1) * h3
      · simp
      · simp

theorem row2_gen (F : Type) [Field F] [Fintype F] [DecidableEq F]
    (hF : Fintype.card F = 4) (ω : F)
    (hω : ω ^ 2 + ω + 1 = 0) (z₀ t₀ : GL (Fin 3 ⊕ Fin 3) F)
    (hz : (z₀ : Matrix (Fin 3 ⊕ Fin 3) (Fin 3 ⊕ Fin 3) F) =
      Matrix.diagonal (Sum.elim ![ω, ω, ω] ![ω ^ 2, ω ^ 2, ω ^ 2]))
    (ht : (t₀ : Matrix (Fin 3 ⊕ Fin 3) (Fin 3 ⊕ Fin 3) F) =
      Matrix.diagonal (Sum.elim ![ω, ω ^ 2, 1] ![ω ^ 2, ω, 1])) :
    GenLeaf (StatedSp 3 F) z₀ t₀ := by
  have _ := hF
  have h3 : ω ^ 3 = 1 := by linear_combination (ω - 1) * hω
  have hzH : z₀ ∈ StatedSp 3 F :=
    k328r2g_diag_mem hz fun i => by fin_cases i <;> simp <;> linear_combination h3
  have htH : t₀ ∈ StatedSp 3 F :=
    k328r2g_diag_mem ht fun i => by fin_cases i <;> simp <;> linear_combination h3
  have hs1 : z₀ * t₀ ^ 2 ∈ StatedSp 3 F :=
    (StatedSp 3 F).mul_mem hzH ((StatedSp 3 F).pow_mem htH 2)
  obtain ⟨L, hL⟩ : ∃ L : Subgroup (GL (Fin 3 ⊕ Fin 3) F), L =
      StatedSp 3 F ⊓ Subgroup.centralizer {z₀} ⊔ StatedSp 3 F ⊓ Subgroup.centralizer {t₀} ⊔
        StatedSp 3 F ⊓ Subgroup.centralizer {z₀ * t₀} ⊔
          StatedSp 3 F ⊓ Subgroup.centralizer {z₀ * t₀ ^ 2} := ⟨_, rfl⟩
  have hLH : L ≤ StatedSp 3 F := by
    rw [hL]
    exact sup_le (sup_le (sup_le inf_le_left inf_le_left) inf_le_left) inf_le_left
  have hC : StatedSp 3 F ⊓ Subgroup.centralizer {z₀} ≤ L := by
    rw [hL]
    exact le_sup_left.trans (le_sup_left.trans le_sup_left)
  have hC1 : StatedSp 3 F ⊓ Subgroup.centralizer {z₀ * t₀ ^ 2} ≤ L := by
    rw [hL]
    exact le_sup_right
  obtain ⟨hfx1, hfx2⟩ := k328r2g_fixed h3 hz ht
  have hW := fun w (hw : w ≠ 0) =>
    k328r2g_W hz hLH hC (fun c => hC1 (k328r2g_fix hs1 hfx1 c)) hw
  have hWd := fun w (hw : w ≠ 0) =>
    k328r2g_Wd hz hLH hC (fun c => hC1 (k328r2g_fix hs1 hfx2 c)) hw
  refine le_antisymm (hL ▸ hLH) ?_
  intro g hg
  rw [statedSp_eq_closure_spTrans] at hg
  rw [← hL]
  exact (Subgroup.closure_le L).mpr (by rintro _ ⟨a, c, rfl⟩; exact k328r2g_all hLH hW hWd a c) hg

end CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.K328
