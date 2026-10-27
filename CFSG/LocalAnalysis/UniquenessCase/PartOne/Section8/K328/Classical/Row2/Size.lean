module

import CFSG.Adapters.StatedClassicalSmallOrders
import CFSG.Adapters.StatedClassicalUnitaryOrders
public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.K328.Matrix

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.K328

open CFSG.Open
open scoped Matrix commutatorElement

private theorem k328r2s_omega {F : Type} [Field F] [Fintype F] (hF : Fintype.card F = 4)
    {ω : F} (hω : ω ^ 2 + ω + 1 = 0) : ω ^ 2 ≠ ω := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : CharP F 2 := charP_of_card_eq_prime_pow (p := 2) (f := 2) (by rw [hF]; norm_num)
  intro h
  have h2 : ω + ω = 0 := CharTwo.add_self_eq_zero ω
  exact one_ne_zero (by linear_combination hω - h - h2 : (1 : F) = 0)

private theorem k328r2s_exists_blk {F : Type} [Field F] {X Y : Matrix (Fin 3) (Fin 3) F}
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

private theorem k328r2s_exists_iota (F : Type) [Field F] :
    ∃ ι : GL (Fin 3) F →* GL (Fin 3 ⊕ Fin 3) F, ∀ A : GL (Fin 3) F,
      (ι A : Matrix (Fin 3 ⊕ Fin 3) (Fin 3 ⊕ Fin 3) F) =
        Matrix.fromBlocks (A : Matrix (Fin 3) (Fin 3) F) 0 0
          ((A⁻¹ : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F)ᵀ := by
  have key : ∀ A : GL (Fin 3) F, ∃ B : GL (Fin 3 ⊕ Fin 3) F,
      (B : Matrix (Fin 3 ⊕ Fin 3) (Fin 3 ⊕ Fin 3) F) =
        Matrix.fromBlocks (A : Matrix (Fin 3) (Fin 3) F) 0 0
          ((A⁻¹ : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F)ᵀ := fun A =>
    k328r2s_exists_blk (by rw [← Matrix.transpose_mul]; simp)
  choose f hf using key
  refine ⟨MonoidHom.mk' f fun A B => ?_, hf⟩
  apply Units.ext
  rw [Units.val_mul, hf, hf, hf]
  simp [Matrix.fromBlocks_multiply, mul_inv_rev, Matrix.transpose_mul]

private theorem k328r2s_of_mem_sp {F : Type} [Field F] {A : GL (Fin 3 ⊕ Fin 3) F}
    {X Y : Matrix (Fin 3) (Fin 3) F}
    (hA : (A : Matrix (Fin 3 ⊕ Fin 3) (Fin 3 ⊕ Fin 3) F) = Matrix.fromBlocks X 0 0 Y)
    (h : A ∈ StatedSp 3 F) : Xᵀ * Y = 1 := by
  rw [StatedAPI.mem_statedSp_iff, hA] at h
  simp [Matrix.fromBlocks_transpose, Matrix.fromBlocks_multiply] at h
  exact h.1

private theorem k328r2s_vec3 {F : Type} (a : F) (i : Fin 3) : (![a, a, a] : Fin 3 → F) i = a := by
  fin_cases i <;> rfl

private theorem k328r2s_blocks {F : Type} [Field F] {ω : F} (hω2 : ω ^ 2 ≠ ω)
    {z g : GL (Fin 3 ⊕ Fin 3) F}
    (hz : (z : Matrix (Fin 3 ⊕ Fin 3) (Fin 3 ⊕ Fin 3) F) =
      Matrix.diagonal (Sum.elim ![ω, ω, ω] ![ω ^ 2, ω ^ 2, ω ^ 2]))
    (hc : z * g = g * z) :
    (g : Matrix (Fin 3 ⊕ Fin 3) (Fin 3 ⊕ Fin 3) F) = Matrix.fromBlocks
      (g : Matrix (Fin 3 ⊕ Fin 3) (Fin 3 ⊕ Fin 3) F).toBlocks₁₁ 0 0
      (g : Matrix (Fin 3 ⊕ Fin 3) (Fin 3 ⊕ Fin 3) F).toBlocks₂₂ := by
  have hc' : (z : Matrix (Fin 3 ⊕ Fin 3) (Fin 3 ⊕ Fin 3) F) * g = g * z := by
    rw [← Units.val_mul, hc, Units.val_mul]
  have hne : ω - ω ^ 2 ≠ 0 := sub_ne_zero.mpr hω2.symm
  have hne' : ω ^ 2 - ω ≠ 0 := sub_ne_zero.mpr hω2
  ext i j
  rcases i with i | i <;> rcases j with j | j
  · simp [Matrix.toBlocks₁₁]
  · have h1 := congrFun (congrFun hc' (Sum.inl i)) (Sum.inr j)
    rw [hz, Matrix.diagonal_mul, Matrix.mul_diagonal] at h1
    simp only [Sum.elim_inl, Sum.elim_inr, k328r2s_vec3] at h1
    have h2 : (ω - ω ^ 2) * (g : Matrix (Fin 3 ⊕ Fin 3) (Fin 3 ⊕ Fin 3) F)
        (Sum.inl i) (Sum.inr j) = 0 := by linear_combination h1
    simp [(mul_eq_zero.mp h2).resolve_left hne]
  · have h1 := congrFun (congrFun hc' (Sum.inr i)) (Sum.inl j)
    rw [hz, Matrix.diagonal_mul, Matrix.mul_diagonal] at h1
    simp only [Sum.elim_inl, Sum.elim_inr, k328r2s_vec3] at h1
    have h2 : (ω ^ 2 - ω) * (g : Matrix (Fin 3 ⊕ Fin 3) (Fin 3 ⊕ Fin 3) F)
        (Sum.inr i) (Sum.inl j) = 0 := by linear_combination h1
    simp [(mul_eq_zero.mp h2).resolve_left hne']
  · simp [Matrix.toBlocks₂₂]

private theorem k328r2s_shape {F : Type} [Field F] {ω : F} (hω2 : ω ^ 2 ≠ ω)
    {z g : GL (Fin 3 ⊕ Fin 3) F}
    (hz : (z : Matrix (Fin 3 ⊕ Fin 3) (Fin 3 ⊕ Fin 3) F) =
      Matrix.diagonal (Sum.elim ![ω, ω, ω] ![ω ^ 2, ω ^ 2, ω ^ 2]))
    (hg : g ∈ StatedSp 3 F) (hc : z * g = g * z) :
    ∃ A : GL (Fin 3) F, (g : Matrix (Fin 3 ⊕ Fin 3) (Fin 3 ⊕ Fin 3) F) =
      Matrix.fromBlocks (A : Matrix (Fin 3) (Fin 3) F) 0 0
        ((A⁻¹ : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F)ᵀ := by
  have hb := k328r2s_blocks hω2 hz hc
  have hinv := k328r2s_of_mem_sp hb hg
  have h2 : (g : Matrix (Fin 3 ⊕ Fin 3) (Fin 3 ⊕ Fin 3) F).toBlocks₂₂ᵀ *
      (g : Matrix (Fin 3 ⊕ Fin 3) (Fin 3 ⊕ Fin 3) F).toBlocks₁₁ = 1 := by
    simpa [Matrix.transpose_mul] using congrArg Matrix.transpose hinv
  refine ⟨⟨(g : Matrix (Fin 3 ⊕ Fin 3) (Fin 3 ⊕ Fin 3) F).toBlocks₁₁,
    (g : Matrix (Fin 3 ⊕ Fin 3) (Fin 3 ⊕ Fin 3) F).toBlocks₂₂ᵀ, mul_eq_one_comm.mp h2, h2⟩, ?_⟩
  show _ = Matrix.fromBlocks _ 0 0 (_ᵀᵀ)
  rw [Matrix.transpose_transpose]
  exact hb

private theorem k328r2s_iota_injective {F : Type} [Field F]
    {ι : GL (Fin 3) F →* GL (Fin 3 ⊕ Fin 3) F}
    (hι : ∀ A : GL (Fin 3) F, (ι A : Matrix (Fin 3 ⊕ Fin 3) (Fin 3 ⊕ Fin 3) F) =
      Matrix.fromBlocks (A : Matrix (Fin 3) (Fin 3) F) 0 0
        ((A⁻¹ : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F)ᵀ) : Function.Injective ι := by
  intro A B h
  apply Units.ext
  have := congrArg (fun g : GL (Fin 3 ⊕ Fin 3) F =>
    (g : Matrix (Fin 3 ⊕ Fin 3) (Fin 3 ⊕ Fin 3) F)) h
  simp only [hι, Matrix.fromBlocks_inj] at this
  exact this.1

private theorem k328r2s_commutator_mem {F : Type} [Field F] (A B : GL (Fin 3) F) :
    ⁅A, B⁆ ∈ StatedSL 3 F := by
  rw [StatedAPI.statedSL_eq_ker_det, MonoidHom.mem_ker, map_commutatorElement,
    commutatorElement_eq_one_iff_mul_comm]
  exact mul_comm _ _

private theorem k328r2s_exists {F : Type} [Field F] {ω : F} (hω2 : ω ^ 2 ≠ ω)
    {z g : GL (Fin 3 ⊕ Fin 3) F}
    (hz : (z : Matrix (Fin 3 ⊕ Fin 3) (Fin 3 ⊕ Fin 3) F) =
      Matrix.diagonal (Sum.elim ![ω, ω, ω] ![ω ^ 2, ω ^ 2, ω ^ 2]))
    {ι : GL (Fin 3) F →* GL (Fin 3 ⊕ Fin 3) F}
    (hι : ∀ A : GL (Fin 3) F, (ι A : Matrix (Fin 3 ⊕ Fin 3) (Fin 3 ⊕ Fin 3) F) =
      Matrix.fromBlocks (A : Matrix (Fin 3) (Fin 3) F) 0 0
        ((A⁻¹ : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F)ᵀ)
    (hg : g ∈ StatedSp 3 F ⊓ Subgroup.centralizer {z}) : ∃ A : GL (Fin 3) F, ι A = g := by
  obtain ⟨A, hA⟩ := k328r2s_shape hω2 hz hg.1
    (Subgroup.mem_centralizer_iff.mp hg.2 z (Set.mem_singleton z))
  exact ⟨A, Units.ext ((hι A).trans hA.symm)⟩

private theorem k328r2s_stdComp_le_map {F : Type} [Field F] {ω : F} (hω2 : ω ^ 2 ≠ ω)
    {z : GL (Fin 3 ⊕ Fin 3) F}
    (hz : (z : Matrix (Fin 3 ⊕ Fin 3) (Fin 3 ⊕ Fin 3) F) =
      Matrix.diagonal (Sum.elim ![ω, ω, ω] ![ω ^ 2, ω ^ 2, ω ^ 2]))
    {ι : GL (Fin 3) F →* GL (Fin 3 ⊕ Fin 3) F}
    (hι : ∀ A : GL (Fin 3) F, (ι A : Matrix (Fin 3 ⊕ Fin 3) (Fin 3 ⊕ Fin 3) F) =
      Matrix.fromBlocks (A : Matrix (Fin 3) (Fin 3) F) 0 0
        ((A⁻¹ : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F)ᵀ) :
    stdComp (StatedSp 3 F) z ≤ (StatedSL 3 F).map ι := by
  refine Subgroup.commutator_le.2 fun g₁ hg₁ g₂ hg₂ => ?_
  obtain ⟨A, rfl⟩ := k328r2s_exists hω2 hz hι hg₁
  obtain ⟨B, rfl⟩ := k328r2s_exists hω2 hz hι hg₂
  exact ⟨⁅A, B⁆, k328r2s_commutator_mem A B, map_commutatorElement ι A B⟩

private theorem k328r2s_card_le {F : Type} [Field F] [Fintype F] (hF : Fintype.card F = 4)
    {ω : F} (hω2 : ω ^ 2 ≠ ω) {z : GL (Fin 3 ⊕ Fin 3) F}
    (hz : (z : Matrix (Fin 3 ⊕ Fin 3) (Fin 3 ⊕ Fin 3) F) =
      Matrix.diagonal (Sum.elim ![ω, ω, ω] ![ω ^ 2, ω ^ 2, ω ^ 2])) :
    Nat.card ↥(stdComp (StatedSp 3 F) z) ≤ 60480 := by
  obtain ⟨ι, hι⟩ := k328r2s_exists_iota F
  calc Nat.card ↥(stdComp (StatedSp 3 F) z) ≤ Nat.card ↥((StatedSL 3 F).map ι) :=
        Subgroup.card_le_of_le (k328r2s_stdComp_le_map hω2 hz hι)
    _ = Nat.card ↥(StatedSL 3 F) := Subgroup.card_map_of_injective (k328r2s_iota_injective hι)
    _ = 60480 := by
        rw [StatedAPI.card_statedSL_three, Nat.card_eq_fintype_card, hF]
        norm_num

private theorem k328r2s_card_of_pos {G : Type} [Group G] [Finite G] {H : Subgroup G}
    {Z : Subgroup H} {X : Subgroup G} (hXH : X ≤ H) (hP : Pos ↥H Z (X.subgroupOf H)) :
    Nat.card X = 60480 ∨ Nat.card X = 16547328 := by
  obtain ⟨-, -, -, -, -, hcen, hlie⟩ := hP
  have hmul := Subgroup.card_eq_card_quotient_mul_card_subgroup
    (Subgroup.center ↥(X.subgroupOf H))
  rw [hcen, card_subgroupOf_of_le hXH] at hmul
  rcases hlie with h | h
  · rw [StatedAPI.card_of_statedClassicalModel_psl_three_four
      (h.statedClassicalModel (by decide))] at hmul
    omega
  · rw [StatedAPI.card_of_statedClassicalModel_psu_three_eight
      (h.statedClassicalModel (by decide))] at hmul
    omega

theorem row2_size (F : Type) [Field F] [Fintype F] [DecidableEq F]
    (hF : Fintype.card F = 4) (ω : F)
    (hω : ω ^ 2 + ω + 1 = 0) (z₀ t₀ : GL (Fin 3 ⊕ Fin 3) F)
    (hz : (z₀ : Matrix (Fin 3 ⊕ Fin 3) (Fin 3 ⊕ Fin 3) F) =
      Matrix.diagonal (Sum.elim ![ω, ω, ω] ![ω ^ 2, ω ^ 2, ω ^ 2]))
    (ht : (t₀ : Matrix (Fin 3 ⊕ Fin 3) (Fin 3 ⊕ Fin 3) F) =
      Matrix.diagonal (Sum.elim ![ω, ω ^ 2, 1] ![ω ^ 2, ω, 1])) :
    SizeLeaf (StatedSp 3 F) z₀ := by
  have _ := ht
  intro hz₀ X hX hP
  have h1 := k328r2s_card_of_pos (hX.trans (stdComp_le _ _)) hP
  have h2 := k328r2s_card_le hF (k328r2s_omega hF hω) hz
  have h3 : Nat.card X ≤ Nat.card (stdComp (StatedSp 3 F) z₀) := Subgroup.card_le_of_le hX
  omega

end CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.K328
