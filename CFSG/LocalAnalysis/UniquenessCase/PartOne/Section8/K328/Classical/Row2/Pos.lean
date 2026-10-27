module

import CFSG.Adapters.StatedQuasisimple
import CFSG.Open.StatedCenterThree
public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.K328.Matrix

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.K328

open CFSG.Open
open scoped Matrix commutatorElement

private theorem k328r2p_scalars {F : Type} [Field F] [Fintype F] (hF : Fintype.card F = 4)
    {ω : F} (hω : ω ^ 2 + ω + 1 = 0) : ω ^ 3 = 1 ∧ ω ≠ 1 ∧ ω ^ 2 ≠ ω := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : CharP F 2 := charP_of_card_eq_prime_pow (p := 2) (f := 2) (by rw [hF]; norm_num)
  refine ⟨by linear_combination (ω - 1) * hω, fun h => ?_, fun h => ?_⟩
  · have h2 : (1 : F) + 1 = 0 := CharTwo.add_self_eq_zero 1
    rw [h] at hω
    exact one_ne_zero (by linear_combination hω - h2 : (1 : F) = 0)
  · have h2 : ω + ω = 0 := CharTwo.add_self_eq_zero ω
    exact one_ne_zero (by linear_combination hω - h - h2 : (1 : F) = 0)

private theorem k328r2p_exists_blk {F : Type} [Field F] {X Y : Matrix (Fin 3) (Fin 3) F}
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

private theorem k328r2p_exists_iota (F : Type) [Field F] :
    ∃ ι : GL (Fin 3) F →* GL (Fin 3 ⊕ Fin 3) F, ∀ A : GL (Fin 3) F,
      (ι A : Matrix (Fin 3 ⊕ Fin 3) (Fin 3 ⊕ Fin 3) F) =
        Matrix.fromBlocks (A : Matrix (Fin 3) (Fin 3) F) 0 0
          ((A⁻¹ : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F)ᵀ := by
  have key : ∀ A : GL (Fin 3) F, ∃ B : GL (Fin 3 ⊕ Fin 3) F,
      (B : Matrix (Fin 3 ⊕ Fin 3) (Fin 3 ⊕ Fin 3) F) =
        Matrix.fromBlocks (A : Matrix (Fin 3) (Fin 3) F) 0 0
          ((A⁻¹ : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F)ᵀ := fun A =>
    k328r2p_exists_blk (by rw [← Matrix.transpose_mul]; simp)
  choose f hf using key
  refine ⟨MonoidHom.mk' f fun A B => ?_, hf⟩
  apply Units.ext
  rw [Units.val_mul, hf, hf, hf]
  simp [Matrix.fromBlocks_multiply, mul_inv_rev, Matrix.transpose_mul]

private theorem k328r2p_mem_sp {F : Type} [Field F] {A : GL (Fin 3 ⊕ Fin 3) F}
    {X Y : Matrix (Fin 3) (Fin 3) F}
    (hA : (A : Matrix (Fin 3 ⊕ Fin 3) (Fin 3 ⊕ Fin 3) F) = Matrix.fromBlocks X 0 0 Y)
    (h : Xᵀ * Y = 1) : A ∈ StatedSp 3 F := by
  rw [StatedAPI.mem_statedSp_iff, hA]
  have hYX : Yᵀ * X = 1 := by simpa [Matrix.transpose_mul] using congrArg Matrix.transpose h
  simp [Matrix.fromBlocks_transpose, Matrix.fromBlocks_multiply, h, hYX]

private theorem k328r2p_of_mem_sp {F : Type} [Field F] {A : GL (Fin 3 ⊕ Fin 3) F}
    {X Y : Matrix (Fin 3) (Fin 3) F}
    (hA : (A : Matrix (Fin 3 ⊕ Fin 3) (Fin 3 ⊕ Fin 3) F) = Matrix.fromBlocks X 0 0 Y)
    (h : A ∈ StatedSp 3 F) : Xᵀ * Y = 1 := by
  rw [StatedAPI.mem_statedSp_iff, hA] at h
  simp [Matrix.fromBlocks_transpose, Matrix.fromBlocks_multiply] at h
  exact h.1

private theorem k328r2p_comm_z {F : Type} [Field F] {ω : F} {z A : GL (Fin 3 ⊕ Fin 3) F}
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

private theorem k328r2p_vec3 {F : Type} (a : F) (i : Fin 3) : (![a, a, a] : Fin 3 → F) i = a := by
  fin_cases i <;> rfl

private theorem k328r2p_blocks {F : Type} [Field F] {ω : F} (hω2 : ω ^ 2 ≠ ω)
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
    simp only [Sum.elim_inl, Sum.elim_inr, k328r2p_vec3] at h1
    have h2 : (ω - ω ^ 2) * (g : Matrix (Fin 3 ⊕ Fin 3) (Fin 3 ⊕ Fin 3) F)
        (Sum.inl i) (Sum.inr j) = 0 := by linear_combination h1
    simp [(mul_eq_zero.mp h2).resolve_left hne]
  · have h1 := congrFun (congrFun hc' (Sum.inr i)) (Sum.inl j)
    rw [hz, Matrix.diagonal_mul, Matrix.mul_diagonal] at h1
    simp only [Sum.elim_inl, Sum.elim_inr, k328r2p_vec3] at h1
    have h2 : (ω ^ 2 - ω) * (g : Matrix (Fin 3 ⊕ Fin 3) (Fin 3 ⊕ Fin 3) F)
        (Sum.inr i) (Sum.inl j) = 0 := by linear_combination h1
    simp [(mul_eq_zero.mp h2).resolve_left hne']
  · simp [Matrix.toBlocks₂₂]

private theorem k328r2p_shape {F : Type} [Field F] {ω : F} (hω2 : ω ^ 2 ≠ ω)
    {z g : GL (Fin 3 ⊕ Fin 3) F}
    (hz : (z : Matrix (Fin 3 ⊕ Fin 3) (Fin 3 ⊕ Fin 3) F) =
      Matrix.diagonal (Sum.elim ![ω, ω, ω] ![ω ^ 2, ω ^ 2, ω ^ 2]))
    (hg : g ∈ StatedSp 3 F) (hc : z * g = g * z) :
    ∃ A : GL (Fin 3) F, (g : Matrix (Fin 3 ⊕ Fin 3) (Fin 3 ⊕ Fin 3) F) =
      Matrix.fromBlocks (A : Matrix (Fin 3) (Fin 3) F) 0 0
        ((A⁻¹ : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F)ᵀ := by
  have hb := k328r2p_blocks hω2 hz hc
  have hinv := k328r2p_of_mem_sp hb hg
  have h2 : (g : Matrix (Fin 3 ⊕ Fin 3) (Fin 3 ⊕ Fin 3) F).toBlocks₂₂ᵀ *
      (g : Matrix (Fin 3 ⊕ Fin 3) (Fin 3 ⊕ Fin 3) F).toBlocks₁₁ = 1 := by
    simpa [Matrix.transpose_mul] using congrArg Matrix.transpose hinv
  refine ⟨⟨(g : Matrix (Fin 3 ⊕ Fin 3) (Fin 3 ⊕ Fin 3) F).toBlocks₁₁,
    (g : Matrix (Fin 3 ⊕ Fin 3) (Fin 3 ⊕ Fin 3) F).toBlocks₂₂ᵀ, mul_eq_one_comm.mp h2, h2⟩, ?_⟩
  show _ = Matrix.fromBlocks _ 0 0 (_ᵀᵀ)
  rw [Matrix.transpose_transpose]
  exact hb

private theorem k328r2p_iota_mem {F : Type} [Field F] {ω : F} {z : GL (Fin 3 ⊕ Fin 3) F}
    (hz : (z : Matrix (Fin 3 ⊕ Fin 3) (Fin 3 ⊕ Fin 3) F) =
      Matrix.diagonal (Sum.elim ![ω, ω, ω] ![ω ^ 2, ω ^ 2, ω ^ 2]))
    {ι : GL (Fin 3) F →* GL (Fin 3 ⊕ Fin 3) F}
    (hι : ∀ A : GL (Fin 3) F, (ι A : Matrix (Fin 3 ⊕ Fin 3) (Fin 3 ⊕ Fin 3) F) =
      Matrix.fromBlocks (A : Matrix (Fin 3) (Fin 3) F) 0 0
        ((A⁻¹ : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F)ᵀ) (A : GL (Fin 3) F) :
    ι A ∈ StatedSp 3 F ⊓ Subgroup.centralizer {z} :=
  ⟨k328r2p_mem_sp (hι A) (by rw [← Matrix.transpose_mul]; simp), k328r2p_comm_z hz (hι A)⟩

private theorem k328r2p_iota_injective {F : Type} [Field F]
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

private theorem k328r2p_commutator_mem {F : Type} [Field F] (A B : GL (Fin 3) F) :
    ⁅A, B⁆ ∈ StatedSL 3 F := by
  rw [StatedAPI.statedSL_eq_ker_det, MonoidHom.mem_ker, map_commutatorElement,
    commutatorElement_eq_one_iff_mul_comm]
  exact mul_comm _ _

private theorem k328r2p_exists {F : Type} [Field F] {ω : F} (hω2 : ω ^ 2 ≠ ω)
    {z g : GL (Fin 3 ⊕ Fin 3) F}
    (hz : (z : Matrix (Fin 3 ⊕ Fin 3) (Fin 3 ⊕ Fin 3) F) =
      Matrix.diagonal (Sum.elim ![ω, ω, ω] ![ω ^ 2, ω ^ 2, ω ^ 2]))
    {ι : GL (Fin 3) F →* GL (Fin 3 ⊕ Fin 3) F}
    (hι : ∀ A : GL (Fin 3) F, (ι A : Matrix (Fin 3 ⊕ Fin 3) (Fin 3 ⊕ Fin 3) F) =
      Matrix.fromBlocks (A : Matrix (Fin 3) (Fin 3) F) 0 0
        ((A⁻¹ : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F)ᵀ)
    (hg : g ∈ StatedSp 3 F ⊓ Subgroup.centralizer {z}) : ∃ A : GL (Fin 3) F, ι A = g := by
  obtain ⟨A, hA⟩ := k328r2p_shape hω2 hz hg.1
    (Subgroup.mem_centralizer_iff.mp hg.2 z (Set.mem_singleton z))
  exact ⟨A, Units.ext ((hι A).trans hA.symm)⟩

private theorem k328r2p_stdComp_eq {F : Type} [Field F] {ω : F} (hω2 : ω ^ 2 ≠ ω)
    {z : GL (Fin 3 ⊕ Fin 3) F}
    (hz : (z : Matrix (Fin 3 ⊕ Fin 3) (Fin 3 ⊕ Fin 3) F) =
      Matrix.diagonal (Sum.elim ![ω, ω, ω] ![ω ^ 2, ω ^ 2, ω ^ 2]))
    {ι : GL (Fin 3) F →* GL (Fin 3 ⊕ Fin 3) F}
    (hι : ∀ A : GL (Fin 3) F, (ι A : Matrix (Fin 3 ⊕ Fin 3) (Fin 3 ⊕ Fin 3) F) =
      Matrix.fromBlocks (A : Matrix (Fin 3) (Fin 3) F) 0 0
        ((A⁻¹ : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F)ᵀ)
    (hperf : ⁅StatedSL 3 F, StatedSL 3 F⁆ = StatedSL 3 F) :
    stdComp (StatedSp 3 F) z = (StatedSL 3 F).map ι := by
  have hle : (StatedSL 3 F).map ι ≤ StatedSp 3 F ⊓ Subgroup.centralizer {z} := by
    rintro _ ⟨A, -, rfl⟩
    exact k328r2p_iota_mem hz hι A
  apply le_antisymm
  · refine Subgroup.commutator_le.2 fun g₁ hg₁ g₂ hg₂ => ?_
    obtain ⟨A, rfl⟩ := k328r2p_exists hω2 hz hι hg₁
    obtain ⟨B, rfl⟩ := k328r2p_exists hω2 hz hι hg₂
    exact ⟨⁅A, B⁆, k328r2p_commutator_mem A B, map_commutatorElement ι A B⟩
  · calc (StatedSL 3 F).map ι = (⁅StatedSL 3 F, StatedSL 3 F⁆).map ι := by rw [hperf]
      _ = ⁅(StatedSL 3 F).map ι, (StatedSL 3 F).map ι⁆ := Subgroup.map_commutator _ _ _
      _ ≤ stdComp (StatedSp 3 F) z := Subgroup.commutator_mono hle hle

private theorem k328r2p_commutator_le {G : Type} [Group G] (C : Subgroup G) : ⁅C, C⁆ ≤ C := by
  refine Subgroup.commutator_le.2 fun a ha b hb => ?_
  rw [commutatorElement_def]
  exact Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.mul_mem _ ha hb)
    (Subgroup.inv_mem _ ha)) (Subgroup.inv_mem _ hb)

private theorem k328r2p_conj_mem {G : Type} [Group G] (C : Subgroup G) {c x : G} (hc : c ∈ C)
    (hx : x ∈ ⁅C, C⁆) : c * x * c⁻¹ ∈ ⁅C, C⁆ := by
  have hxC : x ∈ C := k328r2p_commutator_le C hx
  have h : c * x * c⁻¹ = x * ⁅x⁻¹, c⁆ := by
    rw [commutatorElement_def]
    group
  rw [h]
  exact Subgroup.mul_mem _ hx (Subgroup.commutator_mem_commutator (Subgroup.inv_mem _ hxC) hc)

private theorem k328r2p_stdComp_le_C {G : Type} [Group G] (H : Subgroup G) (z₀ : G) :
    stdComp H z₀ ≤ H ⊓ Subgroup.centralizer {z₀} :=
  k328r2p_commutator_le (H ⊓ Subgroup.centralizer {z₀})

private theorem k328r2p_le_centralizer {G : Type} [Group G] (H : Subgroup G) {z₀ : G}
    (hz₀ : z₀ ∈ H) :
    (stdComp H z₀).subgroupOf H ≤
      Subgroup.centralizer ((Subgroup.zpowers (⟨z₀, hz₀⟩ : H) : Subgroup H) : Set H) := by
  intro x hx
  rw [Subgroup.mem_subgroupOf] at hx
  rw [Subgroup.mem_centralizer_iff]
  intro y hy
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hy
  have hcomm : Commute (⟨z₀, hz₀⟩ : H) x := by
    apply Subtype.ext
    exact Subgroup.mem_centralizer_iff.mp (k328r2p_stdComp_le_C H z₀ hx).2 z₀
      (Set.mem_singleton z₀)
  exact (hcomm.zpow_left k).eq

private theorem k328r2p_normal {G : Type} [Group G] (H : Subgroup G) {z₀ : G} (hz₀ : z₀ ∈ H) :
    (((stdComp H z₀).subgroupOf H).subgroupOf
      (Subgroup.centralizer ((Subgroup.zpowers (⟨z₀, hz₀⟩ : H) : Subgroup H) : Set H))).Normal := by
  refine ⟨fun n hn g => ?_⟩
  rw [Subgroup.mem_subgroupOf, Subgroup.mem_subgroupOf] at hn ⊢
  unfold stdComp at hn ⊢
  have hgC : ((g : H) : G) ∈ H ⊓ Subgroup.centralizer {z₀} := by
    refine Subgroup.mem_inf.mpr ⟨(g : H).2, ?_⟩
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    rw [Set.mem_singleton_iff] at hy
    subst hy
    have := Subgroup.mem_centralizer_iff.mp g.2 ⟨y, hz₀⟩ (Subgroup.mem_zpowers _)
    exact congrArg Subtype.val this
  have := k328r2p_conj_mem (H ⊓ Subgroup.centralizer {z₀}) hgC hn
  simpa using this

private theorem k328r2p_order {F : Type} [Field F] {ω : F} (h3 : ω ^ 3 = 1) (hω1 : ω ≠ 1)
    {z : GL (Fin 3 ⊕ Fin 3) F}
    (hz : (z : Matrix (Fin 3 ⊕ Fin 3) (Fin 3 ⊕ Fin 3) F) =
      Matrix.diagonal (Sum.elim ![ω, ω, ω] ![ω ^ 2, ω ^ 2, ω ^ 2])) : orderOf z = 3 := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have h6 : (ω ^ 2) ^ 3 = 1 := by rw [← pow_mul, mul_comm, pow_mul, h3, one_pow]
  apply orderOf_eq_prime
  · apply Units.ext
    rw [Units.val_pow_eq_pow_val, hz, Matrix.diagonal_pow, Units.val_one, ← Matrix.diagonal_one]
    congr 1
    funext i
    rcases i with i | i <;> fin_cases i <;> simp [h3, h6]
  · intro h
    apply hω1
    have := congrArg (fun g : GL (Fin 3 ⊕ Fin 3) F =>
      (g : Matrix (Fin 3 ⊕ Fin 3) (Fin 3 ⊕ Fin 3) F) (Sum.inl 0) (Sum.inl 0)) h
    simpa [hz] using this

theorem row2_pos (F : Type) [Field F] [Fintype F] [DecidableEq F]
    (hF : Fintype.card F = 4) (ω : F)
    (hω : ω ^ 2 + ω + 1 = 0) (z₀ t₀ : GL (Fin 3 ⊕ Fin 3) F)
    (hz : (z₀ : Matrix (Fin 3 ⊕ Fin 3) (Fin 3 ⊕ Fin 3) F) =
      Matrix.diagonal (Sum.elim ![ω, ω, ω] ![ω ^ 2, ω ^ 2, ω ^ 2]))
    (ht : (t₀ : Matrix (Fin 3 ⊕ Fin 3) (Fin 3 ⊕ Fin 3) F) =
      Matrix.diagonal (Sum.elim ![ω, ω ^ 2, 1] ![ω ^ 2, ω, 1])) :
    PosLeaf (StatedSp 3 F) z₀ := by
  have _ := ht
  intro hz₀
  obtain ⟨h3, hω1, hω2⟩ := k328r2p_scalars hF hω
  obtain ⟨ι, hι⟩ := k328r2p_exists_iota F
  have hSLq : CFSG.IsQuasisimple ↥(StatedSL 3 F) :=
    StatedAPI.isQuasisimple_statedSL_of_two_le (m := 2) le_rfl F
  have hperf : ⁅StatedSL 3 F, StatedSL 3 F⁆ = StatedSL 3 F :=
    commutator_self_of_perfect hSLq.1.1
  have hS := k328r2p_stdComp_eq hω2 hz hι hperf
  let eY := (StatedSL 3 F).equivMapOfInjective ι (k328r2p_iota_injective hι)
  let eX : ↥((stdComp (StatedSp 3 F) z₀).subgroupOf (StatedSp 3 F)) ≃* ↥(StatedSL 3 F) :=
    ((Subgroup.subgroupOfEquivOfLe (stdComp_le (StatedSp 3 F) z₀)).trans
      (MulEquiv.subgroupCongr hS)).trans eY.symm
  refine ⟨?_, ?_, k328r2p_le_centralizer _ hz₀, (k328r2p_normal _ hz₀).isSubnormal,
    isQuasisimple_of_mulEquiv' eX.symm ⟨hSLq.1.1, hSLq.2.1⟩, ?_, ?_⟩
  · rw [Nat.card_zpowers, ← Subgroup.orderOf_coe]
    exact k328r2p_order h3 hω1 hz
  · rw [Subgroup.zpowers_le, Subgroup.mem_subgroupOf]
    show z₀ ∈ stdComp (StatedSp 3 F) z₀
    rw [hS]
    have hC : z₀ ∈ StatedSp 3 F ⊓ Subgroup.centralizer {z₀} :=
      Subgroup.mem_inf.mpr ⟨hz₀, Subgroup.mem_centralizer_iff.mpr fun h hh => by
        rw [Set.mem_singleton_iff] at hh
        rw [hh]⟩
    obtain ⟨A, hA⟩ := k328r2p_exists hω2 hz hι hC
    refine ⟨A, ?_, hA⟩
    have h1 := hι A
    rw [hA, hz, ← Matrix.fromBlocks_diagonal, Matrix.fromBlocks_inj] at h1
    apply StatedAPI.mem_statedSL_of_det
    rw [← h1.1]
    simp [Matrix.det_diagonal, Fin.prod_univ_three]
    linear_combination h3
  · rw [Nat.card_congr (Subgroup.centerCongr eX).toEquiv]
    exact StatedCenterThree.card_center_statedSL_three
      (by rw [Nat.card_eq_fintype_card, hF])
  · have hcen : Subgroup.center ↥(StatedSL 3 F) =
        (StatedScalars (Fin 3) F).subgroupOf (StatedSL 3 F) := by
      have h1 := Subgroup.map_center_eq
        (CFSG.Assembly.LowTwoRank.specialLinearGroupEquivStatedSL 3 F)
      rw [CFSG.Assembly.LowTwoRank.map_center_eq_statedScalars 3 F] at h1
      exact h1.symm
    let e := (QuotientGroup.congr _ _ eX (Subgroup.map_center_eq eX)).trans
      (QuotientGroup.quotientMulEquivOfEq hcen)
    refine Or.inl (Or.inl ⟨by decide, ⟨Nat.prime_two, by norm_num, by norm_num, by decide,
      by decide⟩, F, inferInstance, inferInstance, ?_, ⟨e⟩⟩)
    rw [Nat.card_eq_fintype_card, hF]
    norm_num

end CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.K328
