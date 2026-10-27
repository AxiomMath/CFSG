module

public import Mathlib.LinearAlgebra.Matrix.SpecialLinearGroup
public import Mathlib.Algebra.Field.ZMod
public import Mathlib.Algebra.Order.Field.Basic
public import Mathlib.FieldTheory.Finiteness
public import Mathlib.RepresentationTheory.Basic
public import Mathlib.Tactic.Positivity.Finset

public section

namespace CFSG.RankThree.FFModules

open scoped MatrixGroups
open Matrix

variable {F : Type*} [Field F]

@[expose] def dualMat (g : SL(3, F)) : Matrix (Fin 3) (Fin 3) F :=
  ((g⁻¹ : SL(3, F)) : Matrix (Fin 3) (Fin 3) F)ᵀ

theorem dualMat_mul (g h : SL(3, F)) : dualMat (g * h) = dualMat g * dualMat h := by
  simp only [dualMat, _root_.mul_inv_rev, Matrix.SpecialLinearGroup.coe_mul, Matrix.transpose_mul]

theorem dualMat_one : dualMat (1 : SL(3, F)) = 1 := by
  simp [dualMat]

theorem dualMat_inv_mul (g : SL(3, F)) :
    ((g : Matrix (Fin 3) (Fin 3) F))ᵀ * dualMat g = 1 := by
  rw [dualMat, ← Matrix.transpose_mul, ← Matrix.SpecialLinearGroup.coe_mul, inv_mul_cancel,
    Matrix.SpecialLinearGroup.coe_one, Matrix.transpose_one]

theorem dualMat_eq_one_iff (g : SL(3, F)) : dualMat g = 1 ↔ g = 1 := by
  constructor
  · intro h
    have h1 := dualMat_inv_mul g
    rw [h, Matrix.mul_one] at h1
    have h2 : (g : Matrix (Fin 3) (Fin 3) F) = 1 := by
      rw [← Matrix.transpose_transpose (g : Matrix (Fin 3) (Fin 3) F), h1, Matrix.transpose_one]
    exact Subtype.ext h2
  · rintro rfl
    exact dualMat_one

variable {W : Type*} [AddCommGroup W] [Module (ZMod 2) W]

@[expose] def IsNaturalModule (ρ : Representation (ZMod 2) SL(3, F) W) : Prop :=
  ∃ φ : W ≃+ (Fin 3 → F), ∀ g w, φ (ρ g w) = (g : Matrix (Fin 3) (Fin 3) F) *ᵥ φ w

@[expose] def IsDualNaturalModule (ρ : Representation (ZMod 2) SL(3, F) W) : Prop :=
  ∃ φ : W ≃+ (Fin 3 → F), ∀ g w, φ (ρ g w) = dualMat g *ᵥ φ w

@[expose] def natFix (B : Subgroup SL(3, F)) : Submodule F (Fin 3 → F) where
  carrier := {v | ∀ b ∈ B, (b : Matrix (Fin 3) (Fin 3) F) *ᵥ v = v}
  add_mem' {v w} hv hw b hb := by rw [Matrix.mulVec_add, hv b hb, hw b hb]
  zero_mem' b _ := Matrix.mulVec_zero _
  smul_mem' c v hv b hb := by rw [Matrix.mulVec_smul, hv b hb]

@[expose] def dualFix (B : Subgroup SL(3, F)) : Submodule F (Fin 3 → F) where
  carrier := {v | ∀ b ∈ B, dualMat b *ᵥ v = v}
  add_mem' {v w} hv hw b hb := by rw [Matrix.mulVec_add, hv b hb, hw b hb]
  zero_mem' b _ := Matrix.mulVec_zero _
  smul_mem' c v hv b hb := by rw [Matrix.mulVec_smul, hv b hb]

theorem mem_natFix {B : Subgroup SL(3, F)} {v : Fin 3 → F} :
    v ∈ natFix B ↔ ∀ b ∈ B, (b : Matrix (Fin 3) (Fin 3) F) *ᵥ v = v :=
  Iff.rfl

theorem mem_dualFix {B : Subgroup SL(3, F)} {v : Fin 3 → F} :
    v ∈ dualFix B ↔ ∀ b ∈ B, dualMat b *ᵥ v = v :=
  Iff.rfl

theorem ker_sub_one_ne_top {M : Matrix (Fin 3) (Fin 3) F} (hM : M ≠ 1) :
    {v : Fin 3 → F | M *ᵥ v = v} ≠ Set.univ := by
  intro h
  apply hM
  ext i j
  have hv : M *ᵥ Pi.single j 1 = Pi.single j 1 := by
    have : Pi.single j (1 : F) ∈ {v : Fin 3 → F | M *ᵥ v = v} := by rw [h]; trivial
    exact this
  have := congrFun hv i
  rw [Matrix.mulVec_single_one] at this
  simpa [Matrix.one_apply, Pi.single_apply, eq_comm] using this

theorem natFix_ne_top {B : Subgroup SL(3, F)} (hB : B ≠ ⊥) : natFix B ≠ ⊤ := by
  obtain ⟨b, hb1⟩ := (Subgroup.ne_bot_iff_exists_ne_one).mp hB
  intro htop
  have hM : ((b : SL(3, F)) : Matrix (Fin 3) (Fin 3) F) ≠ 1 := by
    intro h
    exact hb1 (Subtype.ext (Subtype.ext h))
  apply ker_sub_one_ne_top hM
  ext v
  simp only [Set.mem_ofPred_eq, Set.mem_univ, iff_true]
  have : v ∈ natFix B := by rw [htop]; trivial
  exact this b b.2

theorem dualFix_ne_top {B : Subgroup SL(3, F)} (hB : B ≠ ⊥) : dualFix B ≠ ⊤ := by
  obtain ⟨b, hb1⟩ := (Subgroup.ne_bot_iff_exists_ne_one).mp hB
  intro htop
  have hM : dualMat (b : SL(3, F)) ≠ 1 := by
    rw [Ne, dualMat_eq_one_iff]
    intro h
    exact hb1 (Subtype.ext h)
  apply ker_sub_one_ne_top hM
  ext v
  simp only [Set.mem_ofPred_eq, Set.mem_univ, iff_true]
  have : v ∈ dualFix B := by rw [htop]; trivial
  exact this b b.2

section Finite

variable [Fintype F]

omit [Field F] in
theorem card_vec : Nat.card (Fin 3 → F) = Fintype.card F ^ 3 := by
  rw [Nat.card_eq_fintype_card, Fintype.card_fun, Fintype.card_fin]

theorem card_le_of_ne_top {S : Submodule F (Fin 3 → F)} (hS : S ≠ ⊤) :
    Nat.card S ≤ Fintype.card F ^ 2 := by
  have h1 := Submodule.finrank_lt hS
  rw [Module.finrank_fin_fun] at h1
  rw [Module.natCard_eq_pow_finrank (K := F), Nat.card_eq_fintype_card]
  exact Nat.pow_le_pow_right Fintype.card_pos (by omega)

theorem card_natFix_mul_le {n : ℕ} (hF : Fintype.card F = 2 ^ n) {B : Subgroup SL(3, F)}
    (hB : B ≠ ⊥) : 2 ^ n * Nat.card (natFix B) ≤ Nat.card (Fin 3 → F) := by
  rw [card_vec, ← hF]
  calc Fintype.card F * Nat.card (natFix B) ≤ Fintype.card F * Fintype.card F ^ 2 :=
        Nat.mul_le_mul_left _ (card_le_of_ne_top (natFix_ne_top hB))
    _ = Fintype.card F ^ 3 := by ring

theorem card_dualFix_mul_le {n : ℕ} (hF : Fintype.card F = 2 ^ n) {B : Subgroup SL(3, F)}
    (hB : B ≠ ⊥) : 2 ^ n * Nat.card (dualFix B) ≤ Nat.card (Fin 3 → F) := by
  rw [card_vec, ← hF]
  calc Fintype.card F * Nat.card (dualFix B) ≤ Fintype.card F * Fintype.card F ^ 2 :=
        Nat.mul_le_mul_left _ (card_le_of_ne_top (dualFix_ne_top hB))
    _ = Fintype.card F ^ 3 := by ring

end Finite

theorem card_natFix_eq_of_iso {φ : (Fin 3 → F) ≃+ (Fin 3 → F)}
    (hφ : ∀ (g : SL(3, F)) v, φ ((g : Matrix (Fin 3) (Fin 3) F) *ᵥ v) = dualMat g *ᵥ φ v)
    (B : Subgroup SL(3, F)) : Nat.card (natFix B) = Nat.card (dualFix B) := by
  have key : ∀ v, v ∈ natFix B ↔ φ v ∈ dualFix B := by
    intro v
    rw [mem_natFix, mem_dualFix]
    constructor
    · intro h b hb
      rw [← hφ, h b hb]
    · intro h b hb
      apply φ.injective
      rw [hφ, h b hb]
  exact Nat.card_congr (φ.toEquiv.subtypeEquiv key)

theorem natFix_center {z : SL(3, F)} (hz : z ∈ Subgroup.center SL(3, F)) (hz1 : z ≠ 1)
    {v : Fin 3 → F} (hv : (z : Matrix (Fin 3) (Fin 3) F) *ᵥ v = v) : v = 0 := by
  obtain ⟨r, -, hrz⟩ := Matrix.SpecialLinearGroup.mem_center_iff.mp hz
  have hr1 : r ≠ 1 := by
    rintro rfl
    apply hz1
    ext i j
    rw [← hrz]
    simp [Matrix.scalar_apply, Matrix.one_apply, Matrix.diagonal_apply]
  rw [← hrz, Matrix.scalar_apply] at hv
  ext i
  have hi := congrFun hv i
  rw [Matrix.mulVec_diagonal] at hi
  have : (r - 1) * v i = 0 := by rw [sub_mul, one_mul, hi, sub_self]
  rcases mul_eq_zero.mp this with h | h
  · exact absurd (sub_eq_zero.mp h) hr1
  · simpa using h

theorem dualFix_center {z : SL(3, F)} (hz : z ∈ Subgroup.center SL(3, F)) (hz1 : z ≠ 1)
    {v : Fin 3 → F} (hv : dualMat z *ᵥ v = v) : v = 0 := by
  have hzi : z⁻¹ ∈ Subgroup.center SL(3, F) := Subgroup.inv_mem _ hz
  have hzi1 : z⁻¹ ≠ 1 := inv_ne_one.mpr hz1
  obtain ⟨r, -, hrz⟩ := Matrix.SpecialLinearGroup.mem_center_iff.mp hzi
  refine natFix_center hzi hzi1 ?_
  have ht : dualMat z = ((z⁻¹ : SL(3, F)) : Matrix (Fin 3) (Fin 3) F) := by
    rw [dualMat, ← hrz, Matrix.scalar_apply, Matrix.diagonal_transpose]
  rw [← ht]
  exact hv

theorem IsNaturalModule.eq_zero_of_center {ρ : Representation (ZMod 2) SL(3, F) W}
    (h : IsNaturalModule ρ) {z : SL(3, F)} (hz : z ∈ Subgroup.center SL(3, F)) (hz1 : z ≠ 1)
    {w : W} (hw : ρ z w = w) : w = 0 := by
  obtain ⟨φ, hφ⟩ := h
  have h0 : φ w = 0 := natFix_center hz hz1 (by rw [← hφ, hw])
  exact φ.injective (by rw [h0, map_zero])

theorem IsDualNaturalModule.eq_zero_of_center {ρ : Representation (ZMod 2) SL(3, F) W}
    (h : IsDualNaturalModule ρ) {z : SL(3, F)} (hz : z ∈ Subgroup.center SL(3, F)) (hz1 : z ≠ 1)
    {w : W} (hw : ρ z w = w) : w = 0 := by
  obtain ⟨φ, hφ⟩ := h
  have h0 : φ w = 0 := dualFix_center hz hz1 (by rw [← hφ, hw])
  exact φ.injective (by rw [h0, map_zero])

end CFSG.RankThree.FFModules
