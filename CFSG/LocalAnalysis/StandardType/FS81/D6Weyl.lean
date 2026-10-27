module

public import CFSG.LocalAnalysis.StandardType.FS81.D6Refl
public import CFSG.LocalAnalysis.StandardType.FS81.LocalGen
public import CFSG.LocalAnalysis.StandardType.FS81.BasisMonomial

public section

namespace CFSG.StandardType.FrameRoute.FS81

open CFSG.Open CFSG.Assembly
open scoped Matrix

@[expose] def vθ : Coords 7 := ![1, 0, 0, 0, 0, 0, 0]

@[expose] def vP : Fin 3 → Coords 7 :=
  ![![0, 1, 1, 0, 0, 0, 0], ![0, 0, 0, 1, 1, 0, 0], ![0, 0, 0, 0, 0, 1, 1]]

@[expose] def vM : Fin 3 → Coords 7 :=
  ![![0, 1, -1, 0, 0, 0, 0], ![0, 0, 0, 1, -1, 0, 0], ![0, 0, 0, 0, 0, 1, -1]]

@[expose] def wbar1 : Matrix (Fin 7) (Fin 7) (ZMod 3) :=
  d6Refl ![-1, 1, 1, 1, 1, -1, -1] * d6Refl ![-1, 1, 1, -1, -1, 1, 1]

@[expose] def wbar2 : Matrix (Fin 7) (Fin 7) (ZMod 3) :=
  d6Refl ![-1, 1, -1, -1, -1, 1, -1] * d6Refl ![-1, -1, 1, 1, 1, 1, -1]

theorem wbar1_mul_self : wbar1 * wbar1 = 1 := by decide

theorem wbar2_mul_self : wbar2 * wbar2 = 1 := by decide

theorem wbar1_vθ : wbar1 *ᵥ vθ = vP 0 := by decide

theorem wbar1_vP0 : wbar1 *ᵥ vP 0 = vθ := by decide

theorem wbar1_vP1 : wbar1 *ᵥ vP 1 = vP 2 := by decide

theorem wbar1_vP2 : wbar1 *ᵥ vP 2 = vP 1 := by decide

theorem wbar1_vM (j : Fin 3) : wbar1 *ᵥ vM j = vM j := by revert j; decide

theorem wbar2_vθ : wbar2 *ᵥ vθ = vM 2 := by decide

theorem wbar2_vM2 : wbar2 *ᵥ vM 2 = vθ := by decide

theorem wbar2_vM0 : wbar2 *ᵥ vM 0 = vP 1 := by decide

theorem wbar2_vP1 : wbar2 *ᵥ vP 1 = vM 0 := by decide

theorem wbar2_vP0 : wbar2 *ᵥ vP 0 = vP 0 := by decide

theorem wbar2_vM1 : wbar2 *ᵥ vM 1 = vM 1 := by decide

theorem wbar2_vP2 : wbar2 *ᵥ vP 2 = vP 2 := by decide

theorem vP_zero (j : Fin 3) : vP j 0 = 0 := by revert j; decide

theorem vM_zero (j : Fin 3) : vM j 0 = 0 := by revert j; decide

theorem wt_vP (j : Fin 3) : wt (vP j) = 2 := by revert j; decide

theorem wt_vM (j : Fin 3) : wt (vM j) = 2 := by revert j; decide

variable {G : Type} [Group G]

private theorem vec_pair (B : Basis3 G 7) {a b : Fin 7} (hab : a ≠ b) (c : ZMod 3)
    {v : Coords 7} (hv : v = Pi.single a 1 + Pi.single b c) :
    B.vec v = B.b a * B.b b ^ c.val := by
  rw [hv, Basis3.vec_add, Basis3.vec_single, Basis3.vec_single_eq_pow]

theorem vec_vP (B : Basis3 G 7) :
    B.vec (vP 0) = B.b 1 * B.b 2 ∧ B.vec (vP 1) = B.b 3 * B.b 4 ∧
      B.vec (vP 2) = B.b 5 * B.b 6 := by
  refine ⟨?_, ?_, ?_⟩
  · rw [vec_pair B (a := 1) (b := 2) (by decide) 1 (by decide)]; exact congrArg _ (pow_one _)
  · rw [vec_pair B (a := 3) (b := 4) (by decide) 1 (by decide)]; exact congrArg _ (pow_one _)
  · rw [vec_pair B (a := 5) (b := 6) (by decide) 1 (by decide)]; exact congrArg _ (pow_one _)

private theorem pow_val_neg_one (B : Basis3 G 7) (i : Fin 7) :
    B.b i ^ (-1 : ZMod 3).val = (B.b i)⁻¹ := by
  have h3 : B.b i ^ 3 = 1 := by rw [← B.ord i]; exact pow_orderOf_eq_one _
  rw [show (-1 : ZMod 3).val = 2 from rfl, eq_inv_iff_mul_eq_one, ← pow_succ, h3]

theorem vec_vM (B : Basis3 G 7) :
    B.vec (vM 0) = B.b 1 * (B.b 2)⁻¹ ∧ B.vec (vM 1) = B.b 3 * (B.b 4)⁻¹ ∧
      B.vec (vM 2) = B.b 5 * (B.b 6)⁻¹ := by
  refine ⟨?_, ?_, ?_⟩
  · rw [vec_pair B (a := 1) (b := 2) (by decide) (-1) (by decide), pow_val_neg_one]
  · rw [vec_pair B (a := 3) (b := 4) (by decide) (-1) (by decide), pow_val_neg_one]
  · rw [vec_pair B (a := 5) (b := 6) (by decide) (-1) (by decide), pow_val_neg_one]

theorem vec_vθ (B : Basis3 G 7) : B.vec vθ = B.b 0 := by
  rw [show vθ = Pi.single 0 1 by decide, Basis3.vec_single]

theorem exists_weyl_of_mem_realized [Finite G] {k : ℕ} {B : Basis3 G k}
    {A : Matrix (Fin k) (Fin k) (ZMod 3)} (hA : A ∈ B.realized ⊤) (hAA : A * A = 1) :
    ∃ w : G, w ∈ Subgroup.normalizer (B.span : Set G) ∧
      ∀ v : Coords k, w * B.vec v * w⁻¹ = B.vec (A *ᵥ v) ∧ w⁻¹ * B.vec v * w = B.vec (A *ᵥ v) := by
  obtain ⟨w, -, hw⟩ := hA
  refine ⟨w, Basis3.mem_normalizer_of_acts B hw, fun v => ⟨Basis3.acts_vec B hw v, ?_⟩⟩
  have h := Basis3.acts_vec B hw (A *ᵥ v)
  rw [Matrix.mulVec_mulVec, hAA, Matrix.one_mulVec] at h
  rw [← h]
  group

theorem exists_weyl1 [Finite G] {b₀ : G} {K E : Subgroup G}
    (hstd : StdLoc b₀ K E Row.D6) {B : Basis3 G 7} (hB : Adapted B b₀ K E)
    (hrec : RecOutD6 B b₀) :
    ∃ w : G, w ∈ Subgroup.normalizer (E : Set G) ∧
      ∀ v : Coords 7, w * B.vec v * w⁻¹ = B.vec (wbar1 *ᵥ v) ∧
        w⁻¹ * B.vec v * w = B.vec (wbar1 *ᵥ v) := by
  have hA : wbar1 ∈ B.realized ⊤ :=
    mul_mem_realized (d6Refl_mem_realized hstd hB hrec (by decide))
      (d6Refl_mem_realized hstd hB hrec (by decide))
  rw [← hB.1]
  exact exists_weyl_of_mem_realized hA wbar1_mul_self

theorem exists_weyl2 [Finite G] {b₀ : G} {K E : Subgroup G}
    (hstd : StdLoc b₀ K E Row.D6) {B : Basis3 G 7} (hB : Adapted B b₀ K E)
    (hrec : RecOutD6 B b₀) :
    ∃ w : G, w ∈ Subgroup.normalizer (E : Set G) ∧
      ∀ v : Coords 7, w * B.vec v * w⁻¹ = B.vec (wbar2 *ᵥ v) ∧
        w⁻¹ * B.vec v * w = B.vec (wbar2 *ᵥ v) := by
  have hA : wbar2 ∈ B.realized ⊤ :=
    mul_mem_realized (d6Refl_mem_realized hstd hB hrec (by decide))
      (d6Refl_mem_realized hstd hB hrec (by decide))
  rw [← hB.1]
  exact exists_weyl_of_mem_realized hA wbar2_mul_self

end CFSG.StandardType.FrameRoute.FS81
