module

public import CFSG.LocalAnalysis.StandardType.GGKGCentSL2Diag
public import CFSG.ClassicalInvolution.WeakCT.Defs
import CFSG.ClassicalInvolution.WeakCT.Center
import CFSG.ClassicalInvolution.Phan.Blocks
import CFSG.LocalAnalysis.StandardType.GGSixOddIndexF4Facts
import Mathlib.Tactic.Group
public import CFSG.LieType.CurtisTits.SpecialLinear

public section

namespace CFSG.StandardType.KGCentSL2

open Matrix CFSG.LocalAnalysis.ComponentInitial CFSG.ClassicalInvolution.WeakCT
  CFSG.ClassicalInvolution.Phan
open scoped MatrixGroups

variable {F : Type} [Field F]

private theorem sl2Diag_inv' (μ : Fˣ) : (sl2Diag F μ)⁻¹ = sl2Diag F μ⁻¹ := by
  rw [inv_eq_of_mul_eq_one_right]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]

theorem blockSL_diag_conj_blockSL_01 (μ : Fˣ) (A : SL(2, F)) :
    blockSL F 3 2 0 (by omega) (sl2Diag F μ) * blockSL F 3 2 1 (by omega) A *
        (blockSL F 3 2 0 (by omega) (sl2Diag F μ))⁻¹ =
      blockSL F 3 2 1 (by omega) (dconj μ⁻¹ A) := by
  rw [← map_inv, sl2Diag_inv']
  ext a b
  fin_cases a <;> fin_cases b <;>
    simp [coe_blockSL, blockMat_apply, Matrix.mul_apply, Fin.sum_univ_three, Matrix.one_apply] <;>
      field_simp

theorem blockSL_diag_conj_blockSL_10 (μ : Fˣ) (A : SL(2, F)) :
    blockSL F 3 2 1 (by omega) (sl2Diag F μ) * blockSL F 3 2 0 (by omega) A *
        (blockSL F 3 2 1 (by omega) (sl2Diag F μ))⁻¹ =
      blockSL F 3 2 0 (by omega) (dconj μ⁻¹ A) := by
  rw [← map_inv, sl2Diag_inv']
  ext a b
  fin_cases a <;> fin_cases b <;>
    simp [coe_blockSL, blockMat_apply, Matrix.mul_apply, Fin.sum_univ_three, Matrix.one_apply] <;>
      field_simp


private theorem centralizes_of_torus_conj [Finite F] [CharP F 2] (hF : 4 < Nat.card F)
    {X : Type} [Group X] (ιU ιV : SL(2, F) →* X) (hV : Function.Injective ιV)
    (hconj : ∀ (μ : Fˣ) (A : SL(2, F)),
      ιU (sl2Diag F μ) * ιV A * (ιU (sl2Diag F μ))⁻¹ = ιV (dconj μ⁻¹ A))
    {t : X} (htU : ∀ μ : Fˣ, t * ιU (sl2Diag F μ) = ιU (sl2Diag F μ) * t)
    (htV : t ∈ Subgroup.normalizer (ιV.range : Set X)) (m : ℕ) (ht2 : t ^ (2 ^ m) = 1) :
    ∀ A, t * ιV A = ιV A * t := by
  obtain ⟨α, hα⟩ := CFSG.StandardType.ggF4_exists_pullAut hV htV
  have hcomm : ∀ (ν : Fˣ) (A : SL(2, F)), α (dconj ν A) = dconj ν (α A) := by
    intro ν A
    apply hV
    have e1 : dconj ν A = dconj (ν⁻¹)⁻¹ A := by rw [inv_inv]
    have e2 : dconj ν (α A) = dconj (ν⁻¹)⁻¹ (α A) := by rw [inv_inv]
    rw [hα, e1, e2, ← hconj, ← hconj, hα]
    have hu := htU ν⁻¹
    calc t * (ιU (sl2Diag F ν⁻¹) * ιV A * (ιU (sl2Diag F ν⁻¹))⁻¹) * t⁻¹
        = (t * ιU (sl2Diag F ν⁻¹)) * ιV A * (t * ιU (sl2Diag F ν⁻¹))⁻¹ := by group
      _ = (ιU (sl2Diag F ν⁻¹) * t) * ιV A * (ιU (sl2Diag F ν⁻¹) * t)⁻¹ := by rw [hu]
      _ = ιU (sl2Diag F ν⁻¹) * (t * ιV A * t⁻¹) * (ιU (sl2Diag F ν⁻¹))⁻¹ := by group
  have hpow : ∀ (N : ℕ) (A : SL(2, F)), ιV ((α ^ N) A) = t ^ N * ιV A * t⁻¹ ^ N := by
    intro N
    induction N with
    | zero => intro A; simp
    | succ N ih =>
      intro A
      rw [pow_succ', MulAut.mul_apply, hα, ih]
      group
  have hk : ∀ A, (α ^ (2 ^ m)) A = A := fun A =>
    hV (by rw [hpow, inv_pow, ht2, inv_one, one_mul, mul_one])
  intro A
  have h1 := hα A
  rw [eq_one_of_commute_dconj hF α hcomm m hk A] at h1
  calc t * ιV A = t * ιV A * t⁻¹ * t := by group
    _ = ιV A * t := by rw [← h1]

theorem mem_centralizer_of_standardPair [Finite F] [CharP F 2] (hF : 4 < Nat.card F)
    {X : Type} [Group X] {W U V : Subgroup X} (h : LinearBlockStandardPair F W U V) {t : X}
    (htU : ∀ u ∈ U, t * u = u * t) (htV : t ∈ Subgroup.normalizer (V : Set X)) (m : ℕ)
    (ht2 : t ^ (2 ^ m) = 1) : ∀ v ∈ V, t * v = v * t := by
  obtain ⟨θ, c, -, hker, hUV⟩ := h
  set θ' : SL(3, F) →* X := θ.comp (MulAut.conj c⁻¹).toMonoidHom with hθ'
  have hker' : θ'.ker ≤ Subgroup.center SL(3, F) := by
    intro x hx
    have hx1 : θ (c⁻¹ * x * c⁻¹⁻¹) = 1 := hx
    have hz : c⁻¹ * x * c⁻¹⁻¹ ∈ Subgroup.center SL(3, F) := hker hx1
    rw [Subgroup.mem_center_iff] at hz ⊢
    intro g
    have := hz (c⁻¹ * g * c)
    simp only [inv_inv] at this
    calc g * x = c * ((c⁻¹ * g * c) * (c⁻¹ * x * c)) * c⁻¹ := by group
      _ = c * ((c⁻¹ * x * c) * (c⁻¹ * g * c)) * c⁻¹ := by rw [this]
      _ = x * g := by group
  have hmap : ∀ (i : ℕ) (hi : i + 2 ≤ 3),
      (((blockSL F 3 2 i hi).range.map (MulAut.conj c⁻¹).toMonoidHom).map θ) =
        (θ'.comp (blockSL F 3 2 i hi)).range := by
    intro i hi
    rw [Subgroup.map_map, ← MonoidHom.range_comp, MonoidHom.comp_assoc]
  have hinj : ∀ (i : ℕ) (hi : i + 2 ≤ 3), Function.Injective (θ'.comp (blockSL F 3 2 i hi)) :=
    fun i hi => comp_blockSL_injective hker' hi (by norm_num)
  rcases hUV with ⟨hU, hV⟩ | ⟨hV, hU⟩
  · rw [show CFSG.ClassicalInvolution.WeakCT.B12 F = (blockSL F 3 2 0 (by omega)).range from rfl, hmap] at hU
    rw [show CFSG.ClassicalInvolution.WeakCT.B23 F = (blockSL F 3 2 1 (by omega)).range from rfl, hmap] at hV
    subst hU hV
    have key := centralizes_of_torus_conj hF (θ'.comp (blockSL F 3 2 0 (by omega)))
      (θ'.comp (blockSL F 3 2 1 (by omega))) (hinj 1 (by omega))
      (fun μ A => by
        simp only [MonoidHom.comp_apply]
        rw [← map_inv, ← map_mul, ← map_mul, blockSL_diag_conj_blockSL_01])
      (fun μ => htU _ ⟨_, rfl⟩) htV m ht2
    rintro _ ⟨A, rfl⟩
    exact key A
  · rw [show CFSG.ClassicalInvolution.WeakCT.B12 F = (blockSL F 3 2 0 (by omega)).range from rfl, hmap] at hV
    rw [show CFSG.ClassicalInvolution.WeakCT.B23 F = (blockSL F 3 2 1 (by omega)).range from rfl, hmap] at hU
    subst hU hV
    have key := centralizes_of_torus_conj hF (θ'.comp (blockSL F 3 2 1 (by omega)))
      (θ'.comp (blockSL F 3 2 0 (by omega))) (hinj 0 (by omega))
      (fun μ A => by
        simp only [MonoidHom.comp_apply]
        rw [← map_inv, ← map_mul, ← map_mul, blockSL_diag_conj_blockSL_10])
      (fun μ => htU _ ⟨_, rfl⟩) htV m ht2
    rintro _ ⟨A, rfl⟩
    exact key A

end CFSG.StandardType.KGCentSL2

end
