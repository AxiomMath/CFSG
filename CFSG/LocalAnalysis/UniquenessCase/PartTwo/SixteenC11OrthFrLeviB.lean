module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC11OrthFrLeviA

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Open Subgroup
open scoped Matrix

theorem s16c11_fr_hat_mulVec_A {m : ℕ} (hm : m = 3 ∨ m = 4)
    (h : ↥(S16C11FrO (m - 2))) (v : S16C11FrVec m) (i : Fin 2) :
    (s16c11_fr_hat m (s16c11_fr_bound3 hm)
        (((h : Matrix.GeneralLinearGroup (S16C11FrIdx (m - 2)) (ZMod 2)) : Matrix (S16C11FrIdx (m
            - 2)) (S16C11FrIdx (m - 2)) (ZMod 2))) *ᵥ v)
      (s16c11_fr_A m (s16c11_fr_bound3 hm) i) = v (s16c11_fr_A m (s16c11_fr_bound3 hm) i) := by
  rw [Matrix.mulVec, dotProduct]
  trans ∑ k, (Pi.single (s16c11_fr_A m (s16c11_fr_bound3 hm) i)
      (1 : ZMod 2) : S16C11FrIdx m → ZMod 2) k * v k
  · exact Finset.sum_congr rfl fun k _ => by
      rw [← Equiv.apply_symm_apply (s16c11_fr_part m (s16c11_fr_bound3 hm)) k,
        s16c11_fr_hat_row_A_eval hm
          (((h : Matrix.GeneralLinearGroup (S16C11FrIdx (m - 2)) (ZMod 2)) : Matrix (S16C11FrIdx
              (m - 2)) (S16C11FrIdx (m - 2)) (ZMod 2))) i]
  · rw [Finset.sum_eq_single (s16c11_fr_A m (s16c11_fr_bound3 hm) i)]
    · rw [Pi.single_eq_same, one_mul]
    · intro k _ hk; rw [Pi.single_eq_of_ne hk, zero_mul]
    · intro hc; exact absurd (Finset.mem_univ _) hc

theorem s16c11_fr_hat_mulVec_B {m : ℕ} (hm : m = 3 ∨ m = 4)
    (h : ↥(S16C11FrO (m - 2))) (v : S16C11FrVec m) (i : Fin 2) :
    (s16c11_fr_hat m (s16c11_fr_bound3 hm)
        (((h : Matrix.GeneralLinearGroup (S16C11FrIdx (m - 2)) (ZMod 2)) : Matrix (S16C11FrIdx (m
            - 2)) (S16C11FrIdx (m - 2)) (ZMod 2))) *ᵥ v)
      (s16c11_fr_B m (s16c11_fr_bound3 hm) i) = v (s16c11_fr_B m (s16c11_fr_bound3 hm) i) := by
  rw [Matrix.mulVec, dotProduct]
  trans ∑ k, (Pi.single (s16c11_fr_B m (s16c11_fr_bound3 hm) i)
      (1 : ZMod 2) : S16C11FrIdx m → ZMod 2) k * v k
  · exact Finset.sum_congr rfl fun k _ => by
      rw [← Equiv.apply_symm_apply (s16c11_fr_part m (s16c11_fr_bound3 hm)) k,
        s16c11_fr_hat_row_B_eval hm
          (((h : Matrix.GeneralLinearGroup (S16C11FrIdx (m - 2)) (ZMod 2)) : Matrix (S16C11FrIdx
              (m - 2)) (S16C11FrIdx (m - 2)) (ZMod 2))) i]
  · rw [Finset.sum_eq_single (s16c11_fr_B m (s16c11_fr_bound3 hm) i)]
    · rw [Pi.single_eq_same, one_mul]
    · intro k _ hk; rw [Pi.single_eq_of_ne hk, zero_mul]
    · intro hc; exact absurd (Finset.mem_univ _) hc

theorem s16c11_fr_hat_mulVec_emb {m : ℕ} (hm : m = 3 ∨ m = 4)
    (h : ↥(S16C11FrO (m - 2))) (v : S16C11FrVec m) (c : S16C11FrIdx (m - 2)) :
    (s16c11_fr_hat m (s16c11_fr_bound3 hm)
        (((h : Matrix.GeneralLinearGroup (S16C11FrIdx (m - 2)) (ZMod 2)) : Matrix (S16C11FrIdx (m
            - 2)) (S16C11FrIdx (m - 2)) (ZMod 2))) *ᵥ v)
      (s16c11_fr_emb m (s16c11_fr_bound3 hm) c) =
      ((((h : Matrix.GeneralLinearGroup (S16C11FrIdx (m - 2)) (ZMod 2)) : Matrix (S16C11FrIdx (m -
          2)) (S16C11FrIdx (m - 2)) (ZMod 2))) *ᵥ
        (v ∘ s16c11_fr_emb m (s16c11_fr_bound3 hm))) c := by
  rw [Matrix.mulVec, dotProduct, Matrix.mulVec, dotProduct]
  rw [show (∑ k, s16c11_fr_hat m (s16c11_fr_bound3 hm) (((h : Matrix.GeneralLinearGroup
      (S16C11FrIdx (m - 2)) (ZMod 2)) : Matrix (S16C11FrIdx (m - 2)) (S16C11FrIdx (m - 2)) (ZMod
      2)))
        (s16c11_fr_emb m (s16c11_fr_bound3 hm) c) k * v k) =
      ∑ k ∈ Finset.univ.image (s16c11_fr_emb m (s16c11_fr_bound3 hm)),
        s16c11_fr_hat m (s16c11_fr_bound3 hm) (((h : Matrix.GeneralLinearGroup (S16C11FrIdx (m -
            2)) (ZMod 2)) : Matrix (S16C11FrIdx (m - 2)) (S16C11FrIdx (m - 2)) (ZMod 2)))
          (s16c11_fr_emb m (s16c11_fr_bound3 hm) c) k * v k from
    (Finset.sum_subset (Finset.subset_univ _) (fun k _ hk => by
      rw [s16c11_fr_hat_row_C_zero hm (((h : Matrix.GeneralLinearGroup (S16C11FrIdx (m - 2)) (ZMod
          2)) : Matrix (S16C11FrIdx (m - 2)) (S16C11FrIdx (m - 2)) (ZMod 2))) c hk,
          zero_mul])).symm]
  rw [Finset.sum_image (s16c11_fr_emb_injective (s16c11_fr_bound3 hm)).injOn]
  exact Finset.sum_congr rfl fun c' _ => by rw [s16c11_fr_hat_emb hm, Function.comp_apply]

theorem s16c11_fr_hat_isometry {m : ℕ} (hm : m = 3 ∨ m = 4)
    (h : ↥(S16C11FrO (m - 2))) (v : S16C11FrVec m) :
    S16C11FrQ m (s16c11_fr_hat m (s16c11_fr_bound3 hm)
        (((h : Matrix.GeneralLinearGroup (S16C11FrIdx (m - 2)) (ZMod 2)) : Matrix (S16C11FrIdx (m
            - 2)) (S16C11FrIdx (m - 2)) (ZMod 2))) *ᵥ v) =
      S16C11FrQ m v := by
  rw [s16c11_fr_Q_decomp hm (s16c11_fr_hat m (s16c11_fr_bound3 hm) (((h :
      Matrix.GeneralLinearGroup (S16C11FrIdx (m - 2)) (ZMod 2)) : Matrix (S16C11FrIdx (m - 2))
      (S16C11FrIdx (m - 2)) (ZMod 2))) *ᵥ v),
    s16c11_fr_Q_decomp hm v]
  rw [s16c11_fr_hat_mulVec_A hm h v 0, s16c11_fr_hat_mulVec_A hm h v 1,
    s16c11_fr_hat_mulVec_B hm h v 0, s16c11_fr_hat_mulVec_B hm h v 1]
  have hcomp : (s16c11_fr_hat m (s16c11_fr_bound3 hm) (((h : Matrix.GeneralLinearGroup
      (S16C11FrIdx (m - 2)) (ZMod 2)) : Matrix (S16C11FrIdx (m - 2)) (S16C11FrIdx (m - 2)) (ZMod
      2))) *ᵥ v) ∘
        s16c11_fr_emb m (s16c11_fr_bound3 hm) =
      (((h : Matrix.GeneralLinearGroup (S16C11FrIdx (m - 2)) (ZMod 2)) : Matrix (S16C11FrIdx (m -
          2)) (S16C11FrIdx (m - 2)) (ZMod 2))) *ᵥ
        (v ∘ s16c11_fr_emb m (s16c11_fr_bound3 hm)) := by
    funext c
    exact s16c11_fr_hat_mulVec_emb hm h v c
  rw [hcomp,
    show S16C11FrQ (m - 2)
        ((((h : Matrix.GeneralLinearGroup (S16C11FrIdx (m - 2)) (ZMod 2)) :
          Matrix (S16C11FrIdx (m - 2)) (S16C11FrIdx (m - 2)) (ZMod 2)) *ᵥ
          (v ∘ s16c11_fr_emb m (s16c11_fr_bound3 hm)))) =
      S16C11FrQ (m - 2) (v ∘ s16c11_fr_emb m (s16c11_fr_bound3 hm)) from
    CFSG.GroupTheory.WeirSylow.apply_mulVec_of_mem_isometryCore h.2
      (v ∘ s16c11_fr_emb m (s16c11_fr_bound3 hm))]
  try ring

theorem s16c11_fr_hat_fixes {m : ℕ} (hm : m = 3 ∨ m = 4)
    (h : ↥(S16C11FrO (m - 2))) (i : Fin 2) :
    s16c11_fr_hat m (s16c11_fr_bound3 hm)
        (((h : Matrix.GeneralLinearGroup (S16C11FrIdx (m - 2)) (ZMod 2)) : Matrix (S16C11FrIdx (m
            - 2)) (S16C11FrIdx (m - 2)) (ZMod 2))) *ᵥ
      s16c11_fr_Eb m hm i = s16c11_fr_Eb m hm i := by
  funext j
  rw [s16c11_fr_Eb, Matrix.mulVec_single_one, Matrix.col_apply]
  exact s16c11_fr_hat_col_A hm (((h : Matrix.GeneralLinearGroup (S16C11FrIdx (m - 2)) (ZMod 2)) :
      Matrix (S16C11FrIdx (m - 2)) (S16C11FrIdx (m - 2)) (ZMod 2))) i j

theorem s16c11_fr_hat_isInK {m : ℕ} (hm : m = 3 ∨ m = 4)
    (h : ↥(S16C11FrO (m - 2))) :
    ∀ w ∈ s16c11FrLine m, s16c11_fr_hat m (s16c11_fr_bound3 hm)
      (((h : Matrix.GeneralLinearGroup (S16C11FrIdx (m - 2)) (ZMod 2)) : Matrix (S16C11FrIdx (m -
          2)) (S16C11FrIdx (m - 2)) (ZMod 2))) *ᵥ w = w := by
  intro w hw
  simp only [s16c11FrLine, Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · rw [← s16c11_fr_Eb_zero hm]
    exact s16c11_fr_hat_fixes hm h 0
  · rw [← s16c11_fr_Eb_one hm]
    exact s16c11_fr_hat_fixes hm h 1
  · rw [← s16c11_fr_Eb_zero hm, ← s16c11_fr_Eb_one hm, Matrix.mulVec_add,
      s16c11_fr_hat_fixes hm h 0, s16c11_fr_hat_fixes hm h 1]

theorem s16c11_fr_hat_block {m : ℕ} (hm : m = 3 ∨ m = 4)
    (h : ↥(S16C11FrO (m - 2))) :
    s16c11_fr_block m hm (s16c11_fr_hat m (s16c11_fr_bound3 hm)
      (((h : Matrix.GeneralLinearGroup (S16C11FrIdx (m - 2)) (ZMod 2)) : Matrix (S16C11FrIdx (m -
          2)) (S16C11FrIdx (m - 2)) (ZMod 2)))) =
      (((h : Matrix.GeneralLinearGroup (S16C11FrIdx (m - 2)) (ZMod 2)) : Matrix (S16C11FrIdx (m -
          2)) (S16C11FrIdx (m - 2)) (ZMod 2))) := by
  ext r c
  rw [s16c11_fr_block, Matrix.submatrix_apply, s16c11_fr_hat_emb hm]

theorem s16c11_fr_hat_mul_inv {m : ℕ} (hm : m = 3 ∨ m = 4)
    (h : ↥(S16C11FrO (m - 2))) :
    s16c11_fr_hat m (s16c11_fr_bound3 hm)
        (((h : Matrix.GeneralLinearGroup (S16C11FrIdx (m - 2)) (ZMod 2)) : Matrix (S16C11FrIdx (m
            - 2)) (S16C11FrIdx (m - 2)) (ZMod 2))) *
      s16c11_fr_hat m (s16c11_fr_bound3 hm)
        (((h⁻¹ : Matrix.GeneralLinearGroup (S16C11FrIdx (m - 2)) (ZMod 2)) : Matrix (S16C11FrIdx
            (m - 2)) (S16C11FrIdx (m - 2)) (ZMod 2))) = 1 := by
  have hD : s16c11_fr_diag m (((h : Matrix.GeneralLinearGroup (S16C11FrIdx (m - 2)) (ZMod 2)) :
      Matrix (S16C11FrIdx (m - 2)) (S16C11FrIdx (m - 2)) (ZMod 2))) *
      s16c11_fr_diag m (((h⁻¹ : Matrix.GeneralLinearGroup (S16C11FrIdx (m - 2)) (ZMod 2)) : Matrix
          (S16C11FrIdx (m - 2)) (S16C11FrIdx (m - 2)) (ZMod 2))) = 1 := by
    simp only [s16c11_fr_diag, Matrix.fromBlocks_multiply, Matrix.zero_mul, Matrix.mul_zero,
      add_zero, zero_add]
    rw [show (((h : Matrix.GeneralLinearGroup (S16C11FrIdx (m - 2)) (ZMod 2)) : Matrix
        (S16C11FrIdx (m - 2)) (S16C11FrIdx (m - 2)) (ZMod 2))) * (((h⁻¹ :
        Matrix.GeneralLinearGroup (S16C11FrIdx (m - 2)) (ZMod 2)) : Matrix (S16C11FrIdx (m - 2))
        (S16C11FrIdx (m - 2)) (ZMod 2))) = 1 from by
      rw [← Units.val_mul, mul_inv_cancel, Units.val_one]]
    simp only [Matrix.fromBlocks_multiply, Matrix.one_mul, Matrix.mul_one, Matrix.zero_mul,
      Matrix.mul_zero, add_zero, zero_add, Matrix.fromBlocks_one]
  rw [s16c11_fr_hat, s16c11_fr_hat,
    ← Matrix.coe_reindexRingEquiv (ZMod 2) (s16c11_fr_part m (s16c11_fr_bound3 hm))]
  rw [← map_mul, hD, map_one]

theorem s16c11_fr_levi_surjective {m : ℕ} (hm : m = 3 ∨ m = 4) :
    Function.Surjective (s16c11_fr_leviHom hm) := by
  intro h
  let u : (Matrix (S16C11FrIdx m) (S16C11FrIdx m) (ZMod 2))ˣ :=
    Units.mkOfMulEqOne (s16c11_fr_hat m (s16c11_fr_bound3 hm)
        (((h : Matrix.GeneralLinearGroup (S16C11FrIdx (m - 2)) (ZMod 2)) : Matrix (S16C11FrIdx (m
            - 2)) (S16C11FrIdx (m - 2)) (ZMod 2))))
      (s16c11_fr_hat m (s16c11_fr_bound3 hm)
        (((h⁻¹ : Matrix.GeneralLinearGroup (S16C11FrIdx (m - 2)) (ZMod 2)) : Matrix (S16C11FrIdx
            (m - 2)) (S16C11FrIdx (m - 2)) (ZMod 2))))
      (s16c11_fr_hat_mul_inv hm h)
  have hmem : u ∈ S16C11FrO m :=
    Subgroup.subset_closure fun v => by
      change S16C11FrQ m ((u : Matrix (S16C11FrIdx m) (S16C11FrIdx m) (ZMod 2)) *ᵥ v) =
        S16C11FrQ m v
      rw [show (u : Matrix (S16C11FrIdx m) (S16C11FrIdx m) (ZMod 2)) =
          s16c11_fr_hat m (s16c11_fr_bound3 hm)
            (((h : Matrix.GeneralLinearGroup (S16C11FrIdx (m - 2)) (ZMod 2)) : Matrix (S16C11FrIdx
                (m - 2)) (S16C11FrIdx (m - 2)) (ZMod 2))) from rfl]
      exact s16c11_fr_hat_isometry hm h v
  let g : ↥(s16c11FrK m) := ⟨⟨u, hmem⟩, by
    intro w hw
    change (u : Matrix (S16C11FrIdx m) (S16C11FrIdx m) (ZMod 2)) *ᵥ w = w
    rw [show (u : Matrix (S16C11FrIdx m) (S16C11FrIdx m) (ZMod 2)) =
        s16c11_fr_hat m (s16c11_fr_bound3 hm)
          (((h : Matrix.GeneralLinearGroup (S16C11FrIdx (m - 2)) (ZMod 2)) : Matrix (S16C11FrIdx
              (m - 2)) (S16C11FrIdx (m - 2)) (ZMod 2))) from rfl]
    exact s16c11_fr_hat_isInK hm h w hw⟩
  refine ⟨g, ?_⟩
  apply Subtype.ext
  apply Units.ext
  change (s16c11_fr_blockUnit hm g : Matrix (S16C11FrIdx (m - 2)) (S16C11FrIdx (m - 2))
        (ZMod 2)) =
    (((h : Matrix.GeneralLinearGroup (S16C11FrIdx (m - 2)) (ZMod 2)) :
      Matrix (S16C11FrIdx (m - 2)) (S16C11FrIdx (m - 2)) (ZMod 2)))
  change s16c11_fr_block m hm
      ((((g : ↥(s16c11FrK m)) : ↥(S16C11FrO m)) :
        Matrix.GeneralLinearGroup (S16C11FrIdx m) (ZMod 2)) :
        Matrix (S16C11FrIdx m) (S16C11FrIdx m) (ZMod 2)) =
    (((h : Matrix.GeneralLinearGroup (S16C11FrIdx (m - 2)) (ZMod 2)) :
      Matrix (S16C11FrIdx (m - 2)) (S16C11FrIdx (m - 2)) (ZMod 2)))
  change s16c11_fr_block m hm (s16c11_fr_hat m (s16c11_fr_bound3 hm)
    (((h : Matrix.GeneralLinearGroup (S16C11FrIdx (m - 2)) (ZMod 2)) : Matrix (S16C11FrIdx (m -
        2)) (S16C11FrIdx (m - 2)) (ZMod 2)))) =
    (((h : Matrix.GeneralLinearGroup (S16C11FrIdx (m - 2)) (ZMod 2)) : Matrix (S16C11FrIdx (m -
        2)) (S16C11FrIdx (m - 2)) (ZMod 2)))
  rw [s16c11_fr_hat_block]

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
