module

public import CFSG.RankThree.PartOne.KA5L.Roots
public import CFSG.RankThree.PartOne.KE.SLnFamily

public noncomputable section

namespace CFSG.RankThree.PartOne.KA5L

open Matrix CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.RankThree.Chevalley
open CFSG.RankThree.PartOne.KE
open CFSG.ClassicalInvolution.WeakCT
open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
open scoped MatrixGroups

variable {L : Type} [Field L]

theorem a5Root_eq_sub (a b : Fin 6) : a5Root a b = a5Root a 0 - a5Root b 0 := by
  have h := a5Root_add a 0 b
  rw [a5Root_swap b 0] at h
  rw [← h]
  abel

theorem a5Frame_torus (b : Fin Tag.E7.rank → Lˣ) :
    ∃ d : Fin 6 → Lˣ, ∀ A : SL(6, L), rootDiagUnit Tag.E7 b * a5Frame L A *
      (rootDiagUnit Tag.E7 b)⁻¹ = a5Frame L (conjDiagn d A) := by
  set d : Fin 6 → Lˣ := fun i => rootChar b (a5Root i 0) with hd
  refine ⟨d, fun A => ?_⟩
  have h : (MulAut.conj (rootDiagUnit Tag.E7 b)).toMonoidHom.comp (a5Frame L) =
      (a5Frame L).comp (conjDiagnHom d) := by
    refine MonoidHom.eq_of_eqOn_dense
      (CFSG.LinearGroups.special_linear_elementary_generation (n := 6) (K := L)) ?_
    rintro _ ⟨i, j, hij, t, rfl⟩
    obtain ⟨ε, hε⟩ := a5Frame_transv (L := L) i j hij
    simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply,
      conjDiagnHom_apply]
    rw [hε, conjDiagn_transvection, hε, rootDiagUnit_conj_pinnedX b (isRoot_a5Root hij)]
    congr 1
    rw [a5Root_eq_sub i j, rootChar_sub]
    simp only [hd, Units.val_mul, Units.val_inv_eq_inv_val]
    ring
  exact DFunLike.congr_fun h A

section Diagonal

open CFSG.ClassicalInvolution.Phan (blockMat blockMat_apply)


@[expose] def hEntries (t : Fin 5) (s : Lˣ) (i : Fin 6) : L :=
  if i = t.castSucc then (s : L) else if i = t.succ then ((s⁻¹ : Lˣ) : L) else 1

theorem coe_blockSL2_HSL (t : Fin 5) (s : Lˣ) :
    ((blockSL2 L 5 t (HSL s) : SL(6, L)) : Matrix (Fin 6) (Fin 6) L) =
      Matrix.diagonal (hEntries t s) := by
  rw [blockSL2, coe_blockSL]
  ext a b
  fin_cases t <;> fin_cases a <;> fin_cases b <;>
    simp [blockMat_apply, HSL, hEntries]

theorem a5Frame_blockSL2_HSL (t : Fin 5) (s : Lˣ) :
    a5Frame L (blockSL2 L 5 t (HSL s)) = torusElt Tag.E7 L (a5chain t) s := by
  rw [← MonoidHom.comp_apply, a5Frame_comp_blockSL2, simpleRootSL2_HSL]

theorem exists_diag_eq_prod (A : SL(6, L))
    (hA : ∀ i j, i ≠ j → (A : Matrix (Fin 6) (Fin 6) L) i j = 0) :
    ∃ s : Fin 5 → Lˣ, A = blockSL2 L 5 0 (HSL (s 0)) * blockSL2 L 5 1 (HSL (s 1)) *
      blockSL2 L 5 2 (HSL (s 2)) * blockSL2 L 5 3 (HSL (s 3)) * blockSL2 L 5 4 (HSL (s 4)) := by
  have hdiag : (A : Matrix (Fin 6) (Fin 6) L) =
      Matrix.diagonal fun i => (A : Matrix (Fin 6) (Fin 6) L) i i := by
    ext i j
    by_cases hij : i = j
    · subst hij
      simp
    · simp [hA i j hij, Matrix.diagonal_apply_ne _ hij]
  have hdet : ∏ i, (A : Matrix (Fin 6) (Fin 6) L) i i = 1 := by
    have h := A.2
    rwa [hdiag, Matrix.det_diagonal] at h
  have hne : ∀ i, (A : Matrix (Fin 6) (Fin 6) L) i i ≠ 0 := by
    intro i h0
    have : ∏ j, (A : Matrix (Fin 6) (Fin 6) L) j j = 0 :=
      Finset.prod_eq_zero (Finset.mem_univ i) h0
    rw [hdet] at this
    exact one_ne_zero this
  set u : Fin 6 → Lˣ := fun i => Units.mk0 _ (hne i) with hu
  refine ⟨![u 0, u 0 * u 1, u 0 * u 1 * u 2, u 0 * u 1 * u 2 * u 3,
    u 0 * u 1 * u 2 * u 3 * u 4], ?_⟩
  apply Subtype.ext
  simp only [Matrix.SpecialLinearGroup.coe_mul, coe_blockSL2_HSL, Matrix.diagonal_mul_diagonal]
  rw [hdiag]
  congr 1
  funext i
  have h5 : (A : Matrix (Fin 6) (Fin 6) L) 5 5 =
      ((u 0 * u 1 * u 2 * u 3 * u 4)⁻¹ : Lˣ) := by
    rw [Units.val_inv_eq_inv_val]
    refine eq_inv_of_mul_eq_one_right ?_
    rw [Fin.prod_univ_six] at hdet
    simp only [hu, Units.val_mul, Units.val_mk0]
    linear_combination hdet
  have n0 := hne 0
  have n1 := hne 1
  have n2 := hne 2
  have n3 := hne 3
  have n4 := hne 4
  fin_cases i <;> simp [hEntries, h5, hu] <;> field_simp

theorem a5Frame_diag_mem_torusGroup (A : SL(6, L))
    (hA : ∀ i j, i ≠ j → (A : Matrix (Fin 6) (Fin 6) L) i j = 0) :
    a5Frame L A ∈ torusGroup Tag.E7 L := by
  obtain ⟨s, rfl⟩ := exists_diag_eq_prod A hA
  simp only [map_mul, a5Frame_blockSL2_HSL]
  have hmem : ∀ (t : Fin 5) (s : Lˣ), torusElt Tag.E7 L (a5chain t) s ∈ torusGroup Tag.E7 L :=
    fun t s => Subgroup.subset_closure ⟨(a5chain t, s), rfl⟩
  exact mul_mem (mul_mem (mul_mem (mul_mem (hmem _ _) (hmem _ _)) (hmem _ _)) (hmem _ _)) (hmem _ _)

end Diagonal

end CFSG.RankThree.PartOne.KA5L
