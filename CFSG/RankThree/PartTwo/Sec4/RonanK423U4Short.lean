module

public import CFSG.RankThree.PartTwo.Sec21.KS21U4Blocks
public import CFSG.RankThree.PartTwo.Sec21.KS21U4Transport

public section

namespace CFSG.RankThree.PartTwo.Sec4.RonanK423
open Matrix CFSG CFSG.RankThree.PartTwo.Sec21.U4Lines
open CFSG.LieType.Universal.Unitary (SU mem_SU conjTr antidiag)
variable {F : Type} [Field F] [Finite F] [CharP F 2] (σ : F ≃+* F)

@[expose] noncomputable def shortTorusEl (x : Fˣ) : GL (Fin 4) F where
  val := diagonal ![(x : F), (x : F), (x : F)⁻¹, (x : F)⁻¹]
  inv := diagonal ![(x : F)⁻¹, (x : F)⁻¹, (x : F), (x : F)]
  val_inv := by
    rw [diagonal_mul_diagonal, ← diagonal_one]
    congr 1
    ext i
    fin_cases i <;> simp [x.ne_zero]
  inv_val := by
    rw [diagonal_mul_diagonal, ← diagonal_one]
    congr 1
    ext i
    fin_cases i <;> simp [x.ne_zero]

theorem coe_shortTorusEl (x : Fˣ) :
    ((shortTorusEl x : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F) =
      diagonal ![(x : F), (x : F), (x : F)⁻¹, (x : F)⁻¹] :=
  rfl

@[expose] noncomputable def shortTorus : Fˣ →* GL (Fin 4) F :=
  MonoidHom.mk' shortTorusEl fun x y => Units.ext (by
    simp only [Units.val_mul, coe_shortTorusEl, diagonal_mul_diagonal]
    congr 1
    ext i
    fin_cases i <;> simp [mul_inv, mul_comm])

theorem coe_shortTorus (x : Fˣ) :
    ((shortTorus x : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F) =
      diagonal ![(x : F), (x : F), (x : F)⁻¹, (x : F)⁻¹] :=
  rfl

theorem shortTorus_mul_shortSL (x : Fˣ) (r : GL (Fin 4) F) (hr : r ∈ shortSL σ) :
    shortTorus x * r = r * shortTorus x := by
  obtain ⟨B, rfl⟩ := hr
  apply Units.ext
  rw [Units.val_mul, Units.val_mul, coe_shortTorus, coe_iotaS]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [blkS, diagonal_mul, mul_diagonal] <;> ring

theorem short_decomp (hσ : ∀ c, σ (σ c) = c) {t : GL (Fin 4) F} {α β : F}
    (ht : (t : Matrix (Fin 4) (Fin 4) F) = diagonal ![α, α, β, β]) (hαβ : α ≠ β) :
    ∃ A : Subgroup (GL (Fin 4) F), (∀ a ∈ A, ∀ a' ∈ A, a * a' = a' * a) ∧
      (∀ a ∈ A, ∀ r ∈ shortSL σ, a * r = r * a) ∧
      ∀ g ∈ SU σ 4 ⊓ Subgroup.centralizer (Subgroup.zpowers t : Set (GL (Fin 4) F)),
        ∃ r ∈ shortSL σ, ∃ a ∈ A, g = r * a := by
  refine ⟨shortTorus.range, ?_, ?_, ?_⟩
  · rintro _ ⟨x, rfl⟩ _ ⟨y, rfl⟩
    rw [← map_mul, ← map_mul, mul_comm]
  · rintro _ ⟨x, rfl⟩ r hr
    exact shortTorus_mul_shortSL σ x r hr
  · rintro g ⟨hg, hgc⟩
    obtain ⟨hdet, hiso⟩ := mem_SU.1 hg
    obtain ⟨h02, h03, h12, h13, h20, h21, h30, h31⟩ := pattern_short_of_mem ht hαβ hgc
    set m : Matrix (Fin 4) (Fin 4) F := (g : Matrix (Fin 4) (Fin 4) F) with hm
    have hdetexp : m.det = (m 0 0 * m 1 1 - m 0 1 * m 1 0) * (m 2 2 * m 3 3 - m 2 3 * m 3 2) := by
      have e : Fin.succAbove (1 : Fin 4) (2 : Fin 3) = 3 := rfl
      simp [Matrix.det_succ_row_zero, Fin.sum_univ_succ, e, h02, h03, h12, h13, h20, h21, h30, h31]
      ring
    have hνQ : (m 0 0 * m 1 1 - m 0 1 * m 1 0) * (m 2 2 * m 3 3 - m 2 3 * m 3 2) = 1 := by
      rw [← hdetexp]
      exact hdet
    rw [antidiag_four] at hiso
    have E02 : σ (m 0 0) * m 3 2 + σ (m 1 0) * m 2 2 = 0 := by
      have e := congrFun (congrFun hiso 0) 2
      simp [conjTr, Matrix.mul_apply, Fin.sum_univ_four, h02, h03, h12, h13, h20, h21, h30,
        h31] at e
      linear_combination e
    have E03 : σ (m 0 0) * m 3 3 + σ (m 1 0) * m 2 3 = 1 := by
      have e := congrFun (congrFun hiso 0) 3
      simp [conjTr, Matrix.mul_apply, Fin.sum_univ_four, h02, h03, h12, h13, h20, h21, h30,
        h31] at e
      linear_combination e
    have E12 : σ (m 0 1) * m 3 2 + σ (m 1 1) * m 2 2 = 1 := by
      have e := congrFun (congrFun hiso 1) 2
      simp [conjTr, Matrix.mul_apply, Fin.sum_univ_four, h02, h03, h12, h13, h20, h21, h30,
        h31] at e
      linear_combination e
    have E13 : σ (m 0 1) * m 3 3 + σ (m 1 1) * m 2 3 = 0 := by
      have e := congrFun (congrFun hiso 1) 3
      simp [conjTr, Matrix.mul_apply, Fin.sum_univ_four, h02, h03, h12, h13, h20, h21, h30,
        h31] at e
      linear_combination e
    have hPQ : (σ (m 0 0) * σ (m 1 1) - σ (m 1 0) * σ (m 0 1)) *
        (m 2 2 * m 3 3 - m 2 3 * m 3 2) = 1 := by
      linear_combination (σ (m 0 0) * m 3 3 + σ (m 1 0) * m 2 3) * E12 + E03 -
        (σ (m 0 0) * m 3 2 + σ (m 1 0) * m 2 2) * E13
    have hσν : σ (m 0 0 * m 1 1 - m 0 1 * m 1 0) = m 0 0 * m 1 1 - m 0 1 * m 1 0 := by
      simp only [map_sub, map_mul]
      linear_combination (-(σ (m 0 0) * σ (m 1 1) - σ (m 1 0) * σ (m 0 1))) * hνQ +
        (m 0 0 * m 1 1 - m 0 1 * m 1 0) * hPQ
    have hν0 : m 0 0 * m 1 1 - m 0 1 * m 1 0 ≠ 0 := by
      intro h
      rw [h, zero_mul] at hνQ
      exact zero_ne_one hνQ
    have hinj : Function.Injective (fun c : F => c ^ 2) := by
      intro a b hab
      rcases sq_eq_sq_iff_eq_or_eq_neg.1 hab with h | h
      · exact h
      · rw [h, CharTwo.neg_eq]
    obtain ⟨l, hl⟩ := Finite.injective_iff_surjective.1 hinj (m 0 0 * m 1 1 - m 0 1 * m 1 0)
    have hl' : l ^ 2 = m 0 0 * m 1 1 - m 0 1 * m 1 0 := hl
    have hl0 : l ≠ 0 := by
      intro h
      apply hν0
      rw [← hl', h]
      norm_num
    have hσl : σ l = l := by
      have h1 : (σ l) ^ 2 = l ^ 2 := by
        rw [← map_pow σ l 2, hl']
        exact hσν
      rcases sq_eq_sq_iff_eq_or_eq_neg.1 h1 with h | h
      · exact h
      · rw [h, CharTwo.neg_eq]
    obtain ⟨x, hx⟩ : ∃ x : Fˣ, (x : F) = l := ⟨Units.mk0 l hl0, rfl⟩
    have hz : shortTorus x ∈ SU σ 4 := by
      rw [mem_SU]
      refine ⟨?_, ?_⟩
      · rw [coe_shortTorus, Matrix.det_diagonal, Fin.prod_univ_four]
        simp [hx, hl0]
      · rw [coe_shortTorus, antidiag_four]
        ext i j
        fin_cases i <;> fin_cases j <;>
          simp [conjTr, Matrix.mul_apply, Fin.sum_univ_four, diagonal, hx, hσl, hl0]
    obtain ⟨k, hkdef⟩ : ∃ k : GL (Fin 4) F, k = g * (shortTorus x)⁻¹ := ⟨_, rfl⟩
    have hkSU : k ∈ SU σ 4 := by
      rw [hkdef]
      exact mul_mem hg (inv_mem hz)
    have hdinv : (((shortTorus x)⁻¹ : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F) =
        diagonal ![l⁻¹, l⁻¹, l, l] := by
      rw [← map_inv shortTorus x, coe_shortTorus]
      simp [hx]
    have hkm : (k : Matrix (Fin 4) (Fin 4) F) = m * diagonal ![l⁻¹, l⁻¹, l, l] := by
      rw [hkdef, Units.val_mul, hdinv, ← hm]
    have hkpat : (k : Matrix (Fin 4) (Fin 4) F) 0 2 = 0 ∧ (k : Matrix (Fin 4) (Fin 4) F) 0 3 = 0 ∧
        (k : Matrix (Fin 4) (Fin 4) F) 1 2 = 0 ∧ (k : Matrix (Fin 4) (Fin 4) F) 1 3 = 0 ∧
        (k : Matrix (Fin 4) (Fin 4) F) 2 0 = 0 ∧ (k : Matrix (Fin 4) (Fin 4) F) 2 1 = 0 ∧
        (k : Matrix (Fin 4) (Fin 4) F) 3 0 = 0 ∧ (k : Matrix (Fin 4) (Fin 4) F) 3 1 = 0 := by
      simp [hkm, mul_diagonal, h02, h03, h12, h13, h20, h21, h30, h31]
    have hinv' : l * l⁻¹ = 1 := mul_inv_cancel₀ hl0
    have hkdet : (k : Matrix (Fin 4) (Fin 4) F) 0 0 * (k : Matrix (Fin 4) (Fin 4) F) 1 1 -
        (k : Matrix (Fin 4) (Fin 4) F) 0 1 * (k : Matrix (Fin 4) (Fin 4) F) 1 0 = 1 := by
      have hνl : m 0 0 * m 1 1 - m 0 1 * m 1 0 = l ^ 2 := hl'.symm
      simp [hkm, mul_diagonal]
      linear_combination (l⁻¹ ^ 2) * hνl + (l * l⁻¹ + 1) * hinv'
    have hkS : k ∈ shortSL σ := mem_shortSL_of σ hkSU hkpat hkdet
    refine ⟨k, hkS, shortTorus x, ⟨x, rfl⟩, ?_⟩
    rw [hkdef, inv_mul_cancel_right]

end CFSG.RankThree.PartTwo.Sec4.RonanK423
