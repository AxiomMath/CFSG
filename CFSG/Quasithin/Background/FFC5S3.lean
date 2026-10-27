module

public import CFSG.Quasithin.Background.FFC4Six

public section

namespace CFSG.Quasithin

namespace FFC

open CFSG.Assembly.LowTwoRank Matrix

@[expose] def S3Elems (X : Type*) [Group X] : Prop :=
  ∃ t c : X, t * t = 1 ∧ t ≠ 1 ∧ c ^ 3 = 1 ∧ c ≠ 1 ∧ t * c * t⁻¹ = c⁻¹

theorem S3Elems.of_injective {X Y : Type*} [Group X] [Group Y] (f : X →* Y) (hf : Function.Injective f)
    (h : S3Elems X) : S3Elems Y := by
  obtain ⟨t, c, ht2, ht1, hc3, hc1, htc⟩ := h
  refine ⟨f t, f c, by rw [← map_mul, ht2, map_one], fun h' => ht1 (hf (h'.trans (map_one f).symm)),
    by rw [← map_pow, hc3, map_one], fun h' => hc1 (hf (h'.trans (map_one f).symm)), ?_⟩
  rw [← map_mul, ← map_inv, ← map_mul, htc, map_inv]

theorem S3Elems.of_mulEquiv {X Y : Type*} [Group X] [Group Y] (e : X ≃* Y) (h : S3Elems X) : S3Elems Y :=
  h.of_injective e.toMonoidHom e.injective

section Two

variable {K : Type} [Field K] [CharP K 2]

@[expose] def matSwap : Matrix (Fin 2) (Fin 2) K := !![0, 1; 1, 0]

theorem det_matSwap : (matSwap : Matrix (Fin 2) (Fin 2) K).det = 1 := by
  have h2 : (2 : K) = 0 := by exact_mod_cast CharP.cast_eq_zero K 2
  simp [matSwap, Matrix.det_fin_two]
  linear_combination (-1 : K) * h2

@[expose] def slSwap : SpecialLinearGroup (Fin 2) K := ⟨matSwap, det_matSwap⟩

theorem slSwap_coe : ((slSwap : SpecialLinearGroup (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) = matSwap := rfl

omit [CharP K 2] in
theorem slThree_coe : ((slThree : SpecialLinearGroup (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) = matThree := rfl

theorem slSwap_mul_self : (slSwap : SpecialLinearGroup (Fin 2) K) * slSwap = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [slSwap_coe, matSwap, Matrix.mul_apply, Fin.sum_univ_two]

theorem slSwap_ne_one : (slSwap : SpecialLinearGroup (Fin 2) K) ≠ 1 := by
  intro h
  have := congrArg (fun g : SpecialLinearGroup (Fin 2) K => (g : Matrix (Fin 2) (Fin 2) K) 0 0) h
  simp [slSwap_coe, matSwap] at this

theorem slSwap_conj : (slSwap : SpecialLinearGroup (Fin 2) K) * slThree * slSwap⁻¹ = (slThree)⁻¹ := by
  have hinv : (slSwap : SpecialLinearGroup (Fin 2) K)⁻¹ = slSwap :=
    inv_eq_of_mul_eq_one_right slSwap_mul_self
  have h3 : (slThree : SpecialLinearGroup (Fin 2) K)⁻¹ = slThree ^ 2 :=
    inv_eq_of_mul_eq_one_right (by rw [← pow_succ', slThree_pow])
  rw [hinv, h3]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [slSwap_coe, slThree_coe, matSwap, matThree, pow_two, Matrix.mul_apply, Fin.sum_univ_two]

theorem s3Elems_slTwo : S3Elems (SpecialLinearGroup (Fin 2) K) :=
  ⟨slSwap, slThree, slSwap_mul_self, slSwap_ne_one, slThree_pow, slThree_ne_one, slSwap_conj⟩

theorem s3Elems_statedSL_two : S3Elems ↥(StatedSL 2 K) :=
  s3Elems_slTwo.of_mulEquiv (specialLinearGroupEquivStatedSL 2 K)

end Two

section Three

variable {K : Type} [Field K]

@[expose] def blk3 (A : Matrix (Fin 2) (Fin 2) K) : Matrix (Fin 3) (Fin 3) K :=
  !![A 0 0, A 0 1, 0; A 1 0, A 1 1, 0; 0, 0, 1]

theorem det_blk3 (A : Matrix (Fin 2) (Fin 2) K) : (blk3 A).det = A.det := by
  simp [blk3, Matrix.det_fin_three, Matrix.det_fin_two]

theorem blk3_mul (A B : Matrix (Fin 2) (Fin 2) K) : blk3 A * blk3 B = blk3 (A * B) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [blk3, Matrix.mul_apply, Fin.sum_univ_three, Fin.sum_univ_two]

theorem blk3_one : blk3 (1 : Matrix (Fin 2) (Fin 2) K) = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [blk3]

theorem blk3_injective : Function.Injective (blk3 (K := K)) := by
  intro A B h
  ext i j
  have := congrFun (congrFun h (Fin.castSucc i)) (Fin.castSucc j)
  fin_cases i <;> fin_cases j <;> simpa [blk3] using this

@[expose] noncomputable def slBlk : SpecialLinearGroup (Fin 2) K →* SpecialLinearGroup (Fin 3) K where
  toFun A := ⟨blk3 (A : Matrix (Fin 2) (Fin 2) K), by rw [det_blk3]; exact A.2⟩
  map_one' := by
    apply Subtype.ext
    exact blk3_one
  map_mul' A B := by
    apply Subtype.ext
    exact (blk3_mul _ _).symm

theorem slBlk_injective : Function.Injective (slBlk (K := K)) := by
  intro A B h
  apply Subtype.ext
  exact blk3_injective (congrArg Subtype.val h)

theorem s3Elems_statedSL_three [CharP K 2] : S3Elems ↥(StatedSL 3 K) :=
  (s3Elems_slTwo.of_injective slBlk slBlk_injective).of_mulEquiv (specialLinearGroupEquivStatedSL 3 K)

end Three

theorem s3Elems_perm_five : S3Elems (Equiv.Perm (Fin 5)) :=
  ⟨Equiv.swap 0 1, Equiv.swap 0 1 * Equiv.swap 1 2, by decide, by decide, by decide, by decide, by decide⟩

end FFC

end CFSG.Quasithin
