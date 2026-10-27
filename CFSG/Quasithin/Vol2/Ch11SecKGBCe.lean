module

public import CFSG.Quasithin.Vol2.Ch11SecKGBCd
public import CFSG.LocalAnalysis.ComponentInitial.LinearHigherSylowNormalizer
public import CFSG.Quasithin.Vol2.Ch11SecKGBCc

public section

namespace CFSG.Quasithin.Vol2.Ch11.SecB.C10KG

open CFSG.LocalAnalysis.ComponentInitial.LinearFlag Matrix

variable {K : Type} [Field K] [Finite K] [CharP K 2]

theorem exists_unitriangular_mul_tor {A : SpecialLinearGroup (Fin 3) K}
    (hA : A ∈ upperTriangular 3 K) :
    ∃ u ∈ unitriangular 3 K, ∃ a b : Kˣ, A = u * (torOne a * torTwo b) := by
  have hdet : (A : Matrix (Fin 3) (Fin 3) K) 0 0 * (A : Matrix (Fin 3) (Fin 3) K) 1 1 *
      (A : Matrix (Fin 3) (Fin 3) K) 2 2 = 1 := by
    have h := A.2
    rwa [det_of_isUpperTriangular (fun i j hij => mem_upperTriangular.mp hA i j hij),
      Fin.prod_univ_three] at h
  have h0 : (A : Matrix (Fin 3) (Fin 3) K) 0 0 ≠ 0 := fun h => by simp [h] at hdet
  have h1 : (A : Matrix (Fin 3) (Fin 3) K) 1 1 ≠ 0 := fun h => by simp [h] at hdet
  have h2 : (A : Matrix (Fin 3) (Fin 3) K) 2 2 ≠ 0 := fun h => by simp [h] at hdet
  obtain ⟨r, hr⟩ := FiniteField.isSquare_of_char_two (ringChar.eq K 2)
    ((A : Matrix (Fin 3) (Fin 3) K) 2 2)⁻¹
  have hr0 : r ≠ 0 := by
    rintro rfl
    rw [mul_zero, inv_eq_zero] at hr
    exact h2 hr
  set b : Kˣ := Units.mk0 r hr0 with hb
  set a : Kˣ := Units.mk0 ((A : Matrix (Fin 3) (Fin 3) K) 0 0) h0 * b⁻¹ with ha
  set e : Fin 3 → K := ![((A : Matrix (Fin 3) (Fin 3) K) 0 0)⁻¹,
    ((A : Matrix (Fin 3) (Fin 3) K) 1 1)⁻¹, ((A : Matrix (Fin 3) (Fin 3) K) 2 2)⁻¹] with he
  have hD : ((torOne a * torTwo b : SpecialLinearGroup (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) =
      diagonal fun i => ((A : Matrix (Fin 3) (Fin 3) K) i i) := by
    rw [SpecialLinearGroup.coe_mul, coe_torOne, coe_torTwo, diagonal_mul_diagonal]
    congr 1
    ext i
    fin_cases i
    · simp [ha, hb, hr0]
    · simp only [ha, hb, Fin.isValue, Fin.mk_one, Matrix.cons_val_one, Matrix.cons_val_zero,
        _root_.mul_inv_rev, inv_inv, Units.val_mul, Units.val_inv_eq_inv_val, Units.val_mk0]
      have h11 : (A : Matrix (Fin 3) (Fin 3) K) 1 1 =
          ((A : Matrix (Fin 3) (Fin 3) K) 0 0)⁻¹ * ((A : Matrix (Fin 3) (Fin 3) K) 2 2)⁻¹ := by
        field_simp
        linear_combination hdet
      rw [h11, ← inv_inv ((A : Matrix (Fin 3) (Fin 3) K) 2 2), hr]
      field_simp
    · simp only [hb, Fin.isValue, Fin.reduceFinMk, Matrix.cons_val_two, Matrix.tail_cons,
        Matrix.head_cons, one_mul, Units.val_inv_eq_inv_val, Units.val_pow_eq_pow_val,
        Units.val_mk0]
      rw [pow_two, ← hr, inv_inv]
  have hdetu : ((A : Matrix (Fin 3) (Fin 3) K) * diagonal e).det = 1 := by
    rw [det_mul, A.2, det_diagonal, Fin.prod_univ_three, one_mul, he]
    simp only [Fin.isValue, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
      Matrix.tail_cons, Matrix.head_cons]
    rw [← mul_inv, ← mul_inv, hdet, inv_one]
  let u : SpecialLinearGroup (Fin 3) K := ⟨(A : Matrix (Fin 3) (Fin 3) K) * diagonal e, hdetu⟩
  refine ⟨u, ?_, a, b, ?_⟩
  · rw [mem_unitriangular]
    refine ⟨fun i j hij => ?_, fun i => ?_⟩
    · change ((A : Matrix (Fin 3) (Fin 3) K) * diagonal e) i j = 0
      rw [mul_diagonal, mem_upperTriangular.mp hA i j hij, zero_mul]
    · change ((A : Matrix (Fin 3) (Fin 3) K) * diagonal e) i i = 1
      rw [mul_diagonal]
      fin_cases i <;> simp [he, h0, h1, h2]
  · apply Subtype.ext
    rw [SpecialLinearGroup.coe_mul, hD]
    change (A : Matrix (Fin 3) (Fin 3) K) =
      (A : Matrix (Fin 3) (Fin 3) K) * diagonal e * diagonal _
    rw [mul_assoc, diagonal_mul_diagonal]
    have : (fun i => e i * (A : Matrix (Fin 3) (Fin 3) K) i i) = fun _ => (1 : K) := by
      ext i
      fin_cases i <;> simp [he, h0, h1, h2]
    rw [this, diagonal_one, mul_one]

theorem isPGroup_commutator_l3 {Y : Type} [Group Y] [Finite Y] (φ : Y →* projectiveSL 3 K)
    (hφ : Function.Surjective φ) (hZ : φ.ker ≤ Subgroup.center Y) (hodd : Odd (Nat.card φ.ker))
    (Q : Sylow 2 (projectiveSL 3 K)) :
    IsPGroup 2 ↥⁅(Subgroup.normalizer ((Q : Subgroup (projectiveSL 3 K)) :
        Set (projectiveSL 3 K))).comap φ,
      (Subgroup.normalizer ((Q : Subgroup (projectiveSL 3 K)) :
        Set (projectiveSL 3 K))).comap φ⁆ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨U, hU⟩ := exists_sylow_projUnitriangular (K := K) 2 (n := 3) (by norm_num)
  have hNU : Subgroup.normalizer ((U : Subgroup (projectiveSL 3 K)) : Set (projectiveSL 3 K)) =
      projUpperTriangular 3 K := by
    rw [hU]
    exact (sylow_normalizers (K := K) (n := 3) 2 (by norm_num)).2.1
  have hdiag : ∀ d : Fin 3 → K, (∀ i j : Fin 3, j < i → diagonal d i j = 0) :=
    fun d i j hij => diagonal_apply_ne d (ne_of_gt hij)
  refine isPGroup_commutator_of_weyl_data φ hφ hZ hodd U
    (A₁ := ((proj 3 K).comp torOne).range) (A₂ := ((proj 3 K).comp torTwo).range)
    (w := proj 3 K weylL3) ?_ ?_ ?_ ?_ ?_ ?_ ?_ Q
  · intro x hx
    rw [hNU] at hx
    obtain ⟨A, hA, rfl⟩ := Subgroup.mem_map.mp hx
    obtain ⟨u, hu, a, b, rfl⟩ := exists_unitriangular_mul_tor hA
    refine ⟨proj 3 K u, hU ▸ Subgroup.mem_map_of_mem _ hu, proj 3 K (torOne a * torTwo b), ?_,
      map_mul _ _ _⟩
    rw [map_mul]
    exact Subgroup.mul_mem _ (Subgroup.mem_sup_left ⟨a, rfl⟩) (Subgroup.mem_sup_right ⟨b, rfl⟩)
  · rw [hNU]
    refine sup_le ?_ ?_
    · rintro _ ⟨a, rfl⟩
      refine Subgroup.mem_map_of_mem _ (mem_upperTriangular.mpr fun i j hij => ?_)
      rw [coe_torOne]
      exact hdiag _ i j hij
    · rintro _ ⟨b, rfl⟩
      refine Subgroup.mem_map_of_mem _ (mem_upperTriangular.mpr fun i j hij => ?_)
      rw [coe_torTwo]
      exact hdiag _ i j hij
  · exact isCyclic_of_surjective _ ((proj 3 K).comp torOne).rangeRestrict_surjective
  · exact isCyclic_of_surjective _ ((proj 3 K).comp torTwo).rangeRestrict_surjective
  · rintro _ ⟨a, rfl⟩ _ ⟨b, rfl⟩
    simp only [MonoidHom.comp_apply]
    rw [← map_mul, ← map_mul, torOne_mul_torTwo_comm]
  · rintro _ ⟨a, rfl⟩
    simp only [MonoidHom.comp_apply]
    rw [← map_inv, ← map_mul, ← map_mul, weylL3_conj_torOne, map_inv]
  · rintro _ ⟨b, rfl⟩
    simp only [MonoidHom.comp_apply]
    rw [← map_inv, ← map_mul, ← map_mul, weylL3_conj_torTwo]

end CFSG.Quasithin.Vol2.Ch11.SecB.C10KG
