module

public import CFSG.Adapters.ProjectiveSpecialLinear

public section

namespace CFSG.Quasithin.H13.Ch4.CentK

open CFSG.Assembly.LowTwoRank Matrix

private theorem symm_mem_center_three {F : Type} [Field F] {z : ↥(StatedSL 3 F)}
    (hz : z ∈ Subgroup.center ↥(StatedSL 3 F)) :
    (specialLinearGroupEquivStatedSL 3 F).symm z ∈
      Subgroup.center (Matrix.SpecialLinearGroup (Fin 3) F) := by
  rw [Subgroup.mem_center_iff] at hz ⊢
  intro B
  apply (specialLinearGroupEquivStatedSL 3 F).injective
  rw [map_mul, map_mul, MulEquiv.apply_symm_apply]
  exact hz _

private theorem not_isRoot_X_pow_three_sub_C_of_card_four {F : Type} [Field F] [Fintype F]
    (hF : Fintype.card F = 4) {r : F} (hr0 : r ≠ 0) (hr1 : r ≠ 1) (x : F) :
    ¬ (Polynomial.X ^ 3 - Polynomial.C r : Polynomial F).IsRoot x := by
  intro h
  rw [Polynomial.IsRoot.def, Polynomial.eval_sub, Polynomial.eval_pow, Polynomial.eval_X,
    Polynomial.eval_C, sub_eq_zero] at h
  by_cases hx : x = 0
  · rw [hx, zero_pow (by norm_num)] at h
    exact hr0 h.symm
  · have h1 : x ^ 3 = 1 := by
      have := FiniteField.pow_card_sub_one_eq_one x hx
      rw [hF] at this
      simpa using this
    exact hr1 (h.symm.trans h1)

private theorem det_eq_of_pow_three_eq_scalar {F : Type} [Field F]
    {M : Matrix (Fin 3) (Fin 3) F} {r : F} (hM : M ^ 3 = Matrix.scalar (Fin 3) r)
    (hnot : ∀ x : F, ¬ (Polynomial.X ^ 3 - Polynomial.C r : Polynomial F).IsRoot x) :
    M.det = r := by
  have hmonic : (Polynomial.X ^ 3 - Polynomial.C r : Polynomial F).Monic :=
    Polynomial.monic_X_pow_sub_C r (by norm_num)
  have hdeg : (Polynomial.X ^ 3 - Polynomial.C r : Polynomial F).natDegree = 3 :=
    Polynomial.natDegree_X_pow_sub_C
  have hirr : Irreducible (Polynomial.X ^ 3 - Polynomial.C r : Polynomial F) :=
    Polynomial.irreducible_of_degree_le_three_of_not_isRoot (by rw [hdeg]; simp) hnot
  have halg : algebraMap F (Matrix (Fin 3) (Fin 3) F) r = Matrix.scalar (Fin 3) r := by
    rw [Matrix.algebraMap_eq_diagonal, Matrix.scalar_apply]
    rfl
  have hp_eval : Polynomial.aeval M (Polynomial.X ^ 3 - Polynomial.C r : Polynomial F) = 0 := by
    rw [map_sub, map_pow, Polynomial.aeval_X, Polynomial.aeval_C, hM, halg, sub_self]
  rcases hirr.isCoprime_or_dvd M.charpoly with hcop | hdvd
  · exfalso
    obtain ⟨a, b, hab⟩ := hcop
    have h1 := congrArg (Polynomial.aeval M) hab
    rw [map_add, map_mul, map_mul, hp_eval, Matrix.aeval_self_charpoly, map_one, mul_zero,
      mul_zero, add_zero] at h1
    exact zero_ne_one h1
  · have hchi : M.charpoly = Polynomial.X ^ 3 - Polynomial.C r :=
      Polynomial.eq_of_monic_of_dvd_of_natDegree_le hmonic (Matrix.charpoly_monic M) hdvd
        (le_of_eq (by rw [Matrix.charpoly_natDegree_eq_dim, hdeg, Fintype.card_fin]))
    rw [Matrix.det_eq_sign_charpoly_coeff, hchi, Fintype.card_fin]
    norm_num [Polynomial.coeff_sub, Polynomial.coeff_X_pow, Polynomial.coeff_C]

private theorem eq_one_of_pow_three_eq_scalar_card_four {F : Type} [Field F] [Fintype F]
    (hF : Fintype.card F = 4) {M : Matrix (Fin 3) (Fin 3) F} {r : F}
    (hM : M ^ 3 = Matrix.scalar (Fin 3) r) (hdet : M.det = 1) (hr3 : r ^ 3 = 1) : r = 1 := by
  by_contra hne
  have hr0 : r ≠ 0 := by
    rintro rfl
    norm_num at hr3
  have hdetr := det_eq_of_pow_three_eq_scalar hM
    (not_isRoot_X_pow_three_sub_C_of_card_four hF hr0 hne)
  exact hne (hdetr.symm.trans hdet)

theorem pow_three_eq_one_of_mem_center {F : Type} [Field F] {z : ↥(StatedSL 3 F)}
    (hz : z ∈ Subgroup.center ↥(StatedSL 3 F)) : z ^ 3 = 1 := by
  obtain ⟨r, hr, hscalar⟩ := Matrix.SpecialLinearGroup.mem_center_iff.mp
    (symm_mem_center_three hz)
  have hr3 : r ^ 3 = 1 := by simpa using hr
  have hB3 : (specialLinearGroupEquivStatedSL 3 F).symm z ^ 3 = 1 := by
    apply Subtype.ext
    rw [Matrix.SpecialLinearGroup.coe_pow, ← hscalar, ← map_pow, hr3, map_one]
    rfl
  have h := congrArg (specialLinearGroupEquivStatedSL 3 F) hB3
  rwa [map_pow, MulEquiv.apply_symm_apply, map_one] at h

theorem pow_three_eq_one_of_pow_three_mem_center {F : Type} [Field F] [Fintype F]
    (hF : Fintype.card F = 4) {g : ↥(StatedSL 3 F)}
    (hg : g ^ 3 ∈ Subgroup.center ↥(StatedSL 3 F)) : g ^ 3 = 1 := by
  obtain ⟨B, hBdef⟩ : ∃ B : Matrix.SpecialLinearGroup (Fin 3) F,
      B = (specialLinearGroupEquivStatedSL 3 F).symm g := ⟨_, rfl⟩
  have hgB : g = specialLinearGroupEquivStatedSL 3 F B := by
    rw [hBdef, MulEquiv.apply_symm_apply]
  have hB3 : B ^ 3 ∈ Subgroup.center (Matrix.SpecialLinearGroup (Fin 3) F) := by
    rw [hBdef, ← map_pow]
    exact symm_mem_center_three hg
  obtain ⟨r, hr, hscalar⟩ := Matrix.SpecialLinearGroup.mem_center_iff.mp hB3
  have hr3 : r ^ 3 = 1 := by simpa using hr
  have hM : (B : Matrix (Fin 3) (Fin 3) F) ^ 3 = Matrix.scalar (Fin 3) r := by
    rw [← Matrix.SpecialLinearGroup.coe_pow]
    exact hscalar.symm
  have hr1 : r = 1 :=
    eq_one_of_pow_three_eq_scalar_card_four hF hM (Matrix.SpecialLinearGroup.det_coe B) hr3
  have hmat : ((B ^ 3 : Matrix.SpecialLinearGroup (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) = 1 := by
    rw [← hscalar, hr1, map_one]
  have hB3one : B ^ 3 = 1 := Subtype.ext hmat
  rw [hgB, ← map_pow, hB3one, map_one]

end CFSG.Quasithin.H13.Ch4.CentK
