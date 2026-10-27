module

public import CFSG.LinearAlgebra.LinearGroups.Generation
public import CFSG.RankThree.Classical.OrthogonalOrderThree
public import CFSG.LocalAnalysis.SectionRank.OddCover.DegreeThree

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22.L3Lin
open Matrix
open scoped MatrixGroups
variable {F : Type} [Field F]

@[expose] def jSL : SL(2, F) := ⟨!![0, 1; -1, 0], by simp [Matrix.det_fin_two]⟩


theorem sl2_inv_transpose (B : SL(2, F)) : (B⁻¹).transpose = jSL * B * jSL⁻¹ := by
  have hB := B.2
  rw [Matrix.det_fin_two] at hB
  apply Matrix.SpecialLinearGroup.ext
  intro i j
  rw [Matrix.SpecialLinearGroup.coe_transpose, Matrix.SpecialLinearGroup.coe_inv,
    Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul,
    Matrix.SpecialLinearGroup.coe_inv, Matrix.adjugate_fin_two, Matrix.adjugate_fin_two]
  fin_cases i <;> fin_cases j <;> simp [jSL, Matrix.mul_apply, Fin.sum_univ_two, Matrix.vecMul, dotProduct]


end CFSG.LocalAnalysis.UniquenessCase.UC22.L3Lin

namespace CFSG.RankThree.Classical2

open Matrix CFSG.RankThree.Classical CFSG.SectionRank.OddCover
open scoped MatrixGroups commutatorElement

section Basic

variable {K : Type} [Field K] {n : ℕ}

@[expose] def conjSLn (M : GL (Fin n) K) : SL(n, K) →* SL(n, K) where
  toFun A := ⟨(M : Matrix (Fin n) (Fin n) K) * A * (↑M⁻¹ : Matrix (Fin n) (Fin n) K), by
    rw [Matrix.det_mul, Matrix.det_mul, A.2, mul_one, ← Matrix.det_mul, M.mul_inv,
      Matrix.det_one]⟩
  map_one' := Subtype.ext <| by
    change (M : Matrix (Fin n) (Fin n) K) * 1 * (↑M⁻¹ : Matrix (Fin n) (Fin n) K) = 1
    rw [Matrix.mul_one]
    exact M.mul_inv
  map_mul' A B := Subtype.ext <| by
    change (M : Matrix (Fin n) (Fin n) K) * ((A : Matrix (Fin n) (Fin n) K) * B) *
        (↑M⁻¹ : Matrix (Fin n) (Fin n) K) =
      (M : Matrix (Fin n) (Fin n) K) * A * (↑M⁻¹ : Matrix (Fin n) (Fin n) K) *
        ((M : Matrix (Fin n) (Fin n) K) * B * (↑M⁻¹ : Matrix (Fin n) (Fin n) K))
    simp only [Matrix.mul_assoc]
    rw [← Matrix.mul_assoc (↑M⁻¹ : Matrix (Fin n) (Fin n) K) (M : Matrix (Fin n) (Fin n) K),
      M.inv_mul, Matrix.one_mul]

theorem coe_conjSLn (M : GL (Fin n) K) (A : SL(n, K)) :
    ((conjSLn M A : SL(n, K)) : Matrix (Fin n) (Fin n) K) =
      (M : Matrix (Fin n) (Fin n) K) * A * (↑M⁻¹ : Matrix (Fin n) (Fin n) K) :=
  rfl

theorem coe_inv_eq_nonsing_inv (A : SL(n, K)) :
    (↑A⁻¹ : Matrix (Fin n) (Fin n) K) = (A : Matrix (Fin n) (Fin n) K)⁻¹ := by
  refine (Matrix.inv_eq_left_inv ?_).symm
  rw [← Matrix.SpecialLinearGroup.coe_mul, inv_mul_cancel, Matrix.SpecialLinearGroup.coe_one]

@[expose] def invTransposeSL : SL(n, K) →* SL(n, K) where
  toFun A := ⟨(↑A⁻¹ : Matrix (Fin n) (Fin n) K)ᵀ, by
    rw [Matrix.det_transpose, Matrix.SpecialLinearGroup.coe_inv, Matrix.det_adjugate, A.2,
      one_pow]⟩
  map_one' := Subtype.ext (by simp)
  map_mul' A B := Subtype.ext (by
    change (↑(A * B)⁻¹ : Matrix (Fin n) (Fin n) K)ᵀ =
      (↑A⁻¹ : Matrix (Fin n) (Fin n) K)ᵀ * (↑B⁻¹ : Matrix (Fin n) (Fin n) K)ᵀ
    rw [_root_.mul_inv_rev, Matrix.SpecialLinearGroup.coe_mul, Matrix.transpose_mul])

theorem coe_invTransposeSL (A : SL(n, K)) :
    ((invTransposeSL A : SL(n, K)) : Matrix (Fin n) (Fin n) K) =
      (↑A⁻¹ : Matrix (Fin n) (Fin n) K)ᵀ :=
  rfl

theorem invTransposeSL_invTransposeSL (A : SL(n, K)) : invTransposeSL (invTransposeSL A) = A :=
  Subtype.ext (by
    rw [coe_invTransposeSL, ← map_inv, coe_invTransposeSL, inv_inv, Matrix.transpose_transpose])

theorem invTransposeSL_two_eq_conj (B : SL(2, K)) :
    invTransposeSL B = conjSLn (Matrix.SpecialLinearGroup.toGL
      (CFSG.LocalAnalysis.UniquenessCase.UC22.L3Lin.jSL : SL(2, K))) B := by
  change (B⁻¹).transpose = _
  rw [CFSG.LocalAnalysis.UniquenessCase.UC22.L3Lin.sl2_inv_transpose]
  apply Matrix.SpecialLinearGroup.ext
  intro i j
  rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul, coe_conjSLn]
  rfl

variable {i j : Fin n}

theorem transvection_inv' (hij : i ≠ j) (t : K) :
    (SpecialLinearGroup.transvection hij t)⁻¹ = SpecialLinearGroup.transvection hij (-t) := by
  rw [inv_eq_iff_mul_eq_one, ← SpecialLinearGroup.transvection_add, add_neg_cancel,
    SpecialLinearGroup.transvection_coeff_zero]

theorem invTransposeSL_transvection (hij : i ≠ j) (s : K) :
    invTransposeSL (SpecialLinearGroup.transvection hij.symm s) =
      SpecialLinearGroup.transvection hij (-s) := by
  apply Subtype.ext
  rw [coe_invTransposeSL, transvection_inv', SpecialLinearGroup.transvection_coe,
    SpecialLinearGroup.transvection_coe, Matrix.transpose_add, Matrix.transpose_one,
    Matrix.transpose_single]

theorem permGL_inv_mul_single_mul (π : Equiv.Perm (Fin n)) (i j : Fin n) (c : K) :
    (↑(permGL π : GL (Fin n) K)⁻¹ : Matrix (Fin n) (Fin n) K) * single (π i) (π j) c *
      ((permGL π : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) = single i j c := by
  rw [← map_inv, MonoidHom.coe_toHomUnits, MonoidHom.coe_toHomUnits, Matrix.permMatrixHom_apply,
    Matrix.permMatrixHom_apply, inv_inv, Equiv.Perm.permMatrix, Equiv.Perm.permMatrix,
    PEquiv.toMatrix_toPEquiv_mul, PEquiv.mul_toMatrix_toPEquiv, Matrix.submatrix_submatrix]
  change (single (π i) (π j) c).submatrix (⇑π ∘ id) (id ∘ ⇑(π⁻¹).symm) = single i j c
  have : (π⁻¹).symm = π := by
    rw [Equiv.Perm.inv_def, Equiv.symm_symm]
  rw [this, Function.comp_id, Function.id_comp, Matrix.submatrix_single_equiv,
    Equiv.symm_apply_apply, Equiv.symm_apply_apply]

theorem diagHom_mul_one_add_single_mul (d : Fin n → Kˣ) (hij : i ≠ j) (s : K) :
    (diagHom n d : Matrix (Fin n) (Fin n) K) * (1 + single i j s) *
        (↑(diagHom n d)⁻¹ : Matrix (Fin n) (Fin n) K) =
      1 + single i j ((d i : K) * s * ((d j)⁻¹ : Kˣ)) := by
  rw [← map_inv, coe_diagHom, coe_diagHom]
  ext a b
  rw [Matrix.mul_diagonal, Matrix.diagonal_mul]
  simp only [Matrix.add_apply, Matrix.one_apply, Matrix.single_apply, Pi.inv_apply]
  by_cases hab : a = b
  · subst hab
    have hai : ¬ (i = a ∧ j = a) := fun h => hij (h.1.trans h.2.symm)
    simp only [ite_true, hai, ite_false, add_zero, mul_one]
    rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
  · simp only [hab, ite_false, zero_add]
    split_ifs with h
    · obtain ⟨rfl, rfl⟩ := h
      rfl
    · simp

theorem conj_diagHom_transvection (d : Fin n → Kˣ) (hij : i ≠ j) (t : K) :
    conjSLn (diagHom n d) (SpecialLinearGroup.transvection hij t) =
      SpecialLinearGroup.transvection hij ((d i : K) * t * ((d j)⁻¹ : Kˣ)) := by
  apply Subtype.ext
  rw [coe_conjSLn]
  exact diagHom_mul_one_add_single_mul d hij t

theorem weyl_mul_transvection (hij : i ≠ j) :
    SpecialLinearGroup.transvection hij (1 : K) * SpecialLinearGroup.transvection hij.symm (-1) *
        SpecialLinearGroup.transvection hij 1 * SpecialLinearGroup.transvection hij 1 =
      SpecialLinearGroup.transvection hij.symm (-1) * (SpecialLinearGroup.transvection hij 1 *
        SpecialLinearGroup.transvection hij.symm (-1) * SpecialLinearGroup.transvection hij 1) := by
  apply Subtype.ext
  simp only [Matrix.SpecialLinearGroup.coe_mul, SpecialLinearGroup.transvection_coe]
  have hE : ∀ (a b : Fin n) (c : K), single a b c = c • single a b (1 : K) := fun a b c => by
    rw [Matrix.smul_single, smul_eq_mul, mul_one]
  rw [hE i j 1, hE j i (-1)]
  simp only [Matrix.add_mul, Matrix.mul_add, Matrix.one_mul, Matrix.smul_mul,
    Matrix.mul_smul, Matrix.single_mul_single_same,
    Matrix.single_mul_single_of_ne _ _ _ _ hij, Matrix.single_mul_single_of_ne _ _ _ _ hij.symm,
    smul_zero, add_zero, mul_one]
  module

theorem transvection_weyl_apply_self (hij : i ≠ j) (a b : K) :
    ((SpecialLinearGroup.transvection hij a * SpecialLinearGroup.transvection hij.symm (-b) *
        SpecialLinearGroup.transvection hij a : SL(n, K)) : Matrix (Fin n) (Fin n) K) i i =
      1 - a * b := by
  simp only [Matrix.SpecialLinearGroup.coe_mul, SpecialLinearGroup.transvection_coe]
  have hE : ∀ (a b : Fin n) (c : K), single a b c = c • single a b (1 : K) := fun a b c => by
    rw [Matrix.smul_single, smul_eq_mul, mul_one]
  rw [hE i j a, hE j i (-b)]
  simp only [Matrix.add_mul, Matrix.mul_add, Matrix.one_mul, Matrix.smul_mul,
    Matrix.mul_smul, Matrix.single_mul_single_same,
    Matrix.single_mul_single_of_ne _ _ _ _ hij.symm, smul_zero, add_zero, mul_one]
  simp only [Matrix.add_apply, Matrix.smul_apply, Matrix.one_apply_eq, Matrix.single_apply,
    hij.symm, and_self, and_false, false_and, ite_true, ite_false, smul_eq_mul, mul_zero,
    add_zero, zero_add, mul_one]
  ring

end Basic

section RootHom

variable {K : Type} [Field K] {n : ℕ}

theorem exists_diag_eq_conj_map_of_root_hom (hn : 3 ≤ n) (φ : K →+* K)
    (Ψ : SL(n, K) →* SL(n, K)) (c : Fin n → Fin n → Kˣ)
    (hΨ : ∀ (i j : Fin n) (hij : i ≠ j) (t : K),
      Ψ (SpecialLinearGroup.transvection hij t) =
        SpecialLinearGroup.transvection hij ((c i j : K) * φ t)) :
    ∃ d : Fin n → Kˣ, ∀ X : SL(n, K), (Ψ X : Matrix (Fin n) (Fin n) K) =
      (diagHom n d : Matrix (Fin n) (Fin n) K) * (X : Matrix (Fin n) (Fin n) K).map φ *
        (↑(diagHom n d)⁻¹ : Matrix (Fin n) (Fin n) K) := by
  classical
  have hrec : ∀ i j : Fin n, i ≠ j → (c i j : K) * c j i = 1 := by
    intro i j hij
    have h := congrArg Ψ (weyl_mul_transvection (K := K) hij)
    simp only [map_mul, hΨ, map_one, map_neg, mul_one, mul_neg] at h
    set X := SpecialLinearGroup.transvection hij (c i j : K) *
      SpecialLinearGroup.transvection hij.symm (-(c j i : K)) *
        SpecialLinearGroup.transvection hij (c i j : K) with hXdef
    have h1 := congrArg (fun Y : SL(n, K) => (Y : Matrix (Fin n) (Fin n) K) i j) h
    simp only [Matrix.SpecialLinearGroup.coe_mul] at h1
    rw [SpecialLinearGroup.transvection_coe, SpecialLinearGroup.transvection_coe, Matrix.mul_add,
      Matrix.mul_one, Matrix.add_mul, Matrix.one_mul, Matrix.add_apply, Matrix.add_apply,
      Matrix.mul_single_apply_same, Matrix.single_mul_apply_of_ne _ _ _ _ _ hij] at h1
    have h2 : (X : Matrix (Fin n) (Fin n) K) i i * (c i j : K) = 0 := by
      simp only [add_zero] at h1
      linear_combination h1
    have h3 := (mul_eq_zero.mp h2).resolve_right (c i j).ne_zero
    rw [hXdef, transvection_weyl_apply_self hij] at h3
    linear_combination -h3
  have hmul : ∀ i j l : Fin n, i ≠ j → j ≠ l → i ≠ l → (c i l : K) = c i j * c j l := by
    intro i j l hij hjl hil
    have h := congrArg Ψ (Matrix.SpecialLinearGroup.commutatorElement_transvection hij hjl hil
      (1 : K) 1)
    rw [map_commutatorElement, hΨ, hΨ, hΨ,
      Matrix.SpecialLinearGroup.commutatorElement_transvection hij hjl hil] at h
    simp only [map_one, mul_one] at h
    exact (Matrix.SpecialLinearGroup.transvection_injective hil h).symm
  set last : Fin n := ⟨n - 1, by omega⟩ with hlast
  set d : Fin n → Kˣ := fun i => if i = last then 1 else c i last with hddef
  have hcd : ∀ i j : Fin n, i ≠ j → (c i j : K) = (d i : K) * ((d j)⁻¹ : Kˣ) := by
    intro i j hij
    have hinv : ∀ a b : Fin n, a ≠ b → (c b a : K) = ((c a b)⁻¹ : Kˣ) := fun a b hab => by
      simp only [Units.val_inv_eq_inv_val]
      exact eq_inv_of_mul_eq_one_left (by rw [mul_comm]; exact hrec a b hab)
    by_cases hi : i = last
    · subst hi
      have hj : j ≠ last := fun h => hij h.symm
      simp only [hddef, ite_true, hj, ite_false, Units.val_one, one_mul]
      exact hinv j last hj
    by_cases hj : j = last
    · subst hj
      simp only [hddef, hi, ite_false, ite_true, inv_one, Units.val_one, mul_one]
    simp only [hddef, hi, hj, ite_false]
    rw [hmul i last j hi (Ne.symm hj) hij, hinv j last hj]
  let Θ : SL(n, K) →* SL(n, K) := (conjSLn (diagHom n d)).comp (SpecialLinearGroup.map φ)
  have hΘ : Ψ = Θ := by
    refine MonoidHom.eq_of_eqOn_dense CFSG.LinearGroups.special_linear_elementary_generation ?_
    rintro _ ⟨i, j, hij, t, rfl⟩
    apply Subtype.ext
    change ((Ψ (SpecialLinearGroup.transvection hij t) : SL(n, K)) : Matrix (Fin n) (Fin n) K) =
      (diagHom n d : Matrix (Fin n) (Fin n) K) *
        ((SpecialLinearGroup.map φ (SpecialLinearGroup.transvection hij t) : SL(n, K)) :
          Matrix (Fin n) (Fin n) K) * (↑(diagHom n d)⁻¹ : Matrix (Fin n) (Fin n) K)
    rw [hΨ, Matrix.SpecialLinearGroup.map_transvection, SpecialLinearGroup.transvection_coe,
      SpecialLinearGroup.transvection_coe, diagHom_mul_one_add_single_mul d hij, hcd i j hij]
    congr 2
    ring
  refine ⟨d, fun X => ?_⟩
  rw [hΘ]
  change (diagHom n d : Matrix (Fin n) (Fin n) K) *
      ((SpecialLinearGroup.map φ X : SL(n, K)) : Matrix (Fin n) (Fin n) K) *
        (↑(diagHom n d)⁻¹ : Matrix (Fin n) (Fin n) K) = _
  rw [Matrix.SpecialLinearGroup.map_apply_coe, RingHom.mapMatrix_apply]

end RootHom

section RootPermuting

variable {K : Type} [Field K] {n : ℕ}

theorem exists_conj_map_of_root_permuting (hn : 3 ≤ n) (φ : K →+* K) (π : Equiv.Perm (Fin n))
    (Φ : SL(n, K) →* SL(n, K)) (b : Fin n → Fin n → Kˣ)
    (hΦ : ∀ (i j : Fin n) (hij : i ≠ j) (t : K),
      ((Φ (SpecialLinearGroup.transvection hij t) : SL(n, K)) : Matrix (Fin n) (Fin n) K) =
        1 + single (π i) (π j) ((b i j : K) * φ t)) :
    ∃ A : GL (Fin n) K, ∀ X : SL(n, K), ((Φ X : SL(n, K)) : Matrix (Fin n) (Fin n) K) =
      (A : Matrix (Fin n) (Fin n) K) * (X : Matrix (Fin n) (Fin n) K).map φ *
        (↑A⁻¹ : Matrix (Fin n) (Fin n) K) := by
  set P : GL (Fin n) K := permGL π with hPdef
  set Ψ : SL(n, K) →* SL(n, K) := (conjSLn P⁻¹).comp Φ with hΨdef
  have hΨ : ∀ (i j : Fin n) (hij : i ≠ j) (t : K), Ψ (SpecialLinearGroup.transvection hij t) =
      SpecialLinearGroup.transvection hij ((b i j : K) * φ t) := by
    intro i j hij t
    apply Subtype.ext
    change (↑P⁻¹ : Matrix (Fin n) (Fin n) K) *
        ((Φ (SpecialLinearGroup.transvection hij t) : SL(n, K)) : Matrix (Fin n) (Fin n) K) *
          (↑P⁻¹⁻¹ : Matrix (Fin n) (Fin n) K) = _
    rw [inv_inv, hΦ, SpecialLinearGroup.transvection_coe, Matrix.mul_add, Matrix.add_mul,
      Matrix.mul_one, P.inv_mul, hPdef, permGL_inv_mul_single_mul]
  obtain ⟨d, hd⟩ := exists_diag_eq_conj_map_of_root_hom hn φ Ψ b hΨ
  refine ⟨P * diagHom n d, fun X => ?_⟩
  have h1 : ((Φ X : SL(n, K)) : Matrix (Fin n) (Fin n) K) =
      (P : Matrix (Fin n) (Fin n) K) * ((Ψ X : SL(n, K)) : Matrix (Fin n) (Fin n) K) *
        (↑P⁻¹ : Matrix (Fin n) (Fin n) K) := by
    change _ = (P : Matrix (Fin n) (Fin n) K) * ((↑P⁻¹ : Matrix (Fin n) (Fin n) K) *
      ((Φ X : SL(n, K)) : Matrix (Fin n) (Fin n) K) * (↑P⁻¹⁻¹ : Matrix (Fin n) (Fin n) K)) *
        (↑P⁻¹ : Matrix (Fin n) (Fin n) K)
    rw [inv_inv]
    simp only [Matrix.mul_assoc]
    rw [P.mul_inv, Matrix.mul_one, ← Matrix.mul_assoc, P.mul_inv, Matrix.one_mul]
  rw [h1, hd, _root_.mul_inv_rev, Units.val_mul, Units.val_mul]
  simp only [Matrix.mul_assoc]

theorem exists_conj_map_inv_transpose_of_root_permuting (hn : 3 ≤ n) (φ : K →+* K)
    (π : Equiv.Perm (Fin n)) (Φ : SL(n, K) →* SL(n, K)) (b : Fin n → Fin n → Kˣ)
    (hΦ : ∀ (i j : Fin n) (hij : i ≠ j) (t : K),
      ((Φ (SpecialLinearGroup.transvection hij t) : SL(n, K)) : Matrix (Fin n) (Fin n) K) =
        1 + single (π j) (π i) ((b i j : K) * φ t)) :
    ∃ A : GL (Fin n) K, ∀ X : SL(n, K), ((Φ X : SL(n, K)) : Matrix (Fin n) (Fin n) K) =
      (A : Matrix (Fin n) (Fin n) K) * (((X : Matrix (Fin n) (Fin n) K).map φ)⁻¹)ᵀ *
        (↑A⁻¹ : Matrix (Fin n) (Fin n) K) := by
  set P : GL (Fin n) K := permGL π with hPdef
  set Φ' : SL(n, K) →* SL(n, K) := (conjSLn P⁻¹).comp Φ with hΦ'def
  set Ψ : SL(n, K) →* SL(n, K) := invTransposeSL.comp Φ' with hΨdef
  have hΦ' : ∀ (i j : Fin n) (hij : i ≠ j) (t : K), Φ' (SpecialLinearGroup.transvection hij t) =
      SpecialLinearGroup.transvection hij.symm ((b i j : K) * φ t) := by
    intro i j hij t
    apply Subtype.ext
    change (↑P⁻¹ : Matrix (Fin n) (Fin n) K) *
        ((Φ (SpecialLinearGroup.transvection hij t) : SL(n, K)) : Matrix (Fin n) (Fin n) K) *
          (↑P⁻¹⁻¹ : Matrix (Fin n) (Fin n) K) = _
    rw [inv_inv, hΦ, SpecialLinearGroup.transvection_coe, Matrix.mul_add, Matrix.add_mul,
      Matrix.mul_one, P.inv_mul, hPdef, permGL_inv_mul_single_mul]
  have hΨ : ∀ (i j : Fin n) (hij : i ≠ j) (t : K), Ψ (SpecialLinearGroup.transvection hij t) =
      SpecialLinearGroup.transvection hij (((-b i j : Kˣ) : K) * φ t) := by
    intro i j hij t
    change invTransposeSL (Φ' (SpecialLinearGroup.transvection hij t)) = _
    rw [hΦ', invTransposeSL_transvection, Units.val_neg, neg_mul]
  obtain ⟨d, hd⟩ := exists_diag_eq_conj_map_of_root_hom hn φ Ψ (fun i j => -b i j) hΨ
  refine ⟨P * (diagHom n d)⁻¹, fun X => ?_⟩
  have hΦ'X : Φ' X = invTransposeSL (Ψ X) := by
    change Φ' X = invTransposeSL (invTransposeSL (Φ' X))
    rw [invTransposeSL_invTransposeSL]
  have h1 : ((Φ X : SL(n, K)) : Matrix (Fin n) (Fin n) K) =
      (P : Matrix (Fin n) (Fin n) K) * ((Φ' X : SL(n, K)) : Matrix (Fin n) (Fin n) K) *
        (↑P⁻¹ : Matrix (Fin n) (Fin n) K) := by
    change _ = (P : Matrix (Fin n) (Fin n) K) * ((↑P⁻¹ : Matrix (Fin n) (Fin n) K) *
      ((Φ X : SL(n, K)) : Matrix (Fin n) (Fin n) K) * (↑P⁻¹⁻¹ : Matrix (Fin n) (Fin n) K)) *
        (↑P⁻¹ : Matrix (Fin n) (Fin n) K)
    rw [inv_inv]
    simp only [Matrix.mul_assoc]
    rw [P.mul_inv, Matrix.mul_one, ← Matrix.mul_assoc, P.mul_inv, Matrix.one_mul]
  have hdiagT : ∀ e : Fin n → Kˣ, (diagHom n e : Matrix (Fin n) (Fin n) K)ᵀ = diagHom n e :=
    fun e => by rw [coe_diagHom, Matrix.diagonal_transpose]
  have hDunit : IsUnit (diagHom n d : Matrix (Fin n) (Fin n) K).det :=
    (Matrix.isUnit_iff_isUnit_det _).mp (Units.isUnit _)
  have hDinv : (diagHom n d : Matrix (Fin n) (Fin n) K)⁻¹ =
      (↑(diagHom n d)⁻¹ : Matrix (Fin n) (Fin n) K) := (Matrix.coe_units_inv _).symm
  have h2 : ((invTransposeSL (Ψ X) : SL(n, K)) : Matrix (Fin n) (Fin n) K) =
      (↑(diagHom n d)⁻¹ : Matrix (Fin n) (Fin n) K) *
        (((X : Matrix (Fin n) (Fin n) K).map φ)⁻¹)ᵀ * (diagHom n d : Matrix (Fin n) (Fin n) K) := by
    rw [coe_invTransposeSL, coe_inv_eq_nonsing_inv, hd, Matrix.mul_inv_rev, Matrix.mul_inv_rev,
      ← hDinv, Matrix.nonsing_inv_nonsing_inv _ hDunit, Matrix.transpose_mul,
      Matrix.transpose_mul, hDinv, ← map_inv, hdiagT, hdiagT, Matrix.mul_assoc]
  rw [h1, hΦ'X, h2, _root_.mul_inv_rev, inv_inv, Units.val_mul, Units.val_mul]
  simp only [Matrix.mul_assoc]

theorem exists_diag_conj_map_inv_transpose_of_root_hom (hn : 3 ≤ n) (φ : K →+* K)
    (Φ : SL(n, K) →* SL(n, K)) (b : Fin n → Fin n → Kˣ)
    (hΦ : ∀ (i j : Fin n) (hij : i ≠ j) (t : K),
      ((Φ (SpecialLinearGroup.transvection hij t) : SL(n, K)) : Matrix (Fin n) (Fin n) K) =
        1 + single j i ((b i j : K) * φ t)) :
    ∃ d : Fin n → Kˣ, ∀ X : SL(n, K),
      ((Φ X : SL(n, K)) : Matrix (Fin n) (Fin n) K) =
        (diagHom n d : Matrix (Fin n) (Fin n) K) *
          (((X : Matrix (Fin n) (Fin n) K).map φ)⁻¹)ᵀ *
          (↑(diagHom n d)⁻¹ : Matrix (Fin n) (Fin n) K) := by
  set Ψ : SL(n, K) →* SL(n, K) := invTransposeSL.comp Φ with hΨdef
  have hΨ : ∀ (i j : Fin n) (hij : i ≠ j) (t : K),
      Ψ (SpecialLinearGroup.transvection hij t) =
        SpecialLinearGroup.transvection hij (((-b i j : Kˣ) : K) * φ t) := by
    intro i j hij t
    have htr : Φ (SpecialLinearGroup.transvection hij t) =
        SpecialLinearGroup.transvection hij.symm ((b i j : K) * φ t) := by
      apply Subtype.ext
      rw [hΦ]
      rfl
    change invTransposeSL (Φ (SpecialLinearGroup.transvection hij t)) = _
    rw [htr]
    simpa only [Units.val_neg, neg_mul] using
      invTransposeSL_transvection hij ((b i j : K) * φ t)
  obtain ⟨d, hd⟩ := exists_diag_eq_conj_map_of_root_hom hn φ Ψ (fun i j => -b i j) hΨ
  refine ⟨d⁻¹, fun X => ?_⟩
  have hΦX : Φ X = invTransposeSL (Ψ X) := by
    change Φ X = invTransposeSL (invTransposeSL (Φ X))
    rw [invTransposeSL_invTransposeSL]
  have hdiagT : ∀ e : Fin n → Kˣ, (diagHom n e : Matrix (Fin n) (Fin n) K)ᵀ = diagHom n e :=
    fun e => by rw [coe_diagHom, Matrix.diagonal_transpose]
  have hDunit : IsUnit (diagHom n d : Matrix (Fin n) (Fin n) K).det :=
    (Matrix.isUnit_iff_isUnit_det _).mp (Units.isUnit _)
  have hDinv : (diagHom n d : Matrix (Fin n) (Fin n) K)⁻¹ =
      (↑(diagHom n d)⁻¹ : Matrix (Fin n) (Fin n) K) := (Matrix.coe_units_inv _).symm
  have h2 : ((invTransposeSL (Ψ X) : SL(n, K)) : Matrix (Fin n) (Fin n) K) =
      (↑(diagHom n d)⁻¹ : Matrix (Fin n) (Fin n) K) *
        (((X : Matrix (Fin n) (Fin n) K).map φ)⁻¹)ᵀ *
        (diagHom n d : Matrix (Fin n) (Fin n) K) := by
    rw [coe_invTransposeSL, coe_inv_eq_nonsing_inv, hd, Matrix.mul_inv_rev, Matrix.mul_inv_rev,
      ← hDinv, Matrix.nonsing_inv_nonsing_inv _ hDunit, Matrix.transpose_mul,
      Matrix.transpose_mul, hDinv, ← map_inv, hdiagT, hdiagT, Matrix.mul_assoc]
  have hD' : (diagHom (K := K) n) d⁻¹ = (diagHom (K := K) n d)⁻¹ := map_inv _ d
  rw [hΦX, h2, hD', inv_inv]

end RootPermuting

end CFSG.RankThree.Classical2
