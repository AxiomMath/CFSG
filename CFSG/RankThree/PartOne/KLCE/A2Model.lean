module

public import CFSG.RankThree.PartOne.KE.A2Family
public import CFSG.RankThree.PartOne.KLCE.TypeSU
public import CFSG.RankThree.PartOne.KLCE.Frob

public noncomputable section

namespace CFSG.RankThree.PartOne.KLCE

open Matrix CFSG.RankThree.PartOne.KE CFSG.RankThree.Classical2 CFSG.Assembly.LowTwoRank
open scoped MatrixGroups

section Basic

variable {L : Type} [Field L]

theorem single_offdiag (A : Matrix (Fin 3) (Fin 3) L) {i j : Fin 3} {b : L}
    (h : A * Matrix.single i j (1 : L) = Matrix.single i j b * A) :
    (∀ a, a ≠ i → A a i = 0) ∧ A i i = b * A j j := by
  have h1 : ∀ a, A a i = (Matrix.single i j b * A) a j := fun a => by
    have := congrFun (congrFun h a) j
    simpa [Matrix.mul_apply, Matrix.single_apply] using this
  refine ⟨fun a ha => ?_, ?_⟩
  · rw [h1 a]
    simp [Matrix.mul_apply, Ne.symm ha]
  · rw [h1 i]
    simp [Matrix.mul_apply, Matrix.single_apply]

theorem map_one_add_single {q : ℕ} (hq : q ≠ 0) {i j : Fin 3} (hij : i ≠ j) :
    ((1 : Matrix (Fin 3) (Fin 3) L) + Matrix.single i j (1 : L)).map (· ^ q) =
      1 + Matrix.single i j (1 : L) := by
  ext a b
  simp only [Matrix.map_apply, Matrix.add_apply, Matrix.one_apply, Matrix.single_apply]
  by_cases hab : a = b
  · subst hab
    have : ¬ (i = a ∧ j = a) := fun ⟨h1, h2⟩ => hij (h1.trans h2.symm)
    simp [this]
  · by_cases h : i = a ∧ j = b
    · simp [h, hab]
    · simp [h, hab, hq]

theorem mul_single_of_conj {M N : Matrix (Fin 3) (Fin 3) L} (hMN : N * M = 1) {i j : Fin 3} {b : L}
    (h : M * (1 + Matrix.single i j (1 : L)) * N = 1 + Matrix.single i j b) :
    M * Matrix.single i j (1 : L) = Matrix.single i j b * M := by
  have h1 : M * (1 + Matrix.single i j (1 : L)) = (1 + Matrix.single i j b) * M := by
    calc M * (1 + Matrix.single i j (1 : L)) = M * (1 + Matrix.single i j (1 : L)) * (N * M) := by
          rw [hMN, mul_one]
      _ = (M * (1 + Matrix.single i j (1 : L)) * N) * M := by simp only [mul_assoc]
      _ = (1 + Matrix.single i j b) * M := by rw [h]
  rw [mul_add, add_mul, mul_one, one_mul] at h1
  exact add_left_cancel h1

theorem fin3_exists_ne (i : Fin 3) : ∃ j : Fin 3, j ≠ i := ⟨i + 1, by revert i; decide⟩

theorem diag_of_shape_split {q : ℕ} (hq : q ≠ 0) (Θ : SL(3, L) ≃* SL(3, L)) (A : GL (Fin 3) L)
    (hA : ∀ X : SL(3, L), ((Θ X : SL(3, L)) : Matrix (Fin 3) (Fin 3) L) =
      (A : Matrix (Fin 3) (Fin 3) L) * (X : Matrix (Fin 3) (Fin 3) L).map (· ^ q) *
        (↑A⁻¹ : Matrix (Fin 3) (Fin 3) L))
    (b : Fin 3 → Fin 3 → Lˣ)
    (hshape : ∀ (i j : Fin 3) (hij : i ≠ j) (t : L),
      ((Θ (SpecialLinearGroup.transvection hij t) : SL(3, L)) : Matrix (Fin 3) (Fin 3) L) =
        1 + single i j ((b i j : L) * t ^ q)) :
    ∃ a : Fin 3 → Lˣ, (A : Matrix (Fin 3) (Fin 3) L) = Matrix.diagonal (fun i => (a i : L)) ∧
      ∀ i j, i ≠ j → (b i j : L) = (a i : L) * ((a j)⁻¹ : Lˣ) := by
  set M : Matrix (Fin 3) (Fin 3) L := (A : Matrix (Fin 3) (Fin 3) L) with hM
  have hMN : (↑A⁻¹ : Matrix (Fin 3) (Fin 3) L) * M = 1 := by
    rw [hM, ← Units.val_mul, inv_mul_cancel, Units.val_one]
  have hrel : ∀ i j, i ≠ j → M * single i j (1 : L) = single i j (b i j : L) * M := by
    intro i j hij
    refine mul_single_of_conj hMN ?_
    have h1 := hA (SpecialLinearGroup.transvection hij 1)
    rw [hshape i j hij 1, CFSG.LinearGroups.coe_transvection, map_one_add_single hq hij,
      one_pow, mul_one] at h1
    exact h1.symm
  have hoff : ∀ i a, a ≠ i → M a i = 0 := by
    intro i a ha
    obtain ⟨j, hj⟩ := fin3_exists_ne i
    exact (single_offdiag M (hrel i j hj.symm)).1 a ha
  have hdiag : M = Matrix.diagonal fun i => M i i := by
    ext a i
    by_cases h : a = i
    · subst h
      simp
    · simp [Matrix.diagonal_apply_ne _ h, hoff i a h]
  have hdet : IsUnit M.det := (Matrix.isUnit_iff_isUnit_det M).1 (Units.isUnit A)
  have hne : ∀ i, M i i ≠ 0 := by
    have h1 : ∏ i, M i i ≠ 0 := by
      have := hdet.ne_zero
      rwa [hdiag, Matrix.det_diagonal] at this
    exact fun i => (Finset.prod_ne_zero_iff.1 h1) i (Finset.mem_univ i)
  refine ⟨fun i => Units.mk0 (M i i) (hne i), hdiag, fun i j hij => ?_⟩
  have h2 := (single_offdiag M (hrel i j hij)).2
  simp only [Units.val_mk0, Units.val_inv_eq_inv_val]
  have := hne j
  field_simp
  exact h2.symm

theorem exists_diag_lang {q : ℕ} [IsAlgClosed L] (hq : 2 ≤ q) (a : Fin 3 → Lˣ) :
    ∃ h : Fin 3 → Lˣ, ∀ i, (h i : L) ^ q = (a i : L) * (h i : L) := by
  have hn : 0 < q - 1 := by omega
  choose x hx using fun i => IsAlgClosed.exists_pow_nat_eq (a i : L) hn
  have hx0 : ∀ i, x i ≠ 0 := fun i h0 => by
    have := hx i
    rw [h0, zero_pow hn.ne'] at this
    exact (a i).ne_zero this.symm
  refine ⟨fun i => Units.mk0 (x i) (hx0 i), fun i => ?_⟩
  simp only [Units.val_mk0]
  calc x i ^ q = x i ^ (q - 1) * x i := by rw [← pow_succ]; congr 1; omega
    _ = (a i : L) * x i := by rw [hx i]

end Basic

section Conj

variable {L : Type} [Field L]

theorem map_transvection₃ (f : L →+* L) {i j : Fin 3} (h : i ≠ j) (a : L) :
    SpecialLinearGroup.map f (SpecialLinearGroup.transvection h a) =
      SpecialLinearGroup.transvection h (f a) := by
  ext k l
  simp [SpecialLinearGroup.transvection_coe, Matrix.one_apply, Matrix.single_apply]

theorem toGL_injective₃ :
    Function.Injective (Matrix.SpecialLinearGroup.toGL : SL(3, L) →* GL (Fin 3) L) :=
  fun _ _ h => Subtype.ext (congrArg (fun G : GL (Fin 3) L => (G : Matrix (Fin 3) (Fin 3) L)) h)

theorem diagGL3_inv (h : Fin 3 → Lˣ) : (diagGL3 h)⁻¹ = diagGL3 (fun i => (h i)⁻¹) :=
  Units.ext rfl

theorem conjDiag3_inv_conjDiag3 (h : Fin 3 → Lˣ) (X : SL(3, L)) :
    conjDiag3 (fun i => (h i)⁻¹) (conjDiag3 h X) = X := by
  apply toGL_injective₃
  rw [toGL_conjDiag3, toGL_conjDiag3, ← diagGL3_inv]
  group

theorem conjDiag3_conjDiag3_inv (h : Fin 3 → Lˣ) (X : SL(3, L)) :
    conjDiag3 h (conjDiag3 (fun i => (h i)⁻¹) X) = X := by
  have := conjDiag3_inv_conjDiag3 (fun i => (h i)⁻¹) X
  simpa using this

theorem split_conj_eq {Φ₀ : L →+* L} (Θ : SL(3, L) ≃* SL(3, L)) (b : Fin 3 → Fin 3 → Lˣ)
    (hshape : ∀ (i j : Fin 3) (hij : i ≠ j) (t : L),
      ((Θ (SpecialLinearGroup.transvection hij t) : SL(3, L)) : Matrix (Fin 3) (Fin 3) L) =
        1 + single i j ((b i j : L) * Φ₀ t))
    (a h : Fin 3 → Lˣ) (hab : ∀ i j, i ≠ j → (b i j : L) = (a i : L) * ((a j)⁻¹ : Lˣ))
    (hh : ∀ i, Φ₀ (h i) = (a i : L) * (h i : L)) (X : SL(3, L)) :
    Θ X = conjDiag3 (fun i => (h i)⁻¹) (SpecialLinearGroup.map Φ₀ (conjDiag3 h X)) := by
  have hmon : Θ.toMonoidHom = (conjDiag3Hom (fun i => (h i)⁻¹)).comp
      ((SpecialLinearGroup.map Φ₀).comp (conjDiag3Hom h)) := by
    refine MonoidHom.eq_of_eqOn_dense
      (CFSG.LinearGroups.special_linear_elementary_generation (n := 3) (K := L)) ?_
    rintro _ ⟨i, j, hij, t, rfl⟩
    have hΘ : Θ (SpecialLinearGroup.transvection hij t) =
        SpecialLinearGroup.transvection hij ((b i j : L) * Φ₀ t) :=
      Subtype.ext ((hshape i j hij t).trans (CFSG.LinearGroups.coe_transvection hij _).symm)
    simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, conjDiag3Hom_apply]
    rw [hΘ, conjDiag3_transvection, map_transvection₃, conjDiag3_transvection]
    congr 1
    have hhi : (h i : L) ≠ 0 := (h i).ne_zero
    have hhj : (h j : L) ≠ 0 := (h j).ne_zero
    have haj : (a j : L) ≠ 0 := (a j).ne_zero
    rw [hab i j hij]
    simp only [Units.val_inv_eq_inv_val, map_mul, map_inv₀, inv_inv, hh]
    field_simp
  exact DFunLike.congr_fun hmon X

end Conj


section InvT

variable {L : Type} [Field L]

theorem invTransposeSL_map {S : Type} [Field S] (f : L →+* S) (A : SL(3, L)) :
    invTransposeSL (SpecialLinearGroup.map f A) = SpecialLinearGroup.map f (invTransposeSL A) := by
  apply Subtype.ext
  change ((invTransposeSL (SpecialLinearGroup.map f A) : SL(3, S)) : Matrix (Fin 3) (Fin 3) S) =
    ((SpecialLinearGroup.map f (invTransposeSL A) : SL(3, S)) : Matrix (Fin 3) (Fin 3) S)
  rw [coe_invTransposeSL, ← map_inv, SpecialLinearGroup.map_apply_coe,
    SpecialLinearGroup.map_apply_coe, coe_invTransposeSL]
  simp [RingHom.mapMatrix_apply, Matrix.transpose_map]

theorem invTransposeSL_transvection_charTwo [CharP L 2] {i j : Fin 3} (hij : i ≠ j) (t : L) :
    invTransposeSL (SpecialLinearGroup.transvection hij t) =
      SpecialLinearGroup.transvection hij.symm t := by
  have := invTransposeSL_transvection (K := L) hij.symm t
  rw [CharTwo.neg_eq] at this
  exact this

end InvT

section UnitaryDiag

variable {L : Type} [Field L] [CharP L 2]

theorem diag_of_shape_unitary (Φ₀ : L →+* L) (Θ : SL(3, L) ≃* SL(3, L)) (A : GL (Fin 3) L)
    (hA : ∀ X : SL(3, L), ((Θ X : SL(3, L)) : Matrix (Fin 3) (Fin 3) L) =
      (A : Matrix (Fin 3) (Fin 3) L) *
        ((invTransposeSL (SpecialLinearGroup.map Φ₀ X) : SL(3, L)) : Matrix (Fin 3) (Fin 3) L) *
          (↑A⁻¹ : Matrix (Fin 3) (Fin 3) L))
    (b : Fin 3 → Fin 3 → Lˣ)
    (hshape : ∀ (i j : Fin 3) (hij : i ≠ j) (t : L),
      ((Θ (SpecialLinearGroup.transvection hij t) : SL(3, L)) : Matrix (Fin 3) (Fin 3) L) =
        1 + single j i ((b i j : L) * Φ₀ t)) :
    ∃ a : Fin 3 → Lˣ, (A : Matrix (Fin 3) (Fin 3) L) = Matrix.diagonal (fun i => (a i : L)) ∧
      ∀ i j, i ≠ j → (b i j : L) = (a j : L) * ((a i)⁻¹ : Lˣ) := by
  set M : Matrix (Fin 3) (Fin 3) L := (A : Matrix (Fin 3) (Fin 3) L) with hM
  have hMN : (↑A⁻¹ : Matrix (Fin 3) (Fin 3) L) * M = 1 := by
    rw [hM, ← Units.val_mul, inv_mul_cancel, Units.val_one]
  have hrel : ∀ i j, i ≠ j → M * single j i (1 : L) = single j i (b i j : L) * M := by
    intro i j hij
    refine mul_single_of_conj hMN ?_
    have h1 := hA (SpecialLinearGroup.transvection hij 1)
    rw [hshape i j hij 1, map_transvection₃, Φ₀.map_one, invTransposeSL_transvection_charTwo hij,
      CFSG.LinearGroups.coe_transvection hij.symm 1, mul_one] at h1
    exact h1.symm
  have hoff : ∀ j a, a ≠ j → M a j = 0 := by
    intro j a ha
    obtain ⟨i, hi⟩ := fin3_exists_ne j
    exact (single_offdiag M (hrel i j hi)).1 a ha
  have hdiag : M = Matrix.diagonal fun i => M i i := by
    ext a i
    by_cases h : a = i
    · subst h
      simp
    · simp [Matrix.diagonal_apply_ne _ h, hoff i a h]
  have hdet : IsUnit M.det := (Matrix.isUnit_iff_isUnit_det M).1 (Units.isUnit A)
  have hne : ∀ i, M i i ≠ 0 := by
    have h1 : ∏ i, M i i ≠ 0 := by
      have := hdet.ne_zero
      rwa [hdiag, Matrix.det_diagonal] at this
    exact fun i => (Finset.prod_ne_zero_iff.1 h1) i (Finset.mem_univ i)
  refine ⟨fun i => Units.mk0 (M i i) (hne i), hdiag, fun i j hij => ?_⟩
  have h2 := (single_offdiag M (hrel i j hij)).2
  simp only [Units.val_mk0, Units.val_inv_eq_inv_val]
  have := hne i
  field_simp
  exact h2.symm

omit [CharP L 2] in
theorem exists_diag_lang_unitary [IsAlgClosed L] (q : ℕ) (a : Fin 3 → Lˣ) :
    ∃ h : Fin 3 → Lˣ, ∀ i, (h i : L) ^ q * (h i : L) * (a i : L) = 1 := by
  choose x hx using fun i => IsAlgClosed.exists_pow_nat_eq ((a i : L)⁻¹) (Nat.succ_pos q)
  have hx0 : ∀ i, x i ≠ 0 := fun i h0 => by
    have := hx i
    rw [h0, zero_pow (Nat.succ_ne_zero q)] at this
    exact inv_ne_zero (a i).ne_zero this.symm
  refine ⟨fun i => Units.mk0 (x i) (hx0 i), fun i => ?_⟩
  simp only [Units.val_mk0]
  rw [← pow_succ, hx i]
  exact inv_mul_cancel₀ (a i).ne_zero

theorem unitary_conj_eq {Φ₀ : L →+* L} (Θ : SL(3, L) ≃* SL(3, L)) (b : Fin 3 → Fin 3 → Lˣ)
    (hshape : ∀ (i j : Fin 3) (hij : i ≠ j) (t : L),
      ((Θ (SpecialLinearGroup.transvection hij t) : SL(3, L)) : Matrix (Fin 3) (Fin 3) L) =
        1 + single j i ((b i j : L) * Φ₀ t))
    (a h : Fin 3 → Lˣ) (hab : ∀ i j, i ≠ j → (b i j : L) = (a j : L) * ((a i)⁻¹ : Lˣ))
    (hh : ∀ i, Φ₀ (h i) * (h i : L) * (a i : L) = 1) (X : SL(3, L)) :
    Θ X = conjDiag3 (fun i => (h i)⁻¹)
      (invTransposeSL (SpecialLinearGroup.map Φ₀ (conjDiag3 h X))) := by
  have hmon : Θ.toMonoidHom = (conjDiag3Hom (fun i => (h i)⁻¹)).comp
      (invTransposeSL.comp ((SpecialLinearGroup.map Φ₀).comp (conjDiag3Hom h))) := by
    refine MonoidHom.eq_of_eqOn_dense
      (CFSG.LinearGroups.special_linear_elementary_generation (n := 3) (K := L)) ?_
    rintro _ ⟨i, j, hij, t, rfl⟩
    have hΘ : Θ (SpecialLinearGroup.transvection hij t) =
        SpecialLinearGroup.transvection hij.symm ((b i j : L) * Φ₀ t) :=
      Subtype.ext ((hshape i j hij t).trans (CFSG.LinearGroups.coe_transvection hij.symm _).symm)
    simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, conjDiag3Hom_apply]
    rw [hΘ, conjDiag3_transvection, map_transvection₃, invTransposeSL_transvection_charTwo,
      conjDiag3_transvection]
    congr 1
    have hhi : (h i : L) ≠ 0 := (h i).ne_zero
    have hhj : (h j : L) ≠ 0 := (h j).ne_zero
    have hai : (a i : L) ≠ 0 := (a i).ne_zero
    have haj : (a j : L) ≠ 0 := (a j).ne_zero
    have hΦ : ∀ k, Φ₀ (h k) = ((h k : L) * (a k : L))⁻¹ := fun k =>
      eq_inv_of_mul_eq_one_left (by rw [← mul_assoc]; exact hh k)
    rw [hab i j hij]
    simp only [Units.val_inv_eq_inv_val, map_mul, map_inv₀, inv_inv, hΦ]
    field_simp
  exact DFunLike.congr_fun hmon X

end UnitaryDiag


section Model

variable {L : Type} [Field L]

theorem map_injective₃ {K L : Type} [Field K] [Field L] (f : K →+* L) :
    Function.Injective (SpecialLinearGroup.map (n := Fin 3) f) := by
  intro A B h
  ext i j
  have := congrFun (congrFun (congrArg (fun C : SL(3, L) => (C : Matrix (Fin 3) (Fin 3) L)) h) i) j
  simpa using f.injective this

theorem conjDiag3_injective (d : Fin 3 → Lˣ) : Function.Injective (conjDiag3 d) := by
  intro A B h
  have := congrArg (conjDiag3 (fun i => (d i)⁻¹)) h
  rwa [conjDiag3_inv_conjDiag3, conjDiag3_inv_conjDiag3] at this

theorem iterate_frob_pow {q : ℕ} (k : ℕ) (Φ₀ : L →+* L) (hΦ₀ : ∀ c, Φ₀ c = c ^ q) (c : L) :
    (⇑Φ₀)^[k] c = c ^ q ^ k := by
  induction k with
  | zero => simp
  | succ k ih => rw [Function.iterate_succ_apply', ih, hΦ₀, ← pow_mul, ← pow_succ]

theorem iterate_map_sl (Φ₀ : L →+* L) (k : ℕ) (Y : SL(3, L)) (a b : Fin 3) :
    (((⇑(SpecialLinearGroup.map Φ₀))^[k] Y : SL(3, L)) : Matrix (Fin 3) (Fin 3) L) a b =
      (⇑Φ₀)^[k] ((Y : Matrix (Fin 3) (Fin 3) L) a b) := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [Function.iterate_succ_apply', Function.iterate_succ_apply']
    simp [ih]

theorem exists_of_entries_in_range {K : Type} [Field K] (ι : K →+* L) (Y : SL(3, L))
    (h : ∀ a b, ∃ c : K, ι c = (Y : Matrix (Fin 3) (Fin 3) L) a b) :
    ∃ B : SL(3, K), SpecialLinearGroup.map ι B = Y := by
  choose c hc using h
  have hdet : (Matrix.of c : Matrix (Fin 3) (Fin 3) K).det = 1 := by
    apply ι.injective
    rw [RingHom.map_det, map_one]
    have : ι.mapMatrix (Matrix.of c : Matrix (Fin 3) (Fin 3) K) = (Y : Matrix (Fin 3) (Fin 3) L) := by
      ext a b
      simpa using hc a b
    rw [this]
    exact Y.2
  let B : SL(3, K) := ⟨Matrix.of c, hdet⟩
  refine ⟨B, ?_⟩
  ext a b
  rw [SpecialLinearGroup.map_apply_coe]
  simpa [B] using hc a b

theorem range_eq_fixed {K : Type} [Field K] [Finite K] [Algebra K L] [IsAlgClosed L] [CharP L 2]
    {e : ℕ} (he : e ≠ 0) (hK : Nat.card K = 2 ^ e) :
    ∀ y : L, y ^ 2 ^ e = y ↔ ∃ c : K, algebraMap K L c = y := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hsub : Set.range (algebraMap K L) ⊆ {y : L | y ^ 2 ^ e = y} := by
    rintro _ ⟨c, rfl⟩
    have : Fintype K := Fintype.ofFinite K
    have h1 : c ^ 2 ^ e = c := by
      rw [← hK, Nat.card_eq_fintype_card]
      exact FiniteField.pow_card c
    show (algebraMap K L c) ^ 2 ^ e = algebraMap K L c
    rw [← map_pow, h1]
  have hcard : Nat.card {y : L | y ^ 2 ^ e = y} = 2 ^ e :=
    CFSG.RankThree.Classical2.natCard_setOf_pow_eq_self he
  have hfin : Set.Finite {y : L | y ^ 2 ^ e = y} :=
    Set.finite_of_ncard_pos (by
      rw [Nat.card_coe_set_eq] at hcard
      rw [hcard]
      exact pow_pos (by norm_num) e)
  have hrange : (Set.range (algebraMap K L)).ncard = 2 ^ e := by
    rw [← Set.image_univ, Set.ncard_image_of_injective _ (algebraMap K L).injective,
      Set.ncard_univ, hK]
  have hEq : Set.range (algebraMap K L) = {y : L | y ^ 2 ^ e = y} := by
    refine Set.eq_of_subset_of_ncard_le hsub ?_ hfin
    rw [hrange, ← Nat.card_coe_set_eq, hcard]
  intro y
  constructor
  · intro hy
    exact (hEq ▸ (show y ∈ {y : L | y ^ 2 ^ e = y} from hy) : y ∈ Set.range (algebraMap K L))
  · rintro ⟨c, rfl⟩
    exact hsub ⟨c, rfl⟩

end Model

section SplitModel

variable {K₀ K L : Type} [Field K₀] [Field K] [Finite K] [Field L]
  [Algebra K₀ L] [IsAlgClosure K₀ L] [Algebra K L] [CharP L 2]

theorem a2_split_model {f₀ p : ℕ} (hf₀ : 1 ≤ f₀) (hK₀ : Nat.card K₀ = 2 ^ f₀) (hp : 1 ≤ p)
    (hK : Nat.card K = 2 ^ (p * f₀)) (σ : K ≃+* K)
    (hσ : ∀ c : K, iterateFrobenius L 2 f₀ (algebraMap K L c) = algebraMap K L (σ c))
    (Θ : SL(3, L) ≃* SL(3, L)) (b : Fin 3 → Fin 3 → Lˣ)
    (hshape : ∀ (i j : Fin 3) (hij : i ≠ j) (t : L),
      ((Θ (SpecialLinearGroup.transvection hij t) : SL(3, L)) : Matrix (Fin 3) (Fin 3) L) =
        1 + single i j ((b i j : L) * iterateFrobenius L 2 f₀ t)) :
    ∃ ψ : SL(3, K) →* SL(3, L), Function.Injective ψ ∧
      (∀ B, Θ (ψ B) = ψ (SpecialLinearGroup.map σ.toRingHom B)) ∧
      ∀ X, (⇑Θ)^[p] X = X ↔ X ∈ ψ.range := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : IsAlgClosed L := IsAlgClosure.isAlgClosed K₀
  set Φ₀ : L →+* L := iterateFrobenius L 2 f₀ with hΦ₀
  have hΦ₀c : ∀ c, Φ₀ c = c ^ 2 ^ f₀ := fun c => iterateFrobenius_def 2 f₀ c
  have hq0 : 2 ≤ 2 ^ f₀ := by
    calc 2 = 2 ^ 1 := by norm_num
      _ ≤ 2 ^ f₀ := Nat.pow_le_pow_right (by norm_num) hf₀
  obtain ⟨⟨A, hA⟩, -⟩ := CFSG.RankThree.SL3RootPermuting.sl3_root_permuting_frobenius_fixed_split
    (ℓ := 2) (f := f₀) (k := K₀) (Ω := L) Nat.prime_two hf₀ hK₀ (Equiv.refl (Fin 3)) Θ b
    (fun i j hij t => by rw [hshape i j hij t, hΦ₀c]; rfl)
  obtain ⟨a, -, hab⟩ := diag_of_shape_split (by positivity) Θ A hA b
    (fun i j hij t => by rw [hshape i j hij t, hΦ₀c])
  obtain ⟨h, hh⟩ := exists_diag_lang hq0 a
  have hh' : ∀ i, Φ₀ (h i) = (a i : L) * (h i : L) := fun i => by rw [hΦ₀c]; exact hh i
  have hΘ := split_conj_eq Θ b hshape a h hab hh'
  let ι : K →+* L := algebraMap K L
  let ψ : SL(3, K) →* SL(3, L) :=
    (conjDiag3Hom (fun i => (h i)⁻¹)).comp (SpecialLinearGroup.map ι)
  have hψ : ∀ B, ψ B = conjDiag3 (fun i => (h i)⁻¹) (SpecialLinearGroup.map ι B) := fun B => rfl
  refine ⟨ψ, ?_, ?_, ?_⟩
  · intro B B' hBB
    rw [hψ, hψ] at hBB
    exact map_injective₃ ι (conjDiag3_injective _ hBB)
  · intro B
    rw [hψ, hψ, hΘ, conjDiag3_conjDiag3_inv]
    congr 1
    ext i j
    simpa [SpecialLinearGroup.map_apply_coe] using hσ (B i j)
  · intro X
    have hiter : ∀ k Y, (⇑Θ)^[k] Y = conjDiag3 (fun i => (h i)⁻¹)
        ((⇑(SpecialLinearGroup.map Φ₀))^[k] (conjDiag3 h Y)) := by
      intro k
      induction k with
      | zero => intro Y; simp [conjDiag3_inv_conjDiag3]
      | succ k ih =>
        intro Y
        rw [Function.iterate_succ_apply', Function.iterate_succ_apply', ih, hΘ,
          conjDiag3_conjDiag3_inv]
    have hpow : ∀ Y : SL(3, L), (⇑(SpecialLinearGroup.map Φ₀))^[p] Y = Y ↔
        ∀ a b, ((Y : Matrix (Fin 3) (Fin 3) L) a b) ^ 2 ^ (p * f₀) =
          (Y : Matrix (Fin 3) (Fin 3) L) a b := by
      intro Y
      constructor
      · intro hY a b
        have := congrArg (fun Z : SL(3, L) => (Z : Matrix (Fin 3) (Fin 3) L) a b) hY
        simp only [iterate_map_sl, iterate_frob_pow p Φ₀ hΦ₀c] at this
        rwa [← pow_mul, mul_comm f₀ p] at this
      · intro hY
        ext a b
        rw [iterate_map_sl, iterate_frob_pow p Φ₀ hΦ₀c, ← pow_mul, mul_comm f₀ p]
        exact hY a b
    rw [hiter]
    have hXY : conjDiag3 (fun i => (h i)⁻¹) (conjDiag3 h X) = X := conjDiag3_inv_conjDiag3 h X
    have hfix := range_eq_fixed (K := K) (L := L) (e := p * f₀) (by positivity) hK
    constructor
    · intro hX
      have hX' : (⇑(SpecialLinearGroup.map Φ₀))^[p] (conjDiag3 h X) = conjDiag3 h X := by
        apply conjDiag3_injective (fun i => (h i)⁻¹)
        rw [hX, hXY]
      obtain ⟨B, hB⟩ := exists_of_entries_in_range ι (conjDiag3 h X)
        (fun a b => (hfix _).1 ((hpow _).1 hX' a b))
      refine ⟨B, ?_⟩
      rw [hψ, hB, hXY]
    · rintro ⟨B, rfl⟩
      rw [hψ, conjDiag3_conjDiag3_inv]
      congr 1
      refine (hpow _).2 fun a b => (hfix _).2 ⟨B a b, ?_⟩
      simp [SpecialLinearGroup.map_apply_coe, ι]

end SplitModel



section Quadratic

variable {L : Type} [Field L] [IsAlgClosed L] [CharP L 2]

theorem exists_subfield_card {n : ℕ} (hn : n ≠ 0) :
    ∃ (K : Type) (_ : Field K) (_ : Finite K) (_ : CharP K 2) (ι : K →+* L),
      Nat.card K = 2 ^ n ∧ ∀ y : L, y ^ 2 ^ n = y ↔ ∃ c, ι c = y := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let S : Subfield L := RingHom.eqLocusField (iterateFrobenius L 2 n) (RingHom.id L)
  have hmem : ∀ y, y ∈ S ↔ y ^ 2 ^ n = y := fun y => by
    rw [RingHom.mem_eqLocusField, iterateFrobenius_def, RingHom.id_apply]
  have hcard : Nat.card S = 2 ^ n := by
    rw [← CFSG.RankThree.Classical2.natCard_setOf_pow_eq_self (Ω := L) (ℓ := 2) hn]
    exact Nat.card_congr (Equiv.subtypeEquivRight hmem)
  have hfin : Finite S := Nat.finite_of_card_ne_zero (by rw [hcard]; positivity)
  have hchar : CharP S 2 := ⟨fun x => by
    rw [← S.subtype.injective.eq_iff, map_natCast, map_zero]
    exact CharP.cast_eq_zero_iff L 2 x⟩
  refine ⟨S, inferInstance, hfin, hchar, S.subtype, hcard, fun y => ?_⟩
  constructor
  · intro hy
    exact ⟨⟨y, (hmem y).2 hy⟩, rfl⟩
  · rintro ⟨c, rfl⟩
    exact (hmem _).1 c.2

end Quadratic


section Sigma

theorem exists_sigma_unitary {K : Type} [Field K] {f₀ p : ℕ} (hf₀ : 1 ≤ f₀) (hp : p.Prime)
    (hodd : Odd p) (hK : Nat.card K = (2 ^ (p * f₀)) ^ 2) :
    ∃ σ : K ≃+* K, orderOf σ = p ∧ ∀ a, σ a = a ^ 2 ^ (f₀ * (p + 1)) := by
  have hn : Nat.card K = 2 ^ (2 * (p * f₀)) := by rw [hK, ← pow_mul, mul_comm]
  have hp0 := hp.pos
  have hpf : 1 ≤ 2 * (p * f₀) := by nlinarith
  obtain ⟨φ, hφ, hφord, -⟩ :=
    CFSG.LocalAnalysis.ComponentInitial.finite_field_automorphism_fixed_field_cardinality
      Nat.prime_two hpf hn
  refine ⟨φ ^ (f₀ * (p + 1)), ?_, fun a => pow_apply_of_squaring hφ _ a⟩
  have : Fact p.Prime := ⟨hp⟩
  refine orderOf_eq_prime ?_ ?_
  · rw [← pow_mul, ← orderOf_dvd_iff_pow_eq_one, hφord]
    obtain ⟨m, hm⟩ := hodd
    exact ⟨m + 1, by subst hm; ring⟩
  · intro h1
    have h2 := orderOf_dvd_iff_pow_eq_one.2 h1
    rw [hφord] at h2
    have h3 : 2 * (p * f₀) ≤ f₀ * (p + 1) := Nat.le_of_dvd (by positivity) h2
    nlinarith [hp.two_le]

end Sigma

section SUHoms

variable {K : Type} [Field K] [Finite K] {g : ℕ}

@[expose] def statedSU_toSL (hK : Nat.card K = (2 ^ g) ^ 2) :
    ↥(StatedSU 3 (2 ^ g) K) →* SL(3, K) where
  toFun A := ⟨((A : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K),
    ((mem_statedSU_iff hK A.1).1 A.2).1⟩
  map_one' := Subtype.ext rfl
  map_mul' _ _ := Subtype.ext rfl

theorem coe_statedSU_toSL (hK : Nat.card K = (2 ^ g) ^ 2) (A : ↥(StatedSU 3 (2 ^ g) K)) :
    ((statedSU_toSL hK A : SL(3, K)) : Matrix (Fin 3) (Fin 3) K) =
      ((A : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) := rfl

theorem statedSU_toSL_injective (hK : Nat.card K = (2 ^ g) ^ 2) :
    Function.Injective (statedSU_toSL hK) := by
  intro A B h
  apply Subtype.ext
  apply Units.ext
  exact congrArg (fun C : SL(3, K) => (C : Matrix (Fin 3) (Fin 3) K)) h

theorem statedSU_toSL_unitary (hK : Nat.card K = (2 ^ g) ^ 2) (A : ↥(StatedSU 3 (2 ^ g) K)) :
    (((statedSU_toSL hK A : SL(3, K)) : Matrix (Fin 3) (Fin 3) K).map (· ^ 2 ^ g))ᵀ *
      ((statedSU_toSL hK A : SL(3, K)) : Matrix (Fin 3) (Fin 3) K) = 1 :=
  ((mem_statedSU_iff hK A.1).1 A.2).2

theorem toGL_mem_statedSU (hK : Nat.card K = (2 ^ g) ^ 2) (B : SL(3, K))
    (h : (((B : Matrix (Fin 3) (Fin 3) K)).map (· ^ 2 ^ g))ᵀ * (B : Matrix (Fin 3) (Fin 3) K) = 1) :
    Matrix.SpecialLinearGroup.toGL B ∈ StatedSU 3 (2 ^ g) K := by
  rw [mem_statedSU_iff hK]
  exact ⟨B.2, h⟩

@[expose] noncomputable def statedSU_map (hK : Nat.card K = (2 ^ g) ^ 2) (σ : K ≃+* K) :
    ↥(StatedSU 3 (2 ^ g) K) →* ↥(StatedSU 3 (2 ^ g) K) :=
  ((Matrix.GeneralLinearGroup.map σ.toRingHom).comp (StatedSU 3 (2 ^ g) K).subtype).codRestrict
    (StatedSU 3 (2 ^ g) K) fun A => by
      have hA := (mem_statedSU_iff hK A.1).1 A.2
      rw [MonoidHom.comp_apply, Subgroup.coe_subtype, mem_statedSU_iff hK]
      have hc : ((Matrix.GeneralLinearGroup.map σ.toRingHom (A : GL (Fin 3) K) : GL (Fin 3) K) :
          Matrix (Fin 3) (Fin 3) K) = ((A : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K).map σ := rfl
      rw [hc]
      refine ⟨?_, ?_⟩
      · have := RingHom.map_det σ.toRingHom ((A : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K)
        rw [hA.1, map_one] at this
        exact this.symm
      · have e : (((A : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K).map σ).map (· ^ 2 ^ g) =
            (((A : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K).map (· ^ 2 ^ g)).map σ := by
          ext i j
          simp
        rw [e, ← Matrix.transpose_map, ← Matrix.map_mul]
        rw [hA.2]
        ext i j
        simp [Matrix.one_apply]

theorem coe_statedSU_map (hK : Nat.card K = (2 ^ g) ^ 2) (σ : K ≃+* K)
    (A : ↥(StatedSU 3 (2 ^ g) K)) :
    ((((statedSU_map hK σ A : ↥(StatedSU 3 (2 ^ g) K)) : GL (Fin 3) K)) :
      Matrix (Fin 3) (Fin 3) K) =
      (((A : GL (Fin 3) K)) : Matrix (Fin 3) (Fin 3) K).map σ := rfl

end SUHoms


section UnitaryModel

variable {L : Type} [Field L] [CharP L 2]

omit [CharP L 2] in
theorem iterate_F_even (Φ₀ : L →+* L) (m : ℕ) (Y : SL(3, L)) :
    (fun Z => invTransposeSL (SpecialLinearGroup.map Φ₀ Z))^[2 * m] Y =
      (⇑(SpecialLinearGroup.map Φ₀))^[2 * m] Y := by
  induction m generalizing Y with
  | zero => simp
  | succ m ih =>
    have h2 : (fun Z => invTransposeSL (SpecialLinearGroup.map Φ₀ Z))^[2] Y =
        (⇑(SpecialLinearGroup.map Φ₀))^[2] Y := by
      simp only [Function.iterate_succ, Function.iterate_zero, Function.comp, id_eq]
      rw [← invTransposeSL_map, invTransposeSL_invTransposeSL]
    rw [show 2 * (m + 1) = 2 * m + 2 by ring, Function.iterate_add_apply,
      Function.iterate_add_apply, h2, ih]

omit [CharP L 2] in
theorem iterate_F_odd (Φ₀ : L →+* L) (m : ℕ) (Y : SL(3, L)) :
    (fun Z => invTransposeSL (SpecialLinearGroup.map Φ₀ Z))^[2 * m + 1] Y =
      invTransposeSL ((⇑(SpecialLinearGroup.map Φ₀))^[2 * m + 1] Y) := by
  rw [Function.iterate_succ_apply', Function.iterate_succ_apply', iterate_F_even]

omit [CharP L 2] in
theorem invTransposeSL_iterate_map (Φ₀ : L →+* L) (k : ℕ) (Z : SL(3, L)) :
    invTransposeSL ((⇑(SpecialLinearGroup.map Φ₀))^[k] Z) =
      (⇑(SpecialLinearGroup.map Φ₀))^[k] (invTransposeSL Z) := by
  induction k generalizing Z with
  | zero => rfl
  | succ k ih =>
    rw [Function.iterate_succ_apply, Function.iterate_succ_apply, ih, invTransposeSL_map]

theorem invTransposeSL_map_frob_iff (g : ℕ) (B : SL(3, L)) :
    invTransposeSL (SpecialLinearGroup.map (iterateFrobenius L 2 g) B) = B ↔
      (((B : Matrix (Fin 3) (Fin 3) L).map (· ^ 2 ^ g))ᵀ * (B : Matrix (Fin 3) (Fin 3) L) = 1) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hmap : ((SpecialLinearGroup.map (iterateFrobenius L 2 g) B : SL(3, L)) :
      Matrix (Fin 3) (Fin 3) L) = (B : Matrix (Fin 3) (Fin 3) L).map (· ^ 2 ^ g) := by
    ext a b
    simp [SpecialLinearGroup.map_apply_coe, iterateFrobenius_def]
  have hinv : (↑B⁻¹ : Matrix (Fin 3) (Fin 3) L) * (B : Matrix (Fin 3) (Fin 3) L) = 1 := by
    exact congrArg (fun C : SL(3, L) => (C : Matrix (Fin 3) (Fin 3) L)) (inv_mul_cancel B)
  have hinv' : (B : Matrix (Fin 3) (Fin 3) L) * (↑B⁻¹ : Matrix (Fin 3) (Fin 3) L) = 1 := by
    exact congrArg (fun C : SL(3, L) => (C : Matrix (Fin 3) (Fin 3) L)) (mul_inv_cancel B)
  constructor
  · intro h
    have h1 := congrArg invTransposeSL h
    rw [invTransposeSL_invTransposeSL] at h1
    have h2 := congrArg (fun C : SL(3, L) => (C : Matrix (Fin 3) (Fin 3) L)) h1
    simp only [hmap, coe_invTransposeSL] at h2
    rw [h2, Matrix.transpose_transpose]
    exact hinv
  · intro h
    have h1 : SpecialLinearGroup.map (iterateFrobenius L 2 g) B = invTransposeSL B := by
      apply Subtype.ext
      change ((SpecialLinearGroup.map (iterateFrobenius L 2 g) B : SL(3, L)) :
        Matrix (Fin 3) (Fin 3) L) = ((invTransposeSL B : SL(3, L)) : Matrix (Fin 3) (Fin 3) L)
      rw [hmap, coe_invTransposeSL]
      have h3 : ((B : Matrix (Fin 3) (Fin 3) L).map (· ^ 2 ^ g))ᵀ = (↑B⁻¹ : Matrix (Fin 3) (Fin 3) L) := by
        calc ((B : Matrix (Fin 3) (Fin 3) L).map (· ^ 2 ^ g))ᵀ
            = ((B : Matrix (Fin 3) (Fin 3) L).map (· ^ 2 ^ g))ᵀ *
              ((B : Matrix (Fin 3) (Fin 3) L) * (↑B⁻¹ : Matrix (Fin 3) (Fin 3) L)) := by
              rw [hinv', Matrix.mul_one]
          _ = (((B : Matrix (Fin 3) (Fin 3) L).map (· ^ 2 ^ g))ᵀ * (B : Matrix (Fin 3) (Fin 3) L)) *
              (↑B⁻¹ : Matrix (Fin 3) (Fin 3) L) := by rw [Matrix.mul_assoc]
          _ = (↑B⁻¹ : Matrix (Fin 3) (Fin 3) L) := by rw [h, Matrix.one_mul]
      rw [← h3, Matrix.transpose_transpose]
    rw [h1, invTransposeSL_invTransposeSL]

end UnitaryModel


section UnitaryMain

variable {K₀ L : Type} [Field K₀] [Field L] [Algebra K₀ L] [IsAlgClosure K₀ L] [CharP L 2]

theorem a2_unitary_model {f₀ p : ℕ} (hf₀ : 1 ≤ f₀) (hK₀ : Nat.card K₀ = 2 ^ f₀) (hp : p.Prime)
    (hodd : Odd p) (Θ : SL(3, L) ≃* SL(3, L)) (b : Fin 3 → Fin 3 → Lˣ)
    (hshape : ∀ (i j : Fin 3) (hij : i ≠ j) (t : L),
      ((Θ (SpecialLinearGroup.transvection hij t) : SL(3, L)) : Matrix (Fin 3) (Fin 3) L) =
        1 + single j i ((b i j : L) * iterateFrobenius L 2 f₀ t)) :
    ∃ (K : Type) (_ : Field K) (_ : Finite K) (_ : CharP K 2) (σ : K ≃+* K)
      (ψ : ↥(StatedSU 3 (2 ^ (p * f₀)) K) →* SL(3, L))
      (τ' : ↥(StatedSU 3 (2 ^ (p * f₀)) K) →* ↥(StatedSU 3 (2 ^ (p * f₀)) K)),
      Nat.card K = (2 ^ (p * f₀)) ^ 2 ∧ orderOf σ = p ∧
      (∀ A, (((τ' A : ↥(StatedSU 3 (2 ^ (p * f₀)) K)) : GL (Fin 3) K) :
          Matrix (Fin 3) (Fin 3) K) =
        (((A : ↥(StatedSU 3 (2 ^ (p * f₀)) K)) : GL (Fin 3) K) :
          Matrix (Fin 3) (Fin 3) K).map σ) ∧
      Function.Injective ψ ∧ (∀ A, Θ (ψ A) = ψ (τ' A)) ∧
      ∀ X, (⇑Θ)^[p] X = X ↔ X ∈ ψ.range := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : IsAlgClosed L := IsAlgClosure.isAlgClosed K₀
  have hp0 := hp.pos
  set Φ₀ : L →+* L := iterateFrobenius L 2 f₀ with hΦ₀
  have hΦ₀c : ∀ c, Φ₀ c = c ^ 2 ^ f₀ := fun c => iterateFrobenius_def 2 f₀ c
  obtain ⟨⟨A, hA⟩, -⟩ :=
    CFSG.RankThree.SL3RootPermuting.sl3_root_permuting_frobenius_fixed_unitary (ℓ := 2) (f := f₀)
      (k := K₀) (Ω := L) Nat.prime_two hf₀ hK₀ (Equiv.refl (Fin 3)) Θ b
      (fun i j hij t => by rw [hshape i j hij t, hΦ₀c]; rfl)
  have hmapΦ : ∀ X : SL(3, L), ((SpecialLinearGroup.map Φ₀ X : SL(3, L)) :
      Matrix (Fin 3) (Fin 3) L) = (X : Matrix (Fin 3) (Fin 3) L).map (· ^ 2 ^ f₀) := fun X => by
    ext a b
    simp [SpecialLinearGroup.map_apply_coe, hΦ₀c]
  have hA' : ∀ X : SL(3, L), ((Θ X : SL(3, L)) : Matrix (Fin 3) (Fin 3) L) =
      (A : Matrix (Fin 3) (Fin 3) L) *
        ((invTransposeSL (SpecialLinearGroup.map Φ₀ X) : SL(3, L)) : Matrix (Fin 3) (Fin 3) L) *
          (↑A⁻¹ : Matrix (Fin 3) (Fin 3) L) := fun X => by
    rw [hA X, coe_invTransposeSL, coe_inv_eq_nonsing_inv, hmapΦ]
  obtain ⟨a, -, hab⟩ := diag_of_shape_unitary Φ₀ Θ A hA' b hshape
  obtain ⟨h, hh⟩ := exists_diag_lang_unitary (L := L) (2 ^ f₀) a
  have hh' : ∀ i, Φ₀ (h i) * (h i : L) * (a i : L) = 1 := fun i => by rw [hΦ₀c]; exact hh i
  have hΘ := unitary_conj_eq Θ b hshape a h hab hh'
  obtain ⟨K, _, _, _, ι, hKcard, hKfix⟩ :=
    exists_subfield_card (L := L) (n := 2 * (p * f₀)) (by positivity)
  have hK : Nat.card K = (2 ^ (p * f₀)) ^ 2 := by rw [hKcard, ← pow_mul, mul_comm]
  obtain ⟨σ, hσord, hσc⟩ := exists_sigma_unitary (K := K) hf₀ hp hodd hK
  set FQ : K →+* K := iterateFrobenius K 2 (p * f₀) with hFQdef
  set σ₁ : K →+* K := iterateFrobenius K 2 f₀ with hσ₁def
  have hFQ : ∀ a, FQ a = a ^ 2 ^ (p * f₀) := fun a => iterateFrobenius_def 2 (p * f₀) a
  have hσ₁ : ∀ a, σ₁ a = a ^ 2 ^ f₀ := fun a => iterateFrobenius_def 2 f₀ a
  have hι₁ : ∀ a : K, Φ₀ (ι a) = ι (σ₁ a) := fun a => by rw [hΦ₀c, hσ₁, map_pow]
  have hιQ : ∀ a : K, (⇑Φ₀)^[p] (ι a) = ι (FQ a) := fun a => by
    rw [iterate_frob_pow p Φ₀ hΦ₀c, hFQ, map_pow, ← pow_mul, mul_comm]
  have hσFQ : ∀ a, σ a = FQ (σ₁ a) := fun a => by
    rw [hσc, hFQ, hσ₁, ← pow_mul, ← pow_add]
    congr 2
    ring
  set toSL := statedSU_toSL hK with htoSL
  set ψ : ↥(StatedSU 3 (2 ^ (p * f₀)) K) →* SL(3, L) :=
    (conjDiag3Hom (fun i => (h i)⁻¹)).comp ((SpecialLinearGroup.map ι).comp toSL) with hψdef
  have hψ : ∀ A, ψ A = conjDiag3 (fun i => (h i)⁻¹) (SpecialLinearGroup.map ι (toSL A)) :=
    fun A => rfl
  set τ' := statedSU_map hK σ with hτ'
  have htoSLτ : ∀ A, toSL (τ' A) = SpecialLinearGroup.map σ.toRingHom (toSL A) := fun A =>
    Subtype.ext rfl
  have hBu : ∀ A, invTransposeSL (SpecialLinearGroup.map FQ (toSL A)) = toSL A := fun A =>
    (invTransposeSL_map_frob_iff (p * f₀) (toSL A)).2 (statedSU_toSL_unitary hK A)
  refine ⟨K, inferInstance, inferInstance, inferInstance, σ, ψ, τ', hK, hσord,
    fun A => coe_statedSU_map hK σ A, ?_, ?_, ?_⟩
  · intro A A' hAA
    rw [hψ, hψ] at hAA
    exact statedSU_toSL_injective hK (map_injective₃ ι (conjDiag3_injective _ hAA))
  · intro A
    have h1 : invTransposeSL (SpecialLinearGroup.map σ₁ (toSL A)) =
        SpecialLinearGroup.map σ.toRingHom (toSL A) := by
      have hc : SpecialLinearGroup.map FQ (SpecialLinearGroup.map σ₁ (toSL A)) =
          SpecialLinearGroup.map σ₁ (SpecialLinearGroup.map FQ (toSL A)) := by
        ext i j
        simp [SpecialLinearGroup.map_apply_coe, hFQ, hσ₁, ← pow_mul, mul_comm]
      have hu1 : invTransposeSL (SpecialLinearGroup.map FQ (SpecialLinearGroup.map σ₁ (toSL A))) =
          SpecialLinearGroup.map σ₁ (toSL A) := by
        rw [hc, invTransposeSL_map, hBu]
      have h2 := congrArg invTransposeSL hu1
      rw [invTransposeSL_invTransposeSL] at h2
      rw [← h2]
      ext i j
      simp [SpecialLinearGroup.map_apply_coe, hσFQ]
    rw [hψ A, hψ (τ' A), htoSLτ A, hΘ, conjDiag3_conjDiag3_inv]
    congr 1
    have h2 : SpecialLinearGroup.map Φ₀ (SpecialLinearGroup.map ι (toSL A)) =
        SpecialLinearGroup.map ι (SpecialLinearGroup.map σ₁ (toSL A)) := by
      ext i j
      simp [SpecialLinearGroup.map_apply_coe, hι₁]
    rw [h2, invTransposeSL_map, h1]
  · intro X
    obtain ⟨m, hm⟩ := hodd
    have hiter : ∀ k Y, (⇑Θ)^[k] Y = conjDiag3 (fun i => (h i)⁻¹)
        ((fun Z => invTransposeSL (SpecialLinearGroup.map Φ₀ Z))^[k] (conjDiag3 h Y)) := by
      intro k
      induction k with
      | zero => intro Y; simp [conjDiag3_inv_conjDiag3]
      | succ k ih =>
        intro Y
        rw [Function.iterate_succ_apply', Function.iterate_succ_apply', ih, hΘ,
          conjDiag3_conjDiag3_inv]
    have hF : ∀ Y : SL(3, L), (fun Z => invTransposeSL (SpecialLinearGroup.map Φ₀ Z))^[p] Y =
        invTransposeSL ((⇑(SpecialLinearGroup.map Φ₀))^[p] Y) := by
      intro Y
      rw [hm]
      exact iterate_F_odd Φ₀ m Y
    have hmapι : ∀ B : SL(3, K), (⇑(SpecialLinearGroup.map Φ₀))^[p] (SpecialLinearGroup.map ι B) =
        SpecialLinearGroup.map ι (SpecialLinearGroup.map FQ B) := by
      intro B
      ext i j
      simpa [iterate_map_sl, SpecialLinearGroup.map_apply_coe] using hιQ (B i j)
    have key : ∀ Y : SL(3, L), invTransposeSL ((⇑(SpecialLinearGroup.map Φ₀))^[p] Y) = Y ↔
        ∃ A, SpecialLinearGroup.map ι (toSL A) = Y := by
      intro Y
      constructor
      · intro hY
        have hY1 : (⇑(SpecialLinearGroup.map Φ₀))^[p] Y = invTransposeSL Y := by
          have := congrArg invTransposeSL hY
          rwa [invTransposeSL_invTransposeSL] at this
        have hY2 : (⇑(SpecialLinearGroup.map Φ₀))^[p] ((⇑(SpecialLinearGroup.map Φ₀))^[p] Y) =
            Y := by
          rw [hY1, ← invTransposeSL_iterate_map, hY1, invTransposeSL_invTransposeSL]
        have hent : ∀ i j, ∃ c : K, ι c = (Y : Matrix (Fin 3) (Fin 3) L) i j := by
          intro i j
          refine (hKfix _).1 ?_
          have h3 := congrArg (fun Z : SL(3, L) => (Z : Matrix (Fin 3) (Fin 3) L) i j) hY2
          simp only [iterate_map_sl, iterate_frob_pow p Φ₀ hΦ₀c] at h3
          rw [← pow_mul] at h3
          have e : (2 ^ f₀) ^ p * (2 ^ f₀) ^ p = 2 ^ (2 * (p * f₀)) := by
            rw [← pow_mul, ← pow_add, ← two_mul]
            congr 1
            ring
          rwa [e] at h3
        obtain ⟨B, hB⟩ := exists_of_entries_in_range ι Y hent
        have hu : invTransposeSL (SpecialLinearGroup.map FQ B) = B := by
          have h1 : invTransposeSL ((⇑(SpecialLinearGroup.map Φ₀))^[p]
              (SpecialLinearGroup.map ι B)) = SpecialLinearGroup.map ι B := by
            rw [hB]
            exact hY
          rw [hmapι, invTransposeSL_map] at h1
          exact map_injective₃ ι h1
        have hmem := toGL_mem_statedSU hK B ((invTransposeSL_map_frob_iff (p * f₀) B).1 hu)
        refine ⟨⟨_, hmem⟩, ?_⟩
        rw [← hB]
        rfl
      · rintro ⟨A, rfl⟩
        rw [hmapι, invTransposeSL_map, hBu]
    rw [hiter, hF]
    have hXY : conjDiag3 (fun i => (h i)⁻¹) (conjDiag3 h X) = X := conjDiag3_inv_conjDiag3 h X
    constructor
    · intro hX
      have hX' : invTransposeSL ((⇑(SpecialLinearGroup.map Φ₀))^[p] (conjDiag3 h X)) =
          conjDiag3 h X := by
        apply conjDiag3_injective (fun i => (h i)⁻¹)
        rw [hX, hXY]
      obtain ⟨A, hA⟩ := (key _).1 hX'
      refine ⟨A, ?_⟩
      rw [hψ, hA, hXY]
    · rintro ⟨A, rfl⟩
      rw [hψ, conjDiag3_conjDiag3_inv]
      congr 1
      exact (key _).2 ⟨A, rfl⟩

end UnitaryMain

end CFSG.RankThree.PartOne.KLCE
