module

public import CFSG.RankThree.Classical.SLnScalarCommutant
public import Mathlib.LinearAlgebra.Matrix.Permutation
import Mathlib.RingTheory.RootsOfUnity.AlgebraicallyClosed
public import Mathlib.FieldTheory.IsAlgClosed.Basic

public section

namespace CFSG.RankThree.Classical2

open Matrix CFSG.RankThree.Classical

open scoped Matrix

section Elementary

variable {M : Type*} [Field M]

theorem exists_elementary_smul_mem_naturalSL (k : Subfield M) {n : ℕ} {i j : Fin n}
    (hij : i ≠ j) {c : M} (hc : c ∈ k) :
    ∃ X ∈ naturalSL k n, (X : Matrix (Fin n) (Fin n) M) = 1 + Matrix.single i j c := by
  refine ⟨Matrix.SpecialLinearGroup.toGL (Matrix.SpecialLinearGroup.map k.subtype
    (⟨Matrix.transvection i j ⟨c, hc⟩, Matrix.det_transvection_of_ne i j hij _⟩ :
      Matrix.SpecialLinearGroup (Fin n) k)), ⟨_, rfl⟩, ?_⟩
  change (Matrix.transvection i j (⟨c, hc⟩ : k)).map k.subtype = 1 + Matrix.single i j c
  ext a b
  simp only [Matrix.map_apply, Matrix.transvection, Matrix.add_apply, Matrix.one_apply,
    Matrix.single_apply]
  split_ifs <;> simp

theorem map_one_add_single (τ : M ≃+* M) {n : ℕ} (i j : Fin n) (c : M) :
    (1 + Matrix.single i j c : Matrix (Fin n) (Fin n) M).map τ = 1 + Matrix.single i j (τ c) := by
  rw [Matrix.map_add _ (map_add τ), Matrix.map_one _ (map_zero τ) (map_one τ), Matrix.map_single]

theorem inv_one_add_single {n : ℕ} {i j : Fin n} (hij : i ≠ j) :
    (1 + Matrix.single i j (1 : M))⁻¹ = 1 - Matrix.single i j 1 := by
  apply Matrix.inv_eq_left_inv
  rw [sub_mul, one_mul, mul_add, mul_one, Matrix.single_mul_single_of_ne (h := hij.symm)]
  abel

theorem scalar_mul_mul_inv {n : ℕ} (a : Mˣ) (Y : Matrix (Fin n) (Fin n) M) :
    ((Matrix.GeneralLinearGroup.scalar (Fin n) a : GL (Fin n) M) : Matrix (Fin n) (Fin n) M) * Y *
      (↑(Matrix.GeneralLinearGroup.scalar (Fin n) a)⁻¹ : Matrix (Fin n) (Fin n) M) = Y := by
  rw [← map_inv, Matrix.GeneralLinearGroup.coe_scalar, Matrix.GeneralLinearGroup.coe_scalar,
    Matrix.scalar_apply, Matrix.scalar_apply]
  ext i j
  rw [mul_diagonal, diagonal_mul, Units.val_inv_eq_inv_val, mul_comm (a : M), mul_assoc,
    mul_inv_cancel₀ a.ne_zero, mul_one]

theorem scalar_and_eq_of_conj_map_naturalSL (k : Subfield M) {n : ℕ} (hn : 3 ≤ n) (τ : M ≃+* M)
    (A : GL (Fin n) M)
    (hA : ∀ X ∈ naturalSL k n, (A : Matrix (Fin n) (Fin n) M) *
      (X : Matrix (Fin n) (Fin n) M).map τ * (↑A⁻¹ : Matrix (Fin n) (Fin n) M) = X) :
    A ∈ (Matrix.GeneralLinearGroup.scalar (Fin n)).range ∧ ∀ c ∈ k, τ c = c := by
  have hscalar : A ∈ (Matrix.GeneralLinearGroup.scalar (Fin n)).range := by
    refine mem_range_scalar_of_commute_elementary A fun i j hij => ?_
    obtain ⟨X, hX, hXe⟩ := exists_elementary_mem_naturalSL k hij
    have h := hA X hX
    rw [hXe, map_one_add_single, map_one] at h
    have hinv : (↑A⁻¹ : Matrix (Fin n) (Fin n) M) * (A : Matrix (Fin n) (Fin n) M) = 1 :=
      A.inv_mul
    calc (1 + Matrix.single i j 1) * (A : Matrix (Fin n) (Fin n) M) =
        (A : Matrix (Fin n) (Fin n) M) * (1 + Matrix.single i j 1) *
          (↑A⁻¹ : Matrix (Fin n) (Fin n) M) * (A : Matrix (Fin n) (Fin n) M) := by rw [h]
      _ = (A : Matrix (Fin n) (Fin n) M) * (1 + Matrix.single i j 1) := by
        rw [Matrix.mul_assoc _ (↑A⁻¹ : Matrix (Fin n) (Fin n) M), hinv, Matrix.mul_one]
  refine ⟨hscalar, fun c hc => ?_⟩
  obtain ⟨a, rfl⟩ := hscalar
  have h01 : (⟨0, by omega⟩ : Fin n) ≠ ⟨1, by omega⟩ := by simp [Fin.ext_iff]
  obtain ⟨X, hX, hXe⟩ := exists_elementary_smul_mem_naturalSL k h01 hc
  have h := hA X hX
  rw [scalar_mul_mul_inv, hXe, map_one_add_single] at h
  have h' := congrFun (congrFun h ⟨0, by omega⟩) ⟨1, by omega⟩
  simpa [Matrix.add_apply, Matrix.one_apply_ne h01, Matrix.single_apply] using h'

theorem not_exists_conj_map_inv_transpose_naturalSL (k : Subfield M) {n : ℕ} (hn : 3 ≤ n)
    (τ : M ≃+* M) :
    ¬ ∃ A : GL (Fin n) M, ∀ X ∈ naturalSL k n,
      (A : Matrix (Fin n) (Fin n) M) * ((X : Matrix (Fin n) (Fin n) M).map τ)⁻¹ᵀ *
        (↑A⁻¹ : Matrix (Fin n) (Fin n) M) = X := by
  rintro ⟨A, hA⟩
  have hcol : ∀ i j : Fin n, i ≠ j → ∀ l, l ≠ i → (A : Matrix (Fin n) (Fin n) M) l j = 0 := by
    intro i j hij l hl
    obtain ⟨X, hX, hXe⟩ := exists_elementary_mem_naturalSL k hij
    have h := hA X hX
    rw [hXe, map_one_add_single, map_one, inv_one_add_single hij, Matrix.transpose_sub,
      Matrix.transpose_one, Matrix.transpose_single] at h
    exact apply_eq_zero_of_conj_inv_transpose_elementary A h hl
  have h0 : (⟨0, by omega⟩ : Fin n) ≠ ⟨1, by omega⟩ := by simp [Fin.ext_iff]
  have h1 : (⟨0, by omega⟩ : Fin n) ≠ ⟨2, by omega⟩ := by simp [Fin.ext_iff]
  have h2 : (⟨1, by omega⟩ : Fin n) ≠ ⟨2, by omega⟩ := by simp [Fin.ext_iff]
  have hzero : ∀ l, (A : Matrix (Fin n) (Fin n) M) l ⟨0, by omega⟩ = 0 := by
    intro l
    by_cases hl : l = ⟨1, by omega⟩
    · subst hl
      exact hcol _ _ h1.symm _ h2
    · exact hcol _ _ h0.symm _ hl
  exact Matrix.GeneralLinearGroup.det_ne_zero A (Matrix.det_eq_zero_of_column_eq_zero _ hzero)

end Elementary

section Unitary

variable {Ω : Type*} [Field Ω]

theorem exists_ne_and_ne {n : ℕ} (hn : 3 ≤ n) (i j : Fin n) : ∃ h : Fin n, h ≠ i ∧ h ≠ j := by
  by_cases h0 : (⟨0, by omega⟩ : Fin n) ≠ i ∧ (⟨0, by omega⟩ : Fin n) ≠ j
  · exact ⟨_, h0⟩
  by_cases h1 : (⟨1, by omega⟩ : Fin n) ≠ i ∧ (⟨1, by omega⟩ : Fin n) ≠ j
  · exact ⟨_, h1⟩
  refine ⟨⟨2, by omega⟩, ?_, ?_⟩ <;> intro h <;>
    simp only [ne_eq, Fin.ext_iff, not_and_or, not_not] at h0 h1 h <;> omega

@[expose] def unitarySet (q n : ℕ) : Set (GL (Fin n) Ω) :=
  {X | (∀ i j, (X : Matrix (Fin n) (Fin n) Ω) i j ^ q ^ 2 = (X : Matrix (Fin n) (Fin n) Ω) i j) ∧
    (X : Matrix (Fin n) (Fin n) Ω).det = 1 ∧
    ((X : Matrix (Fin n) (Fin n) Ω).map (· ^ q))ᵀ * (X : Matrix (Fin n) (Fin n) Ω) = 1}

theorem diagonal_mem_unitary {q n : ℕ} (hq : 1 ≤ q) {d : Fin n → Ω}
    (hd : ∀ i, d i ^ (q + 1) = 1) (hprod : ∏ i, d i = 1) (hdet : IsUnit (diagonal d).det) :
    (Matrix.nonsingInvUnit (diagonal d) hdet : GL (Fin n) Ω) ∈ unitarySet q n := by
  have hq2 : ∀ i, d i ^ q ^ 2 = d i := by
    intro i
    obtain ⟨m, hm⟩ : ∃ m, q ^ 2 = (q + 1) * m + 1 := ⟨q - 1, by
      obtain ⟨s, rfl⟩ : ∃ s, q = s + 1 := ⟨q - 1, by omega⟩
      simp only [Nat.add_sub_cancel]
      ring⟩
    rw [hm, pow_succ, pow_mul, hd, one_pow, one_mul]
  refine ⟨fun i j => ?_, ?_, ?_⟩
  · change (diagonal d) i j ^ q ^ 2 = (diagonal d) i j
    rw [diagonal_apply]
    split_ifs with h
    · subst h
      exact hq2 i
    · exact zero_pow (by positivity)
  · change (diagonal d).det = 1
    rw [det_diagonal, hprod]
  · change ((diagonal d).map (· ^ q))ᵀ * diagonal d = 1
    rw [diagonal_map (f := fun x : Ω => x ^ q) (zero_pow (by omega)), diagonal_transpose,
      diagonal_mul_diagonal,
      ← diagonal_one]
    congr 1
    funext i
    rw [← pow_succ, hd]

theorem permMatrix_mem_unitary {q n : ℕ} (hq : 1 ≤ q) {π : Equiv.Perm (Fin n)}
    (hπ : Equiv.Perm.sign π = 1) (hdet : IsUnit (π.permMatrix Ω).det) :
    (Matrix.nonsingInvUnit (π.permMatrix Ω) hdet : GL (Fin n) Ω) ∈ unitarySet q n := by
  have hmap : (π.permMatrix Ω).map (· ^ q) = π.permMatrix Ω := by
    ext i j
    simp only [Matrix.map_apply, Equiv.Perm.permMatrix, PEquiv.toMatrix_apply]
    split_ifs
    · exact one_pow q
    · exact zero_pow (by omega)
  refine ⟨fun i j => ?_, ?_, ?_⟩
  · change (π.permMatrix Ω) i j ^ q ^ 2 = (π.permMatrix Ω) i j
    simp only [Equiv.Perm.permMatrix, PEquiv.toMatrix_apply]
    split_ifs
    · exact one_pow _
    · exact zero_pow (by positivity)
  · change (π.permMatrix Ω).det = 1
    rw [det_permutation, hπ]
    simp
  · change ((π.permMatrix Ω).map (· ^ q))ᵀ * π.permMatrix Ω = 1
    rw [hmap, transpose_permMatrix, ← permMatrix_mul, mul_inv_cancel, permMatrix_one]

variable {k : Type*} [Field k]

theorem centralizer_unitary_eq_range_scalar [Finite k] {q : ℕ} (hq : Nat.card k = q) [Algebra k Ω]
    [IsAlgClosure k Ω] {n : ℕ} (hn : 3 ≤ n) :
    Subgroup.centralizer (unitarySet (Ω := Ω) q n) =
      (Matrix.GeneralLinearGroup.scalar (Fin n)).range := by
  have := Fintype.ofFinite k
  have : IsAlgClosed Ω := IsAlgClosure.isAlgClosed k
  have hq1 : 1 ≤ q := by
    rw [← hq]
    exact Nat.one_le_iff_ne_zero.mpr Nat.card_pos.ne'
  have hq2 : 2 ≤ q := by
    rw [← hq]
    exact Finite.one_lt_card
  have hq0 : (q : Ω) = 0 := by
    rw [← hq, Nat.card_eq_fintype_card, ← map_natCast (algebraMap k Ω),
      FiniteField.cast_card_eq_zero, map_zero]
  have : NeZero ((q + 1 : ℕ) : Ω) := ⟨by rw [Nat.cast_add, hq0, zero_add, Nat.cast_one]; simp⟩
  obtain ⟨a, ha⟩ := HasEnoughRootsOfUnity.exists_primitiveRoot Ω (q + 1)
  have ha1 : a ≠ 1 := ha.ne_one (by omega)
  have haq : a ^ (q + 1) = 1 := ha.pow_eq_one
  have ha0 : a ≠ 0 := fun h => by
    rw [h, zero_pow (by omega)] at haq
    exact zero_ne_one haq
  ext C
  constructor
  · intro hC
    have hcomm : ∀ X ∈ unitarySet (Ω := Ω) q n,
        (X : Matrix (Fin n) (Fin n) Ω) * C = C * X := fun X hX =>
      congrArg Units.val (Subgroup.mem_centralizer_iff.mp hC X hX)
    have hoff : ∀ i j : Fin n, i ≠ j → (C : Matrix (Fin n) (Fin n) Ω) i j = 0 := by
      intro i j hij
      obtain ⟨h, hhi, hhj⟩ := exists_ne_and_ne hn i j
      set d : Fin n → Ω := fun x => (if x = i then a else 1) * (if x = h then a⁻¹ else 1)
        with hd
      have hdpow : ∀ x, d x ^ (q + 1) = 1 := by
        intro x
        simp only [hd]
        split_ifs <;> simp [mul_pow, inv_pow, haq]
      have hdprod : ∏ x, d x = 1 := by
        simp only [hd, Finset.prod_mul_distrib, Finset.prod_ite_eq', Finset.mem_univ, ite_true]
        exact mul_inv_cancel₀ ha0
      have hdet : IsUnit (diagonal d).det := by
        rw [det_diagonal, hdprod]
        exact isUnit_one
      have h1 := hcomm _ (diagonal_mem_unitary hq1 hdpow hdprod hdet)
      have h2 := congrFun (congrFun h1 i) j
      change (diagonal d * (C : Matrix (Fin n) (Fin n) Ω)) i j =
        ((C : Matrix (Fin n) (Fin n) Ω) * diagonal d) i j at h2
      rw [diagonal_mul, mul_diagonal] at h2
      have hdi : d i = a := by simp [hd, hhi.symm]
      have hdj : d j = 1 := by simp [hd, hij.symm, hhj.symm]
      rw [hdi, hdj, mul_one] at h2
      have h3 : (a - 1) * (C : Matrix (Fin n) (Fin n) Ω) i j = 0 := by
        rw [sub_mul, h2, one_mul, sub_self]
      exact (mul_eq_zero.mp h3).resolve_left (sub_ne_zero.mpr ha1)
    have hdiag : ∀ i j : Fin n, (C : Matrix (Fin n) (Fin n) Ω) i i =
        (C : Matrix (Fin n) (Fin n) Ω) j j := by
      intro i j
      rcases eq_or_ne i j with rfl | hij
      · rfl
      obtain ⟨h, hhi, hhj⟩ := exists_ne_and_ne hn i j
      set π : Equiv.Perm (Fin n) := Equiv.swap i h * Equiv.swap i j with hπdef
      have hπ : Equiv.Perm.sign π = 1 := by
        rw [hπdef, Equiv.Perm.sign_mul, Equiv.Perm.sign_swap hhi.symm,
          Equiv.Perm.sign_swap hij]
        rfl
      have hπi : π i = j := by
        rw [hπdef, Equiv.Perm.mul_apply, Equiv.swap_apply_left,
          Equiv.swap_apply_of_ne_of_ne hij.symm hhj.symm]
      have hdet : IsUnit (π.permMatrix Ω).det := by
        rw [det_permutation, hπ]
        simp
      have h1 := hcomm _ (permMatrix_mem_unitary hq1 hπ hdet)
      have h2 := congrFun (congrFun h1 i) j
      change (π.permMatrix Ω * (C : Matrix (Fin n) (Fin n) Ω)) i j =
        ((C : Matrix (Fin n) (Fin n) Ω) * π.permMatrix Ω) i j at h2
      have hπj : π.symm j = i := by rw [Equiv.symm_apply_eq, hπi]
      rw [Equiv.Perm.permMatrix, PEquiv.toMatrix_toPEquiv_mul, PEquiv.mul_toMatrix_toPEquiv,
        submatrix_apply, submatrix_apply, id, id, hπi, hπj] at h2
      exact h2.symm
    have hC0 : (C : Matrix (Fin n) (Fin n) Ω) ⟨0, by omega⟩ ⟨0, by omega⟩ ≠ 0 := by
      intro h0
      have hcol : ∀ l, (C : Matrix (Fin n) (Fin n) Ω) l ⟨0, by omega⟩ = 0 := by
        intro l
        rcases eq_or_ne l ⟨0, by omega⟩ with rfl | hl
        · exact h0
        · exact hoff l _ hl
      exact Matrix.GeneralLinearGroup.det_ne_zero C (Matrix.det_eq_zero_of_column_eq_zero _ hcol)
    refine ⟨Units.mk0 _ hC0, Units.ext ?_⟩
    rw [Matrix.GeneralLinearGroup.coe_scalar, Units.val_mk0]
    ext i j
    rw [Matrix.scalar_apply, diagonal_apply]
    split_ifs with h
    · subst h
      exact hdiag _ _
    · exact (hoff i j h).symm
  · rintro ⟨c, rfl⟩
    refine Subgroup.mem_centralizer_iff.mpr fun X _ => Units.ext ?_
    rw [Units.val_mul, Units.val_mul, Matrix.GeneralLinearGroup.coe_scalar]
    exact (Matrix.scalar_commute (c : Ω) (fun r => Commute.all _ r) _).eq.symm

end Unitary

end CFSG.RankThree.Classical2
