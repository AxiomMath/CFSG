module

public import CFSG.RankThree.PartOne.N143X.WeylMatrix

public section

namespace CFSG.RankThree.PartOne.N143X

open Matrix CFSG CFSG.Assembly.LowTwoRank

theorem charP_two_of_card {K : Type} [Field K] [Finite K] {g : ℕ} (hK : Nat.card K = 2 ^ g) :
    CharP K 2 := by
  have : Fintype K := Fintype.ofFinite K
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  exact charP_of_card_eq_prime_pow (f := g) (by rw [Fintype.card_eq_nat_card]; exact hK)

theorem natCast_ne_zero_of_card_two_pow {K : Type} [Field K] [Finite K] {g : ℕ}
    (hK : Nat.card K = 2 ^ g) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) : (p : K) ≠ 0 := by
  have hchar : CharP K 2 := charP_two_of_card hK
  intro h
  have := (CharP.cast_eq_zero_iff K 2 p).1 h
  exact hp2 ((Nat.prime_dvd_prime_iff_eq Nat.prime_two hp).1 this).symm

theorem det_eq_one_of_mem_statedSL' {n : ℕ} {K : Type} [Field K] {A : GL (Fin n) K}
    (hA : A ∈ StatedSL n K) : (A : Matrix (Fin n) (Fin n) K).det = 1 :=
  CFSG.Open.StatedAPI.det_of_mem_statedSL hA

theorem det_eq_one_of_mem_statedSU' {n q : ℕ} {K : Type} [Field K] {A : GL (Fin n) K}
    (hA : A ∈ StatedSU n q K) : (A : Matrix (Fin n) (Fin n) K).det = 1 :=
  CFSG.Open.StatedAPI.det_of_mem_statedSU hA

theorem pow_eq_one_of_scalar_det {n : ℕ} {K : Type} [Field K] {c : Kˣ}
    (hdet : ((Matrix.GeneralLinearGroup.scalar (Fin n) c : GL (Fin n) K) :
      Matrix (Fin n) (Fin n) K).det = 1) : c ^ n = 1 := by
  have := congrArg Units.val (Matrix.GeneralLinearGroup.det_scalar (n := Fin n) c)
  rw [Matrix.GeneralLinearGroup.val_det_apply, Fintype.card_fin] at this
  exact Units.ext (by rw [Units.val_one]; exact this.symm.trans hdet)

theorem factorization_three_psl_le {T : Type} [Group T] {n f : ℕ} (hn : n ≤ 5)
    (hmod : StatedClassicalModel T .PSL n 2 f) {p : ℕ} (hp : p.Prime) (hp7 : 7 ≤ p)
    {E : Subgroup T} (hE : IsElementaryAbelian p E) :
    (Nat.card E.normalizerMonoidHom.range).factorization 3 ≤ 1 := by
  obtain ⟨hadm, K, _, _, hK, ⟨e⟩⟩ := hmod
  have hn2 : 2 ≤ n := hadm.2.2.1
  have hf : 1 ≤ f := hadm.2.1
  have hpK : (p : K) ≠ 0 := natCast_ne_zero_of_card_two_pow (by simpa using hK) hp (by omega)
  refine factorization_three_le_one_of_matrix_model (StatedSL n K) e hp hpK (d := n) ?_ ?_ hE
    (by simpa using hn)
  · intro c hc
    exact pow_eq_one_of_scalar_det (det_eq_one_of_mem_statedSL' hc)
  · intro h
    have := Nat.le_of_dvd (by omega) h
    omega

theorem factorization_three_psu_le {T : Type} [Group T] {n f : ℕ} (hn : n ≤ 5)
    (hmod : StatedClassicalModel T .PSU n 2 f) {p : ℕ} (hp : p.Prime) (hp7 : 7 ≤ p)
    {E : Subgroup T} (hE : IsElementaryAbelian p E) :
    (Nat.card E.normalizerMonoidHom.range).factorization 3 ≤ 1 := by
  obtain ⟨hadm, K, _, _, hK, ⟨e⟩⟩ := hmod
  have hn3 : 3 ≤ n := hadm.2.2.1
  have hf : 1 ≤ f := hadm.2.1
  have hpK : (p : K) ≠ 0 := natCast_ne_zero_of_card_two_pow (g := 2 * f)
    (by rw [hK, ← pow_mul, mul_comm]) hp (by omega)
  refine factorization_three_le_one_of_matrix_model (StatedSU n (2 ^ f) K) e hp hpK (d := n) ?_ ?_
    hE (by simpa using hn)
  · intro c hc
    exact pow_eq_one_of_scalar_det (det_eq_one_of_mem_statedSU' hc)
  · intro h
    have := Nat.le_of_dvd (by omega) h
    omega

@[expose] def isoGroup {ι : Type} [Fintype ι] [DecidableEq ι] {K : Type} [Field K]
    (J : Matrix ι ι K) : Subgroup (GL ι K) where
  carrier := {A | (A : Matrix ι ι K)ᵀ * J * (A : Matrix ι ι K) = J}
  mul_mem' := fun {A B} hA hB => by
    change ((A * B : GL ι K) : Matrix ι ι K)ᵀ * J * ((A * B : GL ι K) : Matrix ι ι K) = J
    have hA' : (A : Matrix ι ι K)ᵀ * J * (A : Matrix ι ι K) = J := hA
    have hB' : (B : Matrix ι ι K)ᵀ * J * (B : Matrix ι ι K) = J := hB
    calc ((A * B : GL ι K) : Matrix ι ι K)ᵀ * J * ((A * B : GL ι K) : Matrix ι ι K)
        = (B : Matrix ι ι K)ᵀ * ((A : Matrix ι ι K)ᵀ * J * (A : Matrix ι ι K)) *
          (B : Matrix ι ι K) := by
          simp only [Units.val_mul, Matrix.transpose_mul, mul_assoc]
      _ = J := by rw [hA', hB']
  one_mem' := by simp
  inv_mem' := fun {A} hA => by
    change ((A⁻¹ : GL ι K) : Matrix ι ι K)ᵀ * J * ((A⁻¹ : GL ι K) : Matrix ι ι K) = J
    have hA' : (A : Matrix ι ι K)ᵀ * J * (A : Matrix ι ι K) = J := hA
    have h1 : (((A⁻¹ : GL ι K) : Matrix ι ι K)ᵀ * (A : Matrix ι ι K)ᵀ) = 1 := by
      rw [← Matrix.transpose_mul, ← Units.val_mul, mul_inv_cancel, Units.val_one,
        Matrix.transpose_one]
    have h2 : (A : Matrix ι ι K) * ((A⁻¹ : GL ι K) : Matrix ι ι K) = 1 := by
      rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
    calc ((A⁻¹ : GL ι K) : Matrix ι ι K)ᵀ * J * ((A⁻¹ : GL ι K) : Matrix ι ι K)
        = ((A⁻¹ : GL ι K) : Matrix ι ι K)ᵀ * ((A : Matrix ι ι K)ᵀ * J * (A : Matrix ι ι K)) *
          ((A⁻¹ : GL ι K) : Matrix ι ι K) := by rw [hA']
      _ = ((((A⁻¹ : GL ι K) : Matrix ι ι K)ᵀ * (A : Matrix ι ι K)ᵀ) * J) *
          ((A : Matrix ι ι K) * ((A⁻¹ : GL ι K) : Matrix ι ι K)) := by
          simp only [mul_assoc]
      _ = J := by rw [h1, h2, one_mul, mul_one]

theorem mem_isoGroup {ι : Type} [Fintype ι] [DecidableEq ι] {K : Type} [Field K]
    {J : Matrix ι ι K} {A : GL ι K} :
    A ∈ isoGroup J ↔ (A : Matrix ι ι K)ᵀ * J * (A : Matrix ι ι K) = J := Iff.rfl

@[expose] def symJ (n : ℕ) (K : Type) [Field K] : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) K :=
  Matrix.fromBlocks 0 1 (-1) 0

theorem symJ_mul_self (n : ℕ) (K : Type) [Field K] : symJ n K * symJ n K = -1 := by
  simp only [symJ, Matrix.fromBlocks_multiply]
  ext (i | i) (j | j) <;> simp [Matrix.fromBlocks, Matrix.one_apply]

theorem symJ_det_ne_zero (n : ℕ) (K : Type) [Field K] : (symJ n K).det ≠ 0 := by
  intro h
  have := congrArg Matrix.det (symJ_mul_self n K)
  rw [Matrix.det_mul, h, zero_mul, Matrix.det_neg, Matrix.det_one] at this
  simp at this

theorem statedSp_le_isoGroup (n : ℕ) (K : Type) [Field K] :
    StatedSp n K ≤ isoGroup (symJ n K) :=
  (Subgroup.closure_le _).2 fun _ hA => hA

theorem factorization_three_psp_le {T : Type} [Group T] {n f : ℕ} (hn : n ≤ 4)
    (hmod : StatedClassicalModel T .PSp n 2 f) {p : ℕ} (hp : p.Prime) (hp7 : 7 ≤ p)
    {E : Subgroup T} (hE : IsElementaryAbelian p E) :
    (Nat.card E.normalizerMonoidHom.range).factorization 3 ≤ 1 := by
  obtain ⟨hadm, K, _, _, hK, ⟨e⟩⟩ := hmod
  have hn2 : 2 ≤ n := hadm.2.2.1
  have hf : 1 ≤ f := hadm.2.1
  have hpK : (p : K) ≠ 0 := natCast_ne_zero_of_card_two_pow (by simpa using hK) hp (by omega)
  have hp2 : p % 2 = 1 := hp.eq_two_or_odd.resolve_left (by omega)
  refine factorization_three_le_one_of_matrix_model_form (StatedSp n K) e hp hp2 hpK
    (d := 2) ?_ ?_ (symJ n K) (symJ_det_ne_zero n K) (fun g hg => statedSp_le_isoGroup n K hg) hE
    (by simp; omega)
  · intro c hc
    have hJ := statedSp_le_isoGroup n K hc
    rw [mem_isoGroup] at hJ
    have h := congrFun (congrFun hJ (Sum.inl ⟨0, by omega⟩)) (Sum.inr ⟨0, by omega⟩)
    refine Units.ext ?_
    rw [Units.val_pow_eq_pow_val, Units.val_one, sq]
    simpa [symJ, Matrix.mul_apply, Matrix.transpose_apply, Matrix.GeneralLinearGroup.coe_scalar,
      Matrix.scalar_apply, Matrix.diagonal_apply, Matrix.fromBlocks, Fintype.sum_sum_type] using h
  · intro h
    have := Nat.le_of_dvd (by norm_num) h
    omega

end CFSG.RankThree.PartOne.N143X
