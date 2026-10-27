module

public import CFSG.RankThree.SteinbergR3ELinearTwoPrimeCentralizer
public import CFSG.CharacterTheory.Wreathed.OddLinearThreeCentralizerCore
public import CFSG.RankThree.SteinbergR3ELinearTwoFieldDescent

public section

namespace CFSG.Quasithin.SteinbergBI

open Matrix CFSG.RankThree.LinearTwo

variable {K : Type} [Field K]

theorem smul_one_add_pow_of_mul_self_eq_zero {n : Type*} [Fintype n] [DecidableEq n]
    {N : Matrix n n K} (hN : N * N = 0) (c : K) (k : ℕ) :
    (c • (1 : Matrix n n K) + N) ^ (k + 1) =
      c ^ (k + 1) • (1 : Matrix n n K) + ((k + 1 : ℕ) * c ^ k : K) • N := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [pow_succ, ih]
    simp only [add_mul, mul_add, smul_mul_assoc, mul_smul_comm, one_mul, mul_one, hN, smul_zero,
      add_zero]
    push_cast
    module

theorem exists_conj_isDiag_of_not_isCyclic [Finite K] (Ā : Subgroup (GL (Fin 2) K))
    (hcomm : ∀ x ∈ Ā, ∀ y ∈ Ā, x * y = y * x) (hcyc : ¬IsCyclic Ā)
    (hchar : (Nat.card Ā : K) ≠ 0) :
    ∃ h : GL (Fin 2) K, ∀ x ∈ Ā,
      ((h * x * h⁻¹ : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K).IsDiag := by
  classical
  have : Finite (GL (Fin 2) K) := inferInstance
  by_cases hsc : ∀ x ∈ Ā, ∃ c : K, (x : Matrix (Fin 2) (Fin 2) K) = c • 1
  · exfalso
    apply hcyc
    have hx : ∀ x : Ā, ((x : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) =
        ((x : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) 0 0 • 1 := fun x => by
      obtain ⟨c, hc⟩ := hsc x x.2
      rw [hc]
      simp
    let φ : Ā →* K :=
      { toFun := fun x => ((x : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) 0 0
        map_one' := by simp
        map_mul' := fun x y => by
          change ((x * y : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) 0 0 = _
          rw [Units.val_mul, hx x, hx y]
          simp [mul_comm] }
    refine isCyclic_of_injective_ringHom φ fun x y hxy => Subtype.ext (Units.ext ?_)
    rw [hx x, hx y]
    rw [show ((x : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) 0 0 =
      ((y : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) 0 0 from hxy]
  push Not at hsc
  obtain ⟨X₀, hX₀, hns⟩ := hsc
  have hcoords : ∀ x ∈ Ā, ∃ a b : K, (x : Matrix (Fin 2) (Fin 2) K) =
      a • (1 : Matrix (Fin 2) (Fin 2) K) + b • (X₀ : Matrix (Fin 2) (Fin 2) K) := by
    intro x hx
    exact exists_eq_smul_one_add_smul hns (by
      rw [← Units.val_mul, hcomm x hx X₀ hX₀, Units.val_mul])
  set L := AlgebraicClosure K
  obtain ⟨r, hr⟩ := exists_charRoot L (X₀ : Matrix (Fin 2) (Fin 2) K)
  have hle : Ā ≤ Subgroup.centralizer ({X₀} : Set (GL (Fin 2) K)) := fun x hx =>
    Subgroup.mem_centralizer_singleton_iff.mpr (hcomm x hx X₀ hX₀)
  obtain ⟨l, hl⟩ : ∃ l : K, algebraMap K L l = r := by
    by_contra hnot
    push Not at hnot
    apply hcyc
    set ψ : Ā →* Lˣ := (evRootHom L hns hr).comp (Subgroup.inclusion hle) with hψ
    refine isCyclic_of_injective_ringHom ((Units.coeHom L).comp ψ) ?_
    rw [injective_iff_map_eq_one]
    intro x hx1
    obtain ⟨a, b, hab⟩ := hcoords x x.2
    have h1 : evRoot L hns r (Subgroup.inclusion hle x) = 1 := by
      have := congrArg Units.val (show ψ x = 1 from Units.val_injective hx1)
      simpa [hψ, evRootHom] using this
    rw [evRoot_eq L hns r _ hab] at h1
    by_cases hb : b = 0
    · subst hb
      have ha : a = 1 := (algebraMap K L).injective (by simpa using h1)
      subst ha
      refine Subtype.ext (Units.ext ?_)
      rw [hab]
      simp
    · exfalso
      refine hnot ((1 - a) / b) ?_
      have hbL : algebraMap K L b ≠ 0 := (map_ne_zero (algebraMap K L)).mpr hb
      rw [map_div₀, map_sub, map_one, div_eq_iff hbL]
      linear_combination -h1
  have hlK : l ^ 2 - (X₀ : Matrix (Fin 2) (Fin 2) K).trace * l +
      (X₀ : Matrix (Fin 2) (Fin 2) K).det = 0 := by
    apply (algebraMap K L).injective
    rw [map_zero, ← hr, ← hl]
    simp only [map_add, map_sub, map_mul, map_pow]
  set μ := (X₀ : Matrix (Fin 2) (Fin 2) K).trace - l with hμ
  have hμK : μ ^ 2 - (X₀ : Matrix (Fin 2) (Fin 2) K).trace * μ +
      (X₀ : Matrix (Fin 2) (Fin 2) K).det = 0 := by
    rw [hμ]
    linear_combination hlK
  have hlμ : l ≠ μ := by
    intro hlμ
    have htr : (X₀ : Matrix (Fin 2) (Fin 2) K).trace = 2 * l := by
      rw [hμ] at hlμ
      linear_combination -hlμ
    have hdet : (X₀ : Matrix (Fin 2) (Fin 2) K).det = l ^ 2 := by
      linear_combination hlK + l * htr
    set N := (X₀ : Matrix (Fin 2) (Fin 2) K) - l • (1 : Matrix (Fin 2) (Fin 2) K) with hN
    have hN2 : N * N = 0 := by
      have hch := mul_self_eq_trace_smul_sub_det_smul (X₀ : Matrix (Fin 2) (Fin 2) K)
      rw [htr, hdet] at hch
      rw [hN, sub_mul, mul_sub, mul_sub, hch, smul_mul_smul_comm, one_mul, smul_one_mul,
        mul_smul_one]
      module
    have hX : (X₀ : Matrix (Fin 2) (Fin 2) K) = l • (1 : Matrix (Fin 2) (Fin 2) K) + N := by
      rw [hN]
      abel
    set n := Nat.card Ā with hn
    have hnpos : 0 < n := Nat.card_pos
    have hpow : (X₀ : Matrix (Fin 2) (Fin 2) K) ^ n = 1 := by
      have h1 : (⟨X₀, hX₀⟩ : Ā) ^ n = 1 := pow_card_eq_one'
      have h2 := congrArg (fun x : Ā => ((x : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K)) h1
      simpa using h2
    obtain ⟨k, hk⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
    rw [hX, hk, smul_one_add_pow_of_mul_self_eq_zero hN2] at hpow
    have hl0 : l ≠ 0 := by
      intro hl0
      exact (X₀ : GL (Fin 2) K).det_ne_zero (by rw [hdet, hl0]; ring)
    have hcoef : ((k + 1 : ℕ) * l ^ k : K) ≠ 0 := by
      refine mul_ne_zero ?_ (pow_ne_zero _ hl0)
      rw [← hk]
      exact hchar
    have hNs : N =
        ((1 - l ^ (k + 1)) / ((k + 1 : ℕ) * l ^ k : K)) • (1 : Matrix (Fin 2) (Fin 2) K) := by
      have h3 : ((k + 1 : ℕ) * l ^ k : K) • N =
          (1 - l ^ (k + 1)) • (1 : Matrix (Fin 2) (Fin 2) K) := by
        rw [sub_smul, one_smul]
        exact eq_sub_of_add_eq' hpow
      rw [div_eq_inv_mul, mul_smul, ← h3, smul_smul, inv_mul_cancel₀ hcoef, one_smul]
    set e := (1 - l ^ (k + 1)) / ((k + 1 : ℕ) * l ^ k : K) with he
    have he0 : e = 0 := by
      have h4 := congrArg (fun M : Matrix (Fin 2) (Fin 2) K => M 0 0) hN2
      rw [hNs] at h4
      simpa [sq] using h4
    apply hns l
    rw [hX, hNs, he0, zero_smul, add_zero]
  obtain ⟨v, hv0, hv⟩ : ∃ v : Fin 2 → K, v ≠ 0 ∧
      ((X₀ : Matrix (Fin 2) (Fin 2) K) - l • (1 : Matrix (Fin 2) (Fin 2) K)) *ᵥ v = 0 :=
    Matrix.exists_mulVec_eq_zero_iff.mpr (by
      rw [Matrix.det_fin_two]
      simp only [Matrix.sub_apply, Matrix.smul_apply, Matrix.one_apply_eq,
        Matrix.one_apply_ne (show (0 : Fin 2) ≠ 1 by decide),
        Matrix.one_apply_ne (show (1 : Fin 2) ≠ 0 by decide), smul_eq_mul, mul_one, mul_zero,
        sub_zero]
      rw [Matrix.trace_fin_two, Matrix.det_fin_two] at hlK
      linear_combination hlK)
  obtain ⟨w, hw0, hw⟩ : ∃ w : Fin 2 → K, w ≠ 0 ∧
      ((X₀ : Matrix (Fin 2) (Fin 2) K) - μ • (1 : Matrix (Fin 2) (Fin 2) K)) *ᵥ w = 0 :=
    Matrix.exists_mulVec_eq_zero_iff.mpr (by
      rw [Matrix.det_fin_two]
      simp only [Matrix.sub_apply, Matrix.smul_apply, Matrix.one_apply_eq,
        Matrix.one_apply_ne (show (0 : Fin 2) ≠ 1 by decide),
        Matrix.one_apply_ne (show (1 : Fin 2) ≠ 0 by decide), smul_eq_mul, mul_one, mul_zero,
        sub_zero]
      rw [Matrix.trace_fin_two, Matrix.det_fin_two] at hμK
      linear_combination hμK)
  have hXv : (X₀ : Matrix (Fin 2) (Fin 2) K) *ᵥ v = l • v := by
    rw [Matrix.sub_mulVec, sub_eq_zero, Matrix.smul_mulVec, Matrix.one_mulVec] at hv
    exact hv
  have hXw : (X₀ : Matrix (Fin 2) (Fin 2) K) *ᵥ w = μ • w := by
    rw [Matrix.sub_mulVec, sub_eq_zero, Matrix.smul_mulVec, Matrix.one_mulVec] at hw
    exact hw
  set Q : Matrix (Fin 2) (Fin 2) K := Matrix.of ![![v 0, w 0], ![v 1, w 1]] with hQ
  have hXQ : (X₀ : Matrix (Fin 2) (Fin 2) K) * Q = Q * diagonal ![l, μ] := by
    have e0 := congrFun hXv 0
    have e1 := congrFun hXv 1
    have f0 := congrFun hXw 0
    have f1 := congrFun hXw 1
    simp only [Matrix.mulVec, dotProduct, Fin.sum_univ_two, Pi.smul_apply, smul_eq_mul] at e0 e1
    simp only [Matrix.mulVec, dotProduct, Fin.sum_univ_two, Pi.smul_apply, smul_eq_mul] at f0 f1
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [hQ, Matrix.mul_apply, Fin.sum_univ_two] <;>
      first
        | linear_combination e0
        | linear_combination e1
        | linear_combination f0
        | linear_combination f1
  have hdetQ : Q.det ≠ 0 := by
    intro h0
    obtain ⟨c, hc0, hc⟩ := Matrix.exists_mulVec_eq_zero_iff.mpr h0
    have hcomb : c 0 • v + c 1 • w = 0 := by
      ext i
      have := congrFun hc i
      fin_cases i <;>
        simp [hQ, Matrix.mulVec, dotProduct, Fin.sum_univ_two] at this ⊢ <;>
        linear_combination this
    have h2 : (c 0 * l) • v + (c 1 * μ) • w = 0 := by
      have := congrArg (fun u => (X₀ : Matrix (Fin 2) (Fin 2) K) *ᵥ u) hcomb
      simpa [Matrix.mulVec_add, Matrix.mulVec_smul, hXv, hXw, smul_smul] using this
    have h3 : (c 1 * (μ - l)) • w = 0 := by
      have e : (c 1 * (μ - l)) • w = ((c 0 * l) • v + (c 1 * μ) • w) - l • (c 0 • v + c 1 • w) := by
        module
      rw [e, h2, hcomb, smul_zero, sub_zero]
    have hc1 : c 1 = 0 := by
      rcases smul_eq_zero.mp h3 with h | h
      · exact (mul_eq_zero.mp h).resolve_right (sub_ne_zero.mpr hlμ.symm)
      · exact absurd h hw0
    have hc0' : c 0 = 0 := by
      rw [hc1, zero_smul, add_zero] at hcomb
      exact (smul_eq_zero.mp hcomb).resolve_right hv0
    apply hc0
    ext i
    fin_cases i
    · exact hc0'
    · exact hc1
  have hQu : IsUnit Q.det := isUnit_iff_ne_zero.mpr hdetQ
  refine ⟨(Matrix.nonsingInvUnit Q hQu)⁻¹, fun x hx => ?_⟩
  obtain ⟨a, b, hab⟩ := hcoords x hx
  have hQinv : Q⁻¹ * Q = 1 := Matrix.nonsing_inv_mul Q hQu
  have hcoe : ((Matrix.nonsingInvUnit Q hQu : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) = Q := rfl
  have key : (((Matrix.nonsingInvUnit Q hQu)⁻¹ * x * (Matrix.nonsingInvUnit Q hQu)⁻¹⁻¹ :
      GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) = a • 1 + b • diagonal ![l, μ] := by
    rw [inv_inv, Units.val_mul, Units.val_mul, Matrix.coe_units_inv, hcoe,
      hab, Matrix.mul_add, Matrix.add_mul, Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_smul,
      Matrix.smul_mul, Matrix.mul_one, hQinv, Matrix.mul_assoc, hXQ, ← Matrix.mul_assoc, hQinv,
      Matrix.one_mul]
  rw [key]
  exact (Matrix.isDiag_one.smul a).add ((Matrix.isDiag_diagonal _).smul b)

open CFSG.Wreathed.OddLinearThreeCentralizerCore (matrixAction matrixAction_finrank
  matrixAction_involutive minusSpace plusSpace involution_spaces_isCompl) in
theorem exists_conj_eq_negNegOne [Finite K] (hK : Odd (Nat.card K))
    {z : Matrix.SpecialLinearGroup (Fin 3) K} (hz : orderOf z = 2) :
    ∃ g : GL (Fin 3) K, (g : Matrix (Fin 3) (Fin 3) K) * (z : Matrix (Fin 3) (Fin 3) K) *
      ((g⁻¹ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) = diagonal ![-1, -1, 1] := by
  classical
  set f := (matrixAction K z).toLinearMap with hf
  obtain ⟨hdm, hdp⟩ := matrixAction_finrank K hK z hz
  have hc := involution_spaces_isCompl
    (CFSG.Wreathed.OddLinearThreeCentralizerCore.two_ne_zero K hK) f
    (matrixAction_involutive K z hz)
  let bm : Module.Basis (Fin 2) K (minusSpace f) := Module.finBasisOfFinrankEq K _ hdm
  let bp : Module.Basis (Fin 1) K (plusSpace f) := Module.finBasisOfFinrankEq K _ hdp
  let b : Module.Basis (Fin 3) K (Fin 3 → K) :=
    ((bm.prod bp).map (Submodule.prodEquivOfIsCompl _ _ hc)).reindex finSumFinEquiv
  have hbm : ∀ i : Fin 2, b (Fin.castAdd 1 i) = (bm i : Fin 3 → K) := by
    intro i
    rw [Module.Basis.reindex_apply, finSumFinEquiv_symm_apply_castAdd, Module.Basis.map_apply,
      Submodule.coe_prodEquivOfIsCompl', Module.Basis.prod_apply_inl_fst,
      Module.Basis.prod_apply_inl_snd, Submodule.coe_zero, add_zero]
  have hbp : b (Fin.natAdd 2 (0 : Fin 1)) = (bp 0 : Fin 3 → K) := by
    rw [Module.Basis.reindex_apply, finSumFinEquiv_symm_apply_natAdd, Module.Basis.map_apply,
      Submodule.coe_prodEquivOfIsCompl', Module.Basis.prod_apply_inr_fst,
      Module.Basis.prod_apply_inr_snd, Submodule.coe_zero, zero_add]
  have hb : ∀ j, f (b j) = (![-1, -1, 1] : Fin 3 → K) j • b j := by
    intro j
    fin_cases j
    · have h := Module.End.mem_eigenspace_iff.mp (bm 0).2
      change f (b (Fin.castAdd 1 0)) = (-1 : K) • b (Fin.castAdd 1 0)
      rw [hbm]
      exact h
    · have h := Module.End.mem_eigenspace_iff.mp (bm 1).2
      change f (b (Fin.castAdd 1 1)) = (-1 : K) • b (Fin.castAdd 1 1)
      rw [hbm]
      exact h
    · have h := Module.End.mem_eigenspace_iff.mp (bp 0).2
      change f (b (Fin.natAdd 2 (0 : Fin 1))) = (1 : K) • b (Fin.natAdd 2 (0 : Fin 1))
      rw [hbp]
      exact h
  have hmat : LinearMap.toMatrix b b f = diagonal ![-1, -1, 1] := by
    ext i j
    rw [LinearMap.toMatrix_apply, hb j, map_smul, Module.Basis.repr_self, Finsupp.smul_apply,
      Finsupp.single_apply, diagonal_apply]
    by_cases hij : i = j
    · subst hij
      simp
    · simp [hij, Ne.symm hij]
  set M := (Pi.basisFun K (Fin 3)).toMatrix b with hM
  set M' := b.toMatrix (Pi.basisFun K (Fin 3)) with hM'
  have h1 : M' * M = 1 := b.toMatrix_mul_toMatrix_flip _
  have h2 : M * M' = 1 := (Pi.basisFun K (Fin 3)).toMatrix_mul_toMatrix_flip b
  have hzM : (z : Matrix (Fin 3) (Fin 3) K) = M * diagonal ![-1, -1, 1] * M' := by
    have := basis_toMatrix_mul_linearMap_toMatrix_mul_basis_toMatrix
      (b := Pi.basisFun K (Fin 3)) (c := Pi.basisFun K (Fin 3)) (b' := b) (c' := b) f
    rw [hmat, LinearMap.toMatrix_eq_toMatrix', hf] at this
    rw [← hM, ← hM'] at this
    rw [this]
    change _ = LinearMap.toMatrix' (Matrix.SpecialLinearGroup.toLin' z).toLinearMap
    rw [Matrix.SpecialLinearGroup.toLin'_to_linearMap, LinearMap.toMatrix'_toLin']
  refine ⟨⟨M', M, h1, h2⟩, ?_⟩
  change M' * (z : Matrix (Fin 3) (Fin 3) K) * M = _
  rw [hzM, ← Matrix.mul_assoc, ← Matrix.mul_assoc, h1, Matrix.one_mul, Matrix.mul_assoc, h1,
    Matrix.mul_one]

theorem block_zero_of_commute (h2 : (2 : K) ≠ 0) {N : Matrix (Fin 3) (Fin 3) K}
    (h : N * diagonal ![-1, -1, 1] = diagonal ![-1, -1, 1] * N) :
    N 0 2 = 0 ∧ N 1 2 = 0 ∧ N 2 0 = 0 ∧ N 2 1 = 0 := by
  have e : ∀ i j, N i j * (![-1, -1, 1] : Fin 3 → K) j =
      (![-1, -1, 1] : Fin 3 → K) i * N i j := fun i j => by
    have := congrFun (congrFun h i) j
    rwa [mul_diagonal, diagonal_mul] at this
  have h02 := e 0 2
  have h12 := e 1 2
  have h20 := e 2 0
  have h21 := e 2 1
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons,
    Matrix.tail_cons, mul_one, one_mul, mul_neg, neg_mul] at h02 h12 h20 h21
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact (mul_eq_zero.mp (by linear_combination h02 : (2 : K) * N 0 2 = 0)).resolve_left h2
  · exact (mul_eq_zero.mp (by linear_combination h12 : (2 : K) * N 1 2 = 0)).resolve_left h2
  · exact (mul_eq_zero.mp (by linear_combination -h20 : (2 : K) * N 2 0 = 0)).resolve_left h2
  · exact (mul_eq_zero.mp (by linear_combination -h21 : (2 : K) * N 2 1 = 0)).resolve_left h2

@[expose] def ulBlock (N : Matrix (Fin 3) (Fin 3) K) : Matrix (Fin 2) (Fin 2) K :=
  !![N 0 0, N 0 1; N 1 0, N 1 1]

@[expose] def blockDiag (X : Matrix (Fin 2) (Fin 2) K) (c : K) : Matrix (Fin 3) (Fin 3) K :=
  !![X 0 0, X 0 1, 0; X 1 0, X 1 1, 0; 0, 0, c]

theorem ulBlock_mul {N N' : Matrix (Fin 3) (Fin 3) K} (h0 : N 0 2 = 0) (h1 : N 1 2 = 0) :
    ulBlock (N * N') = ulBlock N * ulBlock N' := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [ulBlock, Matrix.mul_apply, Fin.sum_univ_three, Fin.sum_univ_two, h0, h1]

theorem ulBlock_one : ulBlock (1 : Matrix (Fin 3) (Fin 3) K) = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [ulBlock]

theorem eq_blockDiag {N : Matrix (Fin 3) (Fin 3) K}
    (h : N 0 2 = 0 ∧ N 1 2 = 0 ∧ N 2 0 = 0 ∧ N 2 1 = 0) : N = blockDiag (ulBlock N) (N 2 2) := by
  obtain ⟨h02, h12, h20, h21⟩ := h
  ext i j
  fin_cases i <;> fin_cases j <;> simp [blockDiag, ulBlock, h02, h12, h20, h21]

theorem blockDiag_mul (X Y : Matrix (Fin 2) (Fin 2) K) (c d : K) :
    blockDiag X c * blockDiag Y d = blockDiag (X * Y) (c * d) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [blockDiag, Matrix.mul_apply, Fin.sum_univ_three, Fin.sum_univ_two]

theorem blockDiag_one : blockDiag (1 : Matrix (Fin 2) (Fin 2) K) 1 = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [blockDiag]

theorem det_blockDiag (X : Matrix (Fin 2) (Fin 2) K) (c : K) :
    (blockDiag X c).det = X.det * c := by
  rw [blockDiag, Matrix.det_fin_three, Matrix.det_fin_two]
  simp
  ring

theorem blockDiag_negNegOne :
    blockDiag (-1 : Matrix (Fin 2) (Fin 2) K) 1 = diagonal ![-1, -1, 1] := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [blockDiag]

theorem isDiag_blockDiag {X : Matrix (Fin 2) (Fin 2) K} (hX : X.IsDiag) (c : K) :
    (blockDiag X c).IsDiag := by
  have h01 : X 0 1 = 0 := hX (by decide)
  have h10 : X 1 0 = 0 := hX (by decide)
  intro i j hij
  fin_cases i <;> fin_cases j <;> simp_all [blockDiag]

theorem exists_conj_diagonal_of_commute [Finite K] (hK : Odd (Nat.card K))
    {z : Matrix.SpecialLinearGroup (Fin 3) K} (hz : orderOf z = 2)
    (A : Subgroup (Matrix.SpecialLinearGroup (Fin 3) K)) (hAz : ∀ a ∈ A, a * z = z * a)
    (hAcomm : ∀ a ∈ A, ∀ b ∈ A, a * b = b * a) (hAcyc : ¬IsCyclic A)
    (hAchar : (Nat.card A : K) ≠ 0) :
    ∃ g : GL (Fin 3) K, (g : Matrix (Fin 3) (Fin 3) K) * (z : Matrix (Fin 3) (Fin 3) K) *
        ((g⁻¹ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) = diagonal ![-1, -1, 1] ∧
      ∀ a ∈ A, ((g : Matrix (Fin 3) (Fin 3) K) * (a : Matrix (Fin 3) (Fin 3) K) *
        ((g⁻¹ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K)).IsDiag := by
  classical
  have h2 := CFSG.Wreathed.OddLinearThreeCentralizerCore.two_ne_zero K hK
  obtain ⟨g₁, hg₁⟩ := exists_conj_eq_negNegOne hK hz
  set G₁ : Matrix (Fin 3) (Fin 3) K := ((g₁ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K)
    with hG₁
  set G₁' : Matrix (Fin 3) (Fin 3) K := ((g₁⁻¹ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K)
    with hG₁'
  have hG : G₁' * G₁ = 1 := by
    rw [hG₁, hG₁', ← Units.val_mul, inv_mul_cancel, Units.val_one]
  have hG2 : G₁ * G₁' = 1 := by
    rw [hG₁, hG₁', ← Units.val_mul, mul_inv_cancel, Units.val_one]
  set C : Matrix.SpecialLinearGroup (Fin 3) K → Matrix (Fin 3) (Fin 3) K :=
    fun x => G₁ * (x : Matrix (Fin 3) (Fin 3) K) * G₁' with hC
  have hCmul : ∀ x y, C (x * y) = C x * C y := by
    intro x y
    show G₁ * ((x * y : Matrix.SpecialLinearGroup (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) * G₁' =
      G₁ * (x : Matrix (Fin 3) (Fin 3) K) * G₁' * (G₁ * (y : Matrix (Fin 3) (Fin 3) K) * G₁')
    rw [Matrix.SpecialLinearGroup.coe_mul]
    simp only [Matrix.mul_assoc]
    rw [← Matrix.mul_assoc G₁' G₁, hG, Matrix.one_mul]
  have hCone : C 1 = 1 := by
    show G₁ * ((1 : Matrix.SpecialLinearGroup (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) * G₁' = 1
    rw [Matrix.SpecialLinearGroup.coe_one, Matrix.mul_one, hG₁, hG₁', ← Units.val_mul,
      mul_inv_cancel, Units.val_one]
  have hCleft : ∀ x, G₁' * C x * G₁ = (x : Matrix (Fin 3) (Fin 3) K) := by
    intro x
    show G₁' * (G₁ * (x : Matrix (Fin 3) (Fin 3) K) * G₁') * G₁ = _
    simp only [Matrix.mul_assoc]
    rw [hG, Matrix.mul_one, ← Matrix.mul_assoc, hG, Matrix.one_mul]
  have hCinj : ∀ x y, C x = C y → x = y := by
    intro x y hxy
    have h1 := congrArg (fun M => G₁' * M * G₁) hxy
    simp only [hCleft] at h1
    exact Subtype.ext h1
  have hCz : ∀ a ∈ A, C a * diagonal ![-1, -1, 1] = diagonal ![-1, -1, 1] * C a := by
    intro a ha
    rw [← hg₁]
    change C a * C z = C z * C a
    rw [← hCmul, ← hCmul, hAz a ha]
  have hblk := fun (a : Matrix.SpecialLinearGroup (Fin 3) K) (ha : a ∈ A) =>
    block_zero_of_commute h2 (hCz a ha)
  have hval_inv : ∀ a : A, ulBlock (C a) * ulBlock (C (a⁻¹ : A)) = 1 := by
    intro a
    rw [← ulBlock_mul (hblk a a.2).1 (hblk a a.2).2.1, ← hCmul]
    simp [hCone, ulBlock_one]
  have hinv_val : ∀ a : A, ulBlock (C (a⁻¹ : A)) * ulBlock (C a) = 1 := by
    intro a
    rw [← ulBlock_mul (hblk _ (a⁻¹ : A).2).1 (hblk _ (a⁻¹ : A).2).2.1, ← hCmul]
    simp [hCone, ulBlock_one]
  let ψ : A →* GL (Fin 2) K :=
    { toFun := fun a => ⟨ulBlock (C a), ulBlock (C (a⁻¹ : A)), hval_inv a, hinv_val a⟩
      map_one' := Units.ext (by simp [hCone, ulBlock_one])
      map_mul' := fun a b => Units.ext (by
        change ulBlock (C ((a * b : A) : Matrix.SpecialLinearGroup (Fin 3) K)) =
          ulBlock (C a) * ulBlock (C b)
        rw [Subgroup.coe_mul, hCmul, ulBlock_mul (hblk a a.2).1 (hblk a a.2).2.1]) }
  have hψ : ∀ a : A, ((ψ a : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) = ulBlock (C a) :=
    fun _ => rfl
  have hψinj : Function.Injective ψ := by
    rw [injective_iff_map_eq_one]
    intro a ha
    have hu : ulBlock (C a) = 1 := by rw [← hψ, ha, Units.val_one]
    have hdet : (C a).det = 1 := by
      show (G₁ * ((a : Matrix.SpecialLinearGroup (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) *
        G₁').det = 1
      rw [Matrix.det_mul, Matrix.det_mul, (a : Matrix.SpecialLinearGroup (Fin 3) K).2, mul_one,
        ← Matrix.det_mul, hG2, Matrix.det_one]
    have heq := eq_blockDiag (hblk a a.2)
    rw [heq, hu, det_blockDiag, Matrix.det_one, one_mul] at hdet
    rw [hu, hdet, blockDiag_one, ← hCone] at heq
    exact Subtype.ext (hCinj _ _ heq)
  have hrcomm : ∀ x ∈ ψ.range, ∀ y ∈ ψ.range, x * y = y * x := by
    rintro _ ⟨a, rfl⟩ _ ⟨b, rfl⟩
    rw [← map_mul, ← map_mul]
    exact congrArg ψ (Subtype.ext (hAcomm a a.2 b b.2))
  have hrcyc : ¬IsCyclic ψ.range := fun h =>
    hAcyc (isCyclic_of_injective ψ.rangeRestrict
      (MonoidHom.rangeRestrict_injective_iff.mpr hψinj))
  have hrcard : (Nat.card ψ.range : K) ≠ 0 := by
    rwa [← Nat.card_congr (MonoidHom.ofInjective hψinj).toEquiv]
  obtain ⟨h, hh⟩ := exists_conj_isDiag_of_not_isCyclic ψ.range hrcomm hrcyc hrcard
  have hhinv : (h : Matrix (Fin 2) (Fin 2) K) * ((h⁻¹ : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) =
      1 := by rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
  have hinvh : ((h⁻¹ : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) * (h : Matrix (Fin 2) (Fin 2) K) =
      1 := by rw [← Units.val_mul, inv_mul_cancel, Units.val_one]
  let g₂ : GL (Fin 3) K :=
    ⟨blockDiag h 1, blockDiag ((h⁻¹ : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) 1,
      by rw [blockDiag_mul, hhinv, one_mul, blockDiag_one],
      by rw [blockDiag_mul, hinvh, one_mul, blockDiag_one]⟩
  set G₂ : Matrix (Fin 3) (Fin 3) K := ((g₂ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) with hG₂
  set G₂' : Matrix (Fin 3) (Fin 3) K := ((g₂⁻¹ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K)
    with hG₂'
  have hconj : ∀ M : Matrix (Fin 3) (Fin 3) K,
      (((g₂ * g₁ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) * M *
        (((g₂ * g₁)⁻¹ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K)) = G₂ * (G₁ * M * G₁') * G₂' := by
    intro M
    rw [_root_.mul_inv_rev, Units.val_mul, Units.val_mul]
    simp only [Matrix.mul_assoc]
    rfl
  refine ⟨g₂ * g₁, ?_, fun a ha => ?_⟩
  · rw [hconj, hg₁, ← blockDiag_negNegOne]
    change blockDiag h 1 * blockDiag (-1) 1 *
      blockDiag ((h⁻¹ : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) 1 = blockDiag (-1) 1
    rw [blockDiag_mul, blockDiag_mul, Matrix.mul_neg, Matrix.mul_one, Matrix.neg_mul, hhinv,
      one_mul, one_mul]
  · rw [hconj]
    change (G₂ * C a * G₂').IsDiag
    rw [eq_blockDiag (hblk a ha)]
    change (blockDiag h 1 * blockDiag (ulBlock (C a)) (C a 2 2) *
      blockDiag ((h⁻¹ : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) 1).IsDiag
    rw [blockDiag_mul, blockDiag_mul, one_mul, mul_one]
    apply isDiag_blockDiag
    have := hh (ψ ⟨a, ha⟩) ⟨⟨a, ha⟩, rfl⟩
    rwa [Units.val_mul, Units.val_mul, hψ] at this

end CFSG.Quasithin.SteinbergBI
