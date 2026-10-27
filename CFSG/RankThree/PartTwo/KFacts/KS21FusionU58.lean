module

public import CFSG.RankThree.PartTwo.KFacts.KS21FusionCore
public import CFSG.RankThree.PartTwo.KFacts.KS21FusionDFT
public import CFSG.RankThree.PartTwo.KFacts.KS21U58
public import CFSG.RankThree.Classical2.SLnRootPermutingFixedGroups

public noncomputable section

namespace CFSG.RankThree.PartTwo.KFacts.KS21.U58

open Matrix CFSG.RankThree.PartTwo.KFacts.KS21.DFT CFSG.Assembly.RankThreeEven
open CFSG.Assembly.LowTwoRank CFSG.ClassicalGroups.UnitaryFlag

abbrev SUI := StatedSU 5 (2 ^ 3) K

theorem card_units_K : Nat.card Kˣ = 63 := by
  classical
  have := Fintype.ofFinite K
  rw [Nat.card_eq_fintype_card, Fintype.card_units, ← Nat.card_eq_fintype_card,
    GaloisField.card 2 (2 * 3) (by norm_num)]
  norm_num

theorem scalars_eq_bot_SUI : (StatedScalars (Fin 5) K).subgroupOf SUI = ⊥ := by
  rw [eq_bot_iff]
  intro g hg
  rw [Subgroup.mem_subgroupOf, StatedScalars, MonoidHom.mem_range] at hg
  obtain ⟨c, hc⟩ := hg
  have hdet := CFSG.RankThree.Classical2.statedSU_le_ker_det 5 (2 ^ 3) K g.2
  rw [MonoidHom.mem_ker, ← hc, GeneralLinearGroup.det_scalar, Fintype.card_fin] at hdet
  have h63 : c ^ 63 = 1 := by rw [← card_units_K]; exact pow_card_eq_one'
  have hc1 : c = 1 := by
    have hdvd : orderOf c ∣ Nat.gcd 5 63 :=
      Nat.dvd_gcd (orderOf_dvd_of_pow_eq_one hdet) (orderOf_dvd_of_pow_eq_one h63)
    exact orderOf_eq_one_iff.mp (Nat.dvd_one.mp (by simpa using hdvd))
  rw [Subgroup.mem_bot]
  apply Subtype.ext
  rw [← hc, hc1, map_one]
  rfl

@[expose] def equivSUI : projSU 5 2 3 ≃* SUI :=
  (MulEquiv.subgroupCongr (CFSG.RankThree.PartTwo.Census.projImage_statedSU 5 2 3)).symm.trans
    ((CFSG.RankThree.PartTwo.Census.statedProjEquivProjImage _).symm.trans
      ((QuotientGroup.quotientMulEquivOfEq scalars_eq_bot_SUI).trans QuotientGroup.quotientBot))

theorem card_SUI : Nat.card SUI = 3 ^ (8 + 1) * 236583028271349760 := by
  rw [← Nat.card_congr equivSUI.toEquiv, Nat.card_congr equivSU.toEquiv]
  have h := (card_hypSU hK (r := 2) (ε := 1) (by norm_num)).1
  have h' : ((Nat.card SU5 : ℕ) : ℤ) = ((3 ^ (8 + 1) * 236583028271349760 : ℕ) : ℤ) := by
    rw [h]
    decide
  exact_mod_cast h'

@[expose] def blk5 (x : GL (Fin 3) K × Kˣ) : Matrix (Fin 5) (Fin 5) K :=
  Matrix.reindex finSumFinEquiv finSumFinEquiv
    (fromBlocks (x.1 : Matrix (Fin 3) (Fin 3) K) 0 0
      (diagonal ![(x.2 : K), (((GeneralLinearGroup.det x.1 * x.2)⁻¹ : Kˣ) : K)]))

theorem blk5_mul (x y : GL (Fin 3) K × Kˣ) : blk5 (x * y) = blk5 x * blk5 y := by
  simp only [blk5, reindex_apply, submatrix_mul_equiv, fromBlocks_multiply, Prod.fst_mul,
    Prod.snd_mul, Units.val_mul, map_mul, Matrix.mul_zero, Matrix.zero_mul, add_zero, zero_add,
    diagonal_mul_diagonal]
  congr 3
  funext i
  fin_cases i
  · rfl
  · simp only [Fin.mk_one, Matrix.cons_val_one, Matrix.cons_val_zero]
    rw [mul_mul_mul_comm, mul_inv, Units.val_mul]

theorem blk5_one : blk5 (1 : GL (Fin 3) K × Kˣ) = 1 := by
  simp only [blk5, Prod.fst_one, Prod.snd_one, map_one, mul_one, inv_one, Units.val_one]
  rw [show (![1, 1] : Fin 2 → K) = fun _ => 1 by funext i; fin_cases i <;> rfl, diagonal_one,
    fromBlocks_one]
  simp [reindex_apply]

@[expose] def blk5Hom : GL (Fin 3) K × Kˣ →* Matrix (Fin 5) (Fin 5) K where
  toFun := blk5
  map_one' := blk5_one
  map_mul' := blk5_mul

@[expose] def emb5 : GL (Fin 3) K × Kˣ →* GL (Fin 5) K :=
  (Units.map blk5Hom).comp (toUnits : GL (Fin 3) K × Kˣ ≃* (GL (Fin 3) K × Kˣ)ˣ).toMonoidHom

theorem coe_emb5 (x : GL (Fin 3) K × Kˣ) : (emb5 x : Matrix (Fin 5) (Fin 5) K) = blk5 x := rfl

theorem emb5_injective : Function.Injective emb5 := by
  intro x y h
  have h' : blk5 x = blk5 y := by rw [← coe_emb5, ← coe_emb5, h]
  refine Prod.ext (Units.ext ?_) (Units.ext ?_)
  · ext i j
    have := congrFun₂ h' (finSumFinEquiv (m := 3) (n := 2) (Sum.inl i))
      (finSumFinEquiv (m := 3) (n := 2) (Sum.inl j))
    simpa [blk5, reindex_apply] using this
  · have := congrFun₂ h' (finSumFinEquiv (m := 3) (n := 2) (Sum.inr 0))
      (finSumFinEquiv (m := 3) (n := 2) (Sum.inr 0))
    simpa [blk5, reindex_apply] using this

theorem det_blk5 (x : GL (Fin 3) K × Kˣ) : (blk5 x).det = 1 := by
  rw [blk5, det_reindex_self, det_fromBlocks_zero₂₁, det_diagonal, Fin.prod_univ_two]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
  rw [← GeneralLinearGroup.val_det_apply, ← Units.val_mul, ← Units.val_mul, ← mul_assoc,
    mul_inv_cancel, Units.val_one]

theorem det_pow_mul_det {A : Matrix (Fin 3) (Fin 3) K}
    (hA : (A.map (· ^ (2 ^ 3)))ᵀ * A = 1) : A.det ^ (2 ^ 3) * A.det = 1 := by
  have h := congrArg Matrix.det hA
  rw [det_mul, det_transpose, det_one] at h
  have hmap : (A.map (· ^ (2 ^ 3))).det = A.det ^ (2 ^ 3) := by
    have := (iterateFrobenius K 2 3).map_det A
    rw [iterateFrobenius_def] at this
    rw [this, RingHom.mapMatrix_apply]
    congr 1
  rwa [hmap] at h

theorem unitary_blk5 (x : GL (Fin 3) K × Kˣ)
    (hA : ((x.1 : Matrix (Fin 3) (Fin 3) K).map (· ^ (2 ^ 3)))ᵀ * x.1 = 1)
    (hb : (x.2 : K) ^ (2 ^ 3) * x.2 = 1) :
    ((blk5 x).map (· ^ (2 ^ 3)))ᵀ * blk5 x = 1 := by
  have hdet := det_pow_mul_det hA
  have hc : ((((GeneralLinearGroup.det x.1 * x.2)⁻¹ : Kˣ) : K)) ^ (2 ^ 3) *
      (((GeneralLinearGroup.det x.1 * x.2)⁻¹ : Kˣ) : K) = 1 := by
    rw [Units.val_inv_eq_inv_val, Units.val_mul, GeneralLinearGroup.val_det_apply, inv_pow,
      ← mul_inv, mul_pow, mul_mul_mul_comm, hdet, hb, mul_one, inv_one]
  have h0 : ((0 : K) ^ (2 ^ 3)) = 0 := by norm_num
  simp only [blk5, reindex_apply, ← submatrix_map, transpose_submatrix, submatrix_mul_equiv,
    fromBlocks_map, fromBlocks_transpose, fromBlocks_multiply,
    Matrix.map_zero (fun x : K => x ^ (2 ^ 3)) h0,
    diagonal_map (f := fun x : K => x ^ (2 ^ 3)) h0, diagonal_transpose, transpose_zero,
    Matrix.mul_zero, Matrix.zero_mul, add_zero, zero_add, diagonal_mul_diagonal, hA]
  rw [show (fun i => (![(x.2 : K), (((GeneralLinearGroup.det x.1 * x.2)⁻¹ : Kˣ) : K)] i) ^
      (2 ^ 3) * ![(x.2 : K), (((GeneralLinearGroup.det x.1 * x.2)⁻¹ : Kˣ) : K)] i) =
      fun _ => 1 by
    funext i; fin_cases i
    · exact hb
    · exact hc]
  rw [diagonal_one, fromBlocks_one]
  simp

theorem emb5_mem {x : GL (Fin 3) K × Kˣ}
    (hA : ((x.1 : Matrix (Fin 3) (Fin 3) K).map (· ^ (2 ^ 3)))ᵀ * x.1 = 1)
    (hb : (x.2 : K) ^ (2 ^ 3) * x.2 = 1) : emb5 x ∈ SUI :=
  Subgroup.subset_closure ⟨det_blk5 x, unitary_blk5 x hA hb⟩

theorem pow_eight_mul_self {t : Kˣ} (ht : t ^ 9 = 1) : (t : K) ^ (2 ^ 3) * t = 1 := by
  rw [← Units.val_pow_eq_pow_val, ← Units.val_mul, ← pow_succ, show 2 ^ 3 + 1 = 9 from rfl, ht,
    Units.val_one]

theorem unitary_diagGL {t : Fin 3 → Kˣ} (ht : ∀ i, t i ^ 9 = 1) :
    (((TauCeti.diagGL t : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K).map (· ^ (2 ^ 3)))ᵀ *
      (TauCeti.diagGL t : GL (Fin 3) K) = 1 := by
  have h0 : ((0 : K) ^ (2 ^ 3)) = 0 := by norm_num
  rw [TauCeti.diagGL_coe, diagonal_map (f := fun x : K => x ^ (2 ^ 3)) h0, diagonal_transpose,
    diagonal_mul_diagonal, ← diagonal_one]
  congr 1
  funext i
  exact pow_eight_mul_self (ht i)

theorem unitary_permGL3 :
    (((permGL3 : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K).map (· ^ (2 ^ 3)))ᵀ *
      (permGL3 : GL (Fin 3) K) = 1 := by
  rw [coe_permGL3]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [permMat3, Matrix.mul_apply, Fin.sum_univ_three]

theorem dftMat_map {ω : K} (hω : ω ^ 2 + ω + 1 = 0) :
    (dftMat ω).map (· ^ (2 ^ 3)) = dftInvMat ω := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [dftMat, dftInvMat] <;> grind

theorem unitary_dftGL {ω : K} (hω : ω ^ 2 + ω + 1 = 0) :
    (((dftGL two_eq_zero hω : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K).map (· ^ (2 ^ 3)))ᵀ *
      (dftGL two_eq_zero hω : GL (Fin 3) K) = 1 := by
  rw [coe_dftGL, dftMat_map hω]
  have hT : (dftInvMat ω)ᵀ = dftInvMat ω := by
    ext i j
    fin_cases i <;> fin_cases j <;> rfl
  rw [hT, dftInvMat_mul_dftMat two_eq_zero hω]

theorem exists_zeta : ∃ ζ : Kˣ, orderOf ζ = 9 := by
  obtain ⟨γ, hγ⟩ := IsCyclic.exists_ofOrder_eq_natCard (α := Kˣ)
  rw [card_units_K] at hγ
  refine ⟨γ ^ 7, ?_⟩
  rw [orderOf_pow_of_dvd (by norm_num) (by rw [hγ]; norm_num), hγ]

theorem card_V9 : Nat.card ((Fin 3 → ZMod 9) × ZMod 9) = 3 ^ 8 := by
  rw [Nat.card_prod, Nat.card_fun, Nat.card_zmod, Nat.card_fin]
  norm_num

theorem rot9_ne : ∃ v : (Fin 3 → ZMod 9) × ZMod 9, rot9 v ≠ v := by
  have : Fact (1 < 9) := ⟨by norm_num⟩
  obtain ⟨u, hu⟩ := rot3_ne (R := ZMod 9)
  exact ⟨(u, 0), fun h => hu (congrArg Prod.fst h)⟩

theorem three_smul_delta9 : 3 • ((![0, 3, 6], 0) : (Fin 3 → ZMod 9) × ZMod 9) = 0 := by
  rw [Prod.smul_mk, smul_zero, Prod.mk_eq_zero]
  refine ⟨?_, rfl⟩
  funext i
  fin_cases i <;> decide

theorem hasFusionTarget_SUI : HasFusionTarget SUI := by
  obtain ⟨ζ, hζ⟩ := exists_zeta
  have hζ9 : ζ ^ 9 = 1 := by
    have := pow_orderOf_eq_one ζ
    rwa [hζ] at this
  have hω : orderOf (ζ ^ 3) = 3 := by
    rw [orderOf_pow_of_dvd (by norm_num) (by rw [hζ]; norm_num), hζ]
  have hω3 : (ζ ^ 3) ^ 3 = 1 := by
    have := pow_orderOf_eq_one (ζ ^ 3)
    rwa [hω] at this
  have hω1 : ζ ^ 3 ≠ 1 := by
    intro h
    rw [h, orderOf_one] at hω
    norm_num at hω
  have hω' := sq_add_add_one_eq_zero hω3 hω1
  have hτS : ∀ v, emb5 (tau9 hζ9 v) ∈ SUI := by
    intro v
    obtain ⟨⟨u, d⟩, rfl⟩ := Multiplicative.ofAdd.surjective v
    rw [tau9_apply]
    refine emb5_mem (unitary_diagGL fun i => ?_) (pow_eight_mul_self ?_)
    · rw [← pow_mul, mul_comm _ 9, pow_mul, hζ9, one_pow]
    · rw [← pow_mul, mul_comm _ 9, pow_mul, hζ9, one_pow]
  have hb1 : ((1 : Kˣ) : K) ^ (2 ^ 3) * ((1 : Kˣ) : K) = 1 := by simp
  exact hasFusionTarget_of_torus_sub (S := SUI) emb5 emb5_injective (tau9_injective hζ9 hζ) hτS
    (w₀ := (permGL3, 1)) (emb5_mem unitary_permGL3 hb1)
    (by rw [Prod.pow_mk, permGL3_pow_three, one_pow]; rfl) (permGL3_mul_tau9 hζ9) rot9_ne
    card_V9 card_SUI (by norm_num) rot9_norm (g₀ := (dftGL two_eq_zero hω', 1))
    (emb5_mem (unitary_dftGL hω') hb1)
    (fun c hc _ => dftGL_mul_tau9_of_fixed hζ9 two_eq_zero hω' hc) three_smul_delta9
    (dftGL_mul_permGL3_tau9 hζ9 two_eq_zero hω')

theorem hasFusionTarget_projSU : HasFusionTarget (projSU 5 2 3) :=
  hasFusionTarget_SUI.of_mulEquiv equivSUI.symm

end CFSG.RankThree.PartTwo.KFacts.KS21.U58
