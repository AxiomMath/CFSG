module

public import CFSG.RankThree.SteinbergR3EEvenQuadraticSL2Fixed
public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.RankThree.Chevalley.SteinbergBNF4NativeA2
public import CFSG.RankThree.Chevalley.SteinbergBUF4B2QuarticDescent

public noncomputable section

namespace CFSG.RankThree.Chevalley

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley Matrix SteinbergBN
open CFSG.RankThree.QuadraticSL2 CFSG.RankThree.Classical CFSG.LocalAnalysis.ComponentInitial

section Block

variable {M : Type} [Field M]

@[expose] def blockSL2Mat (B : Matrix (Fin 2) (Fin 2) M) : Matrix (Fin 3) (Fin 3) M :=
  !![B 0 0, B 0 1, 0; B 1 0, B 1 1, 0; 0, 0, 1]

theorem blockSL2Mat_mul (A B : Matrix (Fin 2) (Fin 2) M) :
    blockSL2Mat (A * B) = blockSL2Mat A * blockSL2Mat B := by
  ext a b
  fin_cases a <;> fin_cases b <;>
    simp [blockSL2Mat, Matrix.mul_apply, Fin.sum_univ_two, Fin.sum_univ_three]

theorem blockSL2Mat_one : blockSL2Mat (1 : Matrix (Fin 2) (Fin 2) M) = 1 := by
  ext a b
  fin_cases a <;> fin_cases b <;> simp [blockSL2Mat]

theorem det_blockSL2Mat (B : Matrix (Fin 2) (Fin 2) M) : (blockSL2Mat B).det = B.det := by
  simp [blockSL2Mat, Matrix.det_fin_three, Matrix.det_fin_two]

@[expose] def blockSL2MatHom : SL2 M →* Matrix.SpecialLinearGroup (Fin 3) M where
  toFun B := ⟨blockSL2Mat (B : Matrix (Fin 2) (Fin 2) M), by rw [det_blockSL2Mat]; exact B.2⟩
  map_one' := Subtype.ext blockSL2Mat_one
  map_mul' A B := Subtype.ext (blockSL2Mat_mul (A : Matrix (Fin 2) (Fin 2) M) B)

theorem unitary_blockSL2Mat (σ : M ≃+* M) {B : Matrix (Fin 2) (Fin 2) M}
    (hB : (B.map σ)ᵀ * B = 1) : ((blockSL2Mat B).map σ)ᵀ * blockSL2Mat B = 1 := by
  have e : ((blockSL2Mat B).map σ)ᵀ * blockSL2Mat B = blockSL2Mat ((B.map σ)ᵀ * B) := by
    ext a b
    fin_cases a <;> fin_cases b <;>
      simp [blockSL2Mat, Matrix.mul_apply, Fin.sum_univ_two, Fin.sum_univ_three]
  rw [e, hB, blockSL2Mat_one]

variable [CharP M 2]

theorem f4A2Equiv_rootSL2_left (κ : F4A2Kind) (B : SL2 M) :
    ((f4A2Equiv M κ ⟨_, rootSL2_single_mem_subsystemGroup (left_mem_pair κ.i κ.j) B⟩ :
      Matrix.SpecialLinearGroup (Fin 3) M) : Matrix (Fin 3) (Fin 3) M) =
        blockSL2Mat (B : Matrix (Fin 2) (Fin 2) M) := by
  obtain ⟨hgen, -⟩ := F4_native_long_and_short_A2_faithful_SL3_all_characteristics M κ
  let ρ' : SL2 M →* subsystemGroup Tag.F4 M {κ.i, κ.j} :=
    { toFun := fun A => ⟨_, rootSL2_single_mem_subsystemGroup (left_mem_pair κ.i κ.j) A⟩
      map_one' := Subtype.ext (map_one _)
      map_mul' := fun A A' => Subtype.ext (map_mul _ A A') }
  have h : (f4A2Equiv M κ).toMonoidHom.comp ρ' = blockSL2MatHom := by
    refine MonoidHom.eq_of_eqOn_dense sl2_closure_upper_lower ?_
    rintro _ (⟨c, rfl⟩ | ⟨c, rfl⟩)
    · have e : ρ' (sl2Upper M c) = qx (left_mem_pair κ.i κ.j) c := Subtype.ext (by
        change rootSL2 Tag.F4 M (Pi.single κ.i 1) (uSL c) = xUnit Tag.F4 M κ.i c
        rw [rootSL2_uSL_of_charTwo (isRoot_single _ κ.i), pinnedX_single])
      apply Subtype.ext
      change ((f4A2Equiv M κ (ρ' (sl2Upper M c)) : Matrix.SpecialLinearGroup (Fin 3) M) :
        Matrix (Fin 3) (Fin 3) M) = blockSL2Mat (sl2Upper M c : Matrix (Fin 2) (Fin 2) M)
      rw [e, (hgen c).1]
      ext a b
      fin_cases a <;> fin_cases b <;> simp [blockSL2Mat, sl2Upper]
    · have e : ρ' (sl2Lower M c) = qy (left_mem_pair κ.i κ.j) c := Subtype.ext (by
        change rootSL2 Tag.F4 M (Pi.single κ.i 1) (vSL c) = yUnit Tag.F4 M κ.i c
        rw [rootSL2_vSL_of_charTwo (isRoot_single _ κ.i), pinnedX_neg_single])
      apply Subtype.ext
      change ((f4A2Equiv M κ (ρ' (sl2Lower M c)) : Matrix.SpecialLinearGroup (Fin 3) M) :
        Matrix (Fin 3) (Fin 3) M) = blockSL2Mat (sl2Lower M c : Matrix (Fin 2) (Fin 2) M)
      rw [e, (hgen c).2.1]
      ext a b
      fin_cases a <;> fin_cases b <;> simp [blockSL2Mat, sl2Lower]
  exact congrArg (fun φ : SL2 M →* Matrix.SpecialLinearGroup (Fin 3) M =>
    ((φ B : Matrix.SpecialLinearGroup (Fin 3) M) : Matrix (Fin 3) (Fin 3) M)) h

end Block

section Swap

variable {L : Type} [Field L]

@[expose] def swapGL2 : GL (Fin 2) L :=
  ⟨!![0, 1; 1, 0], !![0, 1; 1, 0], by
    ext a b
    fin_cases a <;> fin_cases b <;> simp [Matrix.mul_apply, Fin.sum_univ_two], by
    ext a b
    fin_cases a <;> fin_cases b <;> simp [Matrix.mul_apply, Fin.sum_univ_two]⟩

theorem coe_swapGL2 : ((swapGL2 : GL (Fin 2) L) : Matrix (Fin 2) (Fin 2) L) = !![0, 1; 1, 0] :=
  rfl

theorem coe_swapGL2_inv :
    ((swapGL2⁻¹ : GL (Fin 2) L) : Matrix (Fin 2) (Fin 2) L) = !![0, 1; 1, 0] :=
  rfl

theorem swapTwo_mul_mul_swapTwo (X : Matrix (Fin 2) (Fin 2) L) :
    !![0, 1; 1, 0] * X * !![0, 1; 1, 0] = !![X 1 1, X 1 0; X 0 1, X 0 0] := by
  ext a b
  fin_cases a <;> fin_cases b <;>
    simp only [Matrix.mul_apply, Fin.sum_univ_two, Matrix.of_apply, Matrix.cons_val',
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.empty_val',
      Matrix.cons_val_fin_one, zero_mul, mul_zero, one_mul, mul_one, add_zero, zero_add,
      Fin.zero_eta, Fin.mk_one, Fin.isValue]

theorem semilinearConj_swapGL2_involutive (σ : L ≃+* L) (hσ : ∀ c, σ (σ c) = c)
    (A : Matrix.SpecialLinearGroup (Fin 2) L) :
    semilinearConj swapGL2 σ (semilinearConj swapGL2 σ A) = A := by
  apply Subtype.ext
  simp only [semilinearConj, MonoidHom.comp_apply, coe_conjSL,
    Matrix.SpecialLinearGroup.map_apply_coe, RingHom.mapMatrix_apply, coe_swapGL2,
    coe_swapGL2_inv, swapTwo_mul_mul_swapTwo]
  ext a b
  fin_cases a <;> fin_cases b <;> simp [hσ]

theorem unitary_of_semilinearConj_swapGL2_eq [CharP L 2] (σ : L ≃+* L)
    {B : Matrix.SpecialLinearGroup (Fin 2) L} (hB : semilinearConj swapGL2 σ B = B) :
    ((B : Matrix (Fin 2) (Fin 2) L).map σ)ᵀ * (B : Matrix (Fin 2) (Fin 2) L) = 1 := by
  have h := congrArg (fun A : Matrix.SpecialLinearGroup (Fin 2) L =>
    (A : Matrix (Fin 2) (Fin 2) L)) hB
  simp only [semilinearConj, MonoidHom.comp_apply, coe_conjSL,
    Matrix.SpecialLinearGroup.map_apply_coe, RingHom.mapMatrix_apply, coe_swapGL2,
    coe_swapGL2_inv, swapTwo_mul_mul_swapTwo] at h
  have h00 := congrFun (congrFun h 0) 0
  have h01 := congrFun (congrFun h 0) 1
  have h10 := congrFun (congrFun h 1) 0
  have h11 := congrFun (congrFun h 1) 1
  simp only [Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.empty_val', Matrix.cons_val_fin_one, Matrix.map_apply, RingEquiv.coe_toRingHom]
    at h00 h01 h10 h11
  have hdet := B.2
  rw [Matrix.det_fin_two] at hdet
  have h2 : (2 : L) = 0 := CharTwo.two_eq_zero
  ext a b
  fin_cases a <;> fin_cases b <;>
    simp [Matrix.mul_apply, Fin.sum_univ_two, h00, h01, h10, h11]
  · linear_combination hdet +
      (B : Matrix (Fin 2) (Fin 2) L) 0 1 * (B : Matrix (Fin 2) (Fin 2) L) 1 0 * h2
  · linear_combination
      (B : Matrix (Fin 2) (Fin 2) L) 0 1 * (B : Matrix (Fin 2) (Fin 2) L) 1 1 * h2
  · linear_combination
      (B : Matrix (Fin 2) (Fin 2) L) 0 0 * (B : Matrix (Fin 2) (Fin 2) L) 1 0 * h2
  · linear_combination hdet +
      (B : Matrix (Fin 2) (Fin 2) L) 0 1 * (B : Matrix (Fin 2) (Fin 2) L) 1 0 * h2

end Swap

theorem exists_conjSL_rootSL2_mem (K : Type) [Field K] [Finite K] (K₂ : Type) [Field K₂]
    [CharP K₂ 2] [Algebra K K₂] (hdeg : Module.finrank K K₂ = 2) (σ : K₂ ≃+* K₂)
    (hσ : ∀ c, σ c = c ^ Nat.card K) (κ : F4A2Kind) {U : Subgroup (ModGL Tag.F4 K₂)}
    (hU : ∀ v, v ∈ U ↔ ∃ hv : v ∈ subsystemGroup Tag.F4 K₂ {κ.i, κ.j},
      ((f4A2Equiv K₂ κ ⟨v, hv⟩ : Matrix (Fin 3) (Fin 3) K₂).map σ)ᵀ *
        (f4A2Equiv K₂ κ ⟨v, hv⟩ : Matrix (Fin 3) (Fin 3) K₂) = 1) :
    ∃ P : GL (Fin 2) K₂, ∀ A : SL2 K,
      rootSL2 Tag.F4 K₂ (Pi.single κ.i 1)
        (conjSL P (Matrix.SpecialLinearGroup.map (algebraMap K K₂) A)) ∈ U := by
  obtain ⟨-, hord, -⟩ := quadratic_frobenius hdeg σ hσ
  have hσσ : ∀ c, σ (σ c) = c := fun c => by
    have h := congrArg (fun τ : K₂ ≃+* K₂ => τ c) (pow_orderOf_eq_one σ)
    simpa only [hord, pow_two, RingAut.mul_apply, RingAut.one_apply] using h
  obtain ⟨P, -, hfix, -, -⟩ := even_quadratic_semilinear_SL2_fixed_matrix_group K K₂ hdeg σ hσ
    swapGL2 (semilinearConj_swapGL2_involutive σ hσσ)
  refine ⟨P, fun A => (hU _).2 ⟨rootSL2_single_mem_subsystemGroup (left_mem_pair κ.i κ.j) _, ?_⟩⟩
  have hmem : conjSL P (Matrix.SpecialLinearGroup.map (algebraMap K K₂) A) ∈
      (semilinearConj swapGL2 σ).eqLocus (MonoidHom.id _) := by
    rw [hfix]
    exact ⟨_, ⟨A, rfl⟩, rfl⟩
  rw [f4A2Equiv_rootSL2_left κ]
  exact unitary_blockSL2Mat σ (unitary_of_semilinearConj_swapGL2_eq σ hmem)

end CFSG.RankThree.Chevalley
