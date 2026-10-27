module

public import CFSG.Quasithin.Vol2.Ch12Sec6KGCompPSL2A
public import CFSG.LocalAnalysis.ComponentInitial.LinearHigherAutomorphismGeneration
public import CFSG.LocalAnalysis.ComponentInitial.LinearHigherGraphFieldInvolution
import CFSG.LocalAnalysis.ComponentInitial.SteinbergBUProjectivePlaneCoprimeCentral
import CFSG.LieType.SeitzGeneration.SpFourMix

public section

namespace CFSG.Quasithin.H13.S126C

open Matrix CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.LinearFlag

variable {F : Type} [Field F]

theorem vecMulVec_mul_self {v w : Fin 3 → F} (h : w ⬝ᵥ v = 0) :
    vecMulVec v w * vecMulVec v w = 0 := by
  rw [vecMulVec_mul_vecMulVec, h, zero_smul, vecMulVec_zero]

@[expose] noncomputable def rankOneSL (v w : Fin 3 → F) (h : w ⬝ᵥ v = 0) :
    SpecialLinearGroup (Fin 3) F :=
  ⟨1 + vecMulVec v w, by
    rw [vecMulVec_eq Unit, det_one_add_replicateCol_mul_replicateRow, h, add_zero]⟩

theorem coe_rankOneSL {v w : Fin 3 → F} (h : w ⬝ᵥ v = 0) :
    ((rankOneSL v w h : SpecialLinearGroup (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) =
      1 + vecMulVec v w :=
  rfl

theorem coe_rankOneSL_pow {v w : Fin 3 → F} (h : w ⬝ᵥ v = 0) (n : ℕ) :
    ((rankOneSL v w h ^ n : SpecialLinearGroup (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) =
      1 + (n : F) • vecMulVec v w := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [pow_succ, Matrix.SpecialLinearGroup.coe_mul, ih, coe_rankOneSL, add_mul, mul_add, mul_add,
      one_mul, mul_one, one_mul, smul_mul_assoc, vecMulVec_mul_self h, smul_zero, add_zero]
    push_cast
    rw [add_smul, one_smul]
    abel

theorem coe_rankOneSL_inv {v w : Fin 3 → F} (h : w ⬝ᵥ v = 0) :
    (((rankOneSL v w h)⁻¹ : SpecialLinearGroup (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) =
      1 - vecMulVec v w := by
  have hmul : (1 + vecMulVec v w) * (1 - vecMulVec v w) = 1 := by
    rw [mul_sub, mul_one, add_mul, one_mul, vecMulVec_mul_self h, add_zero]
    abel
  have h1 : rankOneSL v w h * ⟨1 - vecMulVec v w, by
      have := congrArg Matrix.det hmul
      rwa [det_mul, det_one, ← coe_rankOneSL h, (rankOneSL v w h).2, one_mul] at this⟩ = 1 :=
    Subtype.ext hmul
  rw [inv_eq_of_mul_eq_one_right h1]

theorem orderOf_rankOneSL {p : ℕ} [Fact p.Prime] [CharP F p] {v w : Fin 3 → F} (hv : v ≠ 0)
    (hw : w ≠ 0) (h : w ⬝ᵥ v = 0) :
    orderOf (rankOneSL v w h) = p ∧ orderOf (proj 3 F (rankOneSL v w h)) = p := by
  have hN : vecMulVec v w ≠ 0 := vecMulVec_ne_zero hv hw
  have hp1 : rankOneSL v w h ^ p = 1 := Subtype.ext (by
    rw [coe_rankOneSL_pow, CharP.cast_eq_zero, zero_smul, add_zero]
    rfl)
  refine ⟨orderOf_eq_prime hp1 fun h1 => hN ?_, orderOf_eq_prime (by rw [← map_pow, hp1, map_one])
    fun h1 => hN ?_⟩
  · have := congrArg (fun g : SpecialLinearGroup (Fin 3) F => (g : Matrix (Fin 3) (Fin 3) F)) h1
    simpa [coe_rankOneSL] using this
  · rw [← MonoidHom.mem_ker, ker_proj, scalars_eq_center,
      Matrix.SpecialLinearGroup.mem_center_iff] at h1
    obtain ⟨r, -, hr⟩ := h1
    rw [coe_rankOneSL] at hr
    have hN' : vecMulVec v w = (r - 1) • (1 : Matrix (Fin 3) (Fin 3) F) := by
      rw [sub_smul, one_smul, show r • (1 : Matrix (Fin 3) (Fin 3) F) = scalar (Fin 3) r by
        rw [smul_one_eq_diagonal, scalar_apply], hr]
      abel
    have hsq := vecMulVec_mul_self h
    rw [hN', smul_mul_smul_comm, mul_one, smul_eq_zero] at hsq
    rcases hsq with h0 | h0
    · rw [hN', (mul_self_eq_zero.mp h0), zero_smul]
    · exact absurd h0 one_ne_zero

theorem exists_eigen_of_mul_self_eq_one (h2 : (2 : F) ≠ 0) {A : Matrix (Fin 3) (Fin 3) F}
    (hA : A * A = 1) (h1 : A ≠ 1) (hm : A ≠ -1) :
    ∃ v w : Fin 3 → F, v ≠ 0 ∧ w ≠ 0 ∧ A *ᵥ v = v ∧ w ᵥ* A = -w ∧ w ⬝ᵥ v = 0 := by
  obtain ⟨j, hj⟩ : ∃ j, (A + 1) *ᵥ Pi.single j 1 ≠ 0 := by
    by_contra hcon
    push Not at hcon
    apply hm
    rw [eq_neg_iff_add_eq_zero]
    ext i j
    have := congrFun (hcon j) i
    rwa [mulVec_single_one] at this
  obtain ⟨i, hi⟩ : ∃ i, Pi.single i 1 ᵥ* (A - 1) ≠ 0 := by
    by_contra hcon
    push Not at hcon
    apply h1
    rw [← sub_eq_zero]
    ext i j
    have := congrFun (hcon i) j
    rwa [single_one_vecMul] at this
  set v := (A + 1) *ᵥ Pi.single j 1 with hvdef
  set w := Pi.single i 1 ᵥ* (A - 1) with hwdef
  have hv : A *ᵥ v = v := by
    rw [hvdef, mulVec_mulVec, mul_add, hA, mul_one, add_comm]
  have hw : w ᵥ* A = -w := by
    rw [hwdef, vecMul_vecMul, sub_mul, hA, one_mul, ← neg_sub, vecMul_neg]
  refine ⟨v, w, hj, hi, hv, hw, ?_⟩
  have hneg : w ⬝ᵥ v = -(w ⬝ᵥ v) := by
    conv_lhs => rw [← hv]
    rw [dotProduct_mulVec, hw, neg_dotProduct]
  have h2x : (2 : F) * (w ⬝ᵥ v) = 0 := by linear_combination hneg
  exact (mul_eq_zero.mp h2x).resolve_left h2

theorem slConjugation_rankOneSL {B : GL (Fin 3) F} (hB : B * B = 1) {v w : Fin 3 → F}
    (hv : (B : Matrix (Fin 3) (Fin 3) F) *ᵥ v = v) (hw : w ᵥ* (B : Matrix (Fin 3) (Fin 3) F) = -w)
    (h : w ⬝ᵥ v = 0) :
    CFSG.ComponentClassification.CatalogueBHigherLinearAction.slConjugation 3 F B
      (rankOneSL v w h) = (rankOneSL v w h)⁻¹ := by
  have hBinv : B⁻¹ = B := inv_eq_of_mul_eq_one_right hB
  have hBB : (B : Matrix (Fin 3) (Fin 3) F) * B = 1 := by
    rw [← Matrix.GeneralLinearGroup.coe_mul, hB, Matrix.GeneralLinearGroup.coe_one]
  apply Subtype.ext
  rw [coe_slConjugation, coe_rankOneSL_inv, coe_rankOneSL, hBinv, mul_add, mul_one, add_mul, hBB,
    mul_vecMulVec, vecMulVec_mul, hv, hw, vecMulVec_neg, sub_eq_add_neg]

theorem slConjugation_transpose_rankOneSL {A : GL (Fin 3) F}
    (hA : (A : Matrix (Fin 3) (Fin 3) F)ᵀ = A) {u : Fin 3 → F}
    (h : (u ᵥ* ((A⁻¹ : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F)) ⬝ᵥ u = 0) :
    CFSG.ComponentClassification.CatalogueBHigherLinearAction.slConjugation 3 F A
      ((rankOneSL u _ h)⁻¹).transpose = (rankOneSL u _ h)⁻¹ := by
  set S : Matrix (Fin 3) (Fin 3) F := ((A⁻¹ : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) with hS
  have hAS : (A : Matrix (Fin 3) (Fin 3) F) * S = 1 := by
    rw [hS, ← Matrix.GeneralLinearGroup.coe_mul, mul_inv_cancel, Matrix.GeneralLinearGroup.coe_one]
  have hSt : Sᵀ = S := by
    have h1 : Sᵀ * (A : Matrix (Fin 3) (Fin 3) F) = 1 := by
      rw [← hA, ← transpose_mul, hAS, transpose_one]
    calc Sᵀ = Sᵀ * ((A : Matrix (Fin 3) (Fin 3) F) * S) := by rw [hAS, mul_one]
      _ = S := by rw [← mul_assoc, h1, one_mul]
  have hAr : (A : Matrix (Fin 3) (Fin 3) F) *ᵥ (u ᵥ* S) = u := by
    rw [← mulVec_transpose, hSt, mulVec_mulVec, hAS, one_mulVec]
  apply Subtype.ext
  rw [coe_slConjugation, Matrix.SpecialLinearGroup.coe_transpose, coe_rankOneSL_inv,
    transpose_sub, transpose_one, transpose_vecMulVec, mul_sub, mul_one, sub_mul,
    show ((A⁻¹ : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) = S from rfl, hAS, mul_vecMulVec,
    vecMulVec_mul, hAr]

variable [Finite F]

theorem exists_sl3_inv_of_involution {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hFc : Nat.card F = p)
    {ν : MulAut (projectiveSL 3 F)} (hν2 : ν ^ 2 = 1) (hν1 : ν ≠ 1) :
    ∃ T : SpecialLinearGroup (Fin 3) F, orderOf T = p ∧ orderOf (proj 3 F T) = p ∧
      ν (proj 3 F T) = proj 3 F T⁻¹ := by
  have : Fact p.Prime := ⟨hp⟩
  have : Fintype F := Fintype.ofFinite F
  have : CharP F p := charP_of_card_eq_prime_pow (by rw [← Nat.card_eq_fintype_card, hFc, pow_one])
  have h2 : (2 : F) ≠ 0 := by
    intro h
    have : (p : ℕ) ∣ 2 := (CharP.cast_eq_zero_iff F p 2).mp (by exact_mod_cast h)
    have := Nat.le_of_dvd (by norm_num) this
    have := hp.two_le
    omega
  obtain ⟨-, hform⟩ := automorphism_generation (n := 3) (K := F) (by norm_num)
  obtain ⟨A, σ, ε, hε, rfl⟩ := hform ν
  rw [ringAut_eq_one hp hFc σ, map_one, mul_one] at hν2 hν1 ⊢
  interval_cases ε
  · rw [pow_zero, mul_one] at hν2 hν1 ⊢
    rw [← map_pow] at hν2
    obtain ⟨c, hc⟩ := (CFSG.LocalAnalysis.ComponentInitial.ProjectivePlane.conjAut_eq_one_iff
      (by norm_num) _).mp hν2
    set d : Fˣ := Matrix.GeneralLinearGroup.det A with hd
    have hdc : d ^ 2 = c ^ 3 := by
      have h := congrArg Matrix.GeneralLinearGroup.det hc
      rw [map_pow] at h
      rw [h]
      apply Units.ext
      rw [Matrix.GeneralLinearGroup.val_det_apply, Matrix.GeneralLinearGroup.coe_scalar,
        scalar_apply, det_diagonal, Finset.prod_const, Finset.card_univ, Fintype.card_fin,
        Units.val_pow_eq_pow_val]
    set μ : Fˣ := c * d⁻¹ with hμ
    have hμc : μ ^ 2 * c = 1 := by
      rw [hμ, mul_pow, inv_pow, hdc]
      group
    set B : GL (Fin 3) F := Matrix.GeneralLinearGroup.scalar (Fin 3) μ * A with hB
    have hBA : conjAut 3 F B = conjAut 3 F A := by
      rw [hB, map_mul, conjAut_scalar, one_mul]
    have hcoeB : (B : Matrix (Fin 3) (Fin 3) F) = (μ : F) • (A : Matrix (Fin 3) (Fin 3) F) := by
      rw [hB, Matrix.GeneralLinearGroup.coe_mul, Matrix.GeneralLinearGroup.coe_scalar,
        smul_eq_diagonal_mul, scalar_apply]
    have hAA : (A : Matrix (Fin 3) (Fin 3) F) * A = (c : F) • 1 := by
      rw [← Matrix.GeneralLinearGroup.coe_mul, ← pow_two, hc, Matrix.GeneralLinearGroup.coe_scalar,
        scalar_apply, smul_one_eq_diagonal]
    have hBBm : (B : Matrix (Fin 3) (Fin 3) F) * B = 1 := by
      rw [hcoeB, smul_mul_smul_comm, hAA, smul_smul, ← Units.val_mul, ← Units.val_mul, ← pow_two,
        hμc, Units.val_one, one_smul]
    have hBB : B * B = 1 := Units.ext hBBm
    have hB1 : (B : Matrix (Fin 3) (Fin 3) F) ≠ 1 := by
      intro h1
      apply hν1
      rw [← hBA, show B = 1 from Units.ext h1, map_one]
    have hBm : (B : Matrix (Fin 3) (Fin 3) F) ≠ -1 := by
      intro h1
      apply hν1
      have : B = Matrix.GeneralLinearGroup.scalar (Fin 3) (-1) := by
        apply Units.ext
        rw [h1, Matrix.GeneralLinearGroup.coe_scalar, Units.val_neg, Units.val_one, scalar_apply,
          ← smul_one_eq_diagonal, neg_smul, one_smul]
      rw [← hBA, this, conjAut_scalar]
    obtain ⟨v, w, hv, hw, hAv, hwA, hwv⟩ := exists_eigen_of_mul_self_eq_one h2 hBBm hB1 hBm
    obtain ⟨ho, hop⟩ := orderOf_rankOneSL (p := p) hv hw hwv
    refine ⟨rankOneSL v w hwv, ho, hop, ?_⟩
    rw [← hBA, conjAut_proj, slConjugation_rankOneSL hBB hAv hwA hwv]
  · rw [pow_one] at hν2 hν1 ⊢
    have hsq := sq_conjAut_fieldAut_dualAut A (1 : F ≃+* F)
    rw [map_one, mul_one, mul_one, map_one, mul_one, hν2] at hsq
    have hmap : Matrix.GeneralLinearGroup.map ((1 : F ≃+* F) : F →+* F) =
        MonoidHom.id (GL (Fin 3) F) := Matrix.GeneralLinearGroup.map_id
    rw [hmap, MonoidHom.id_apply] at hsq
    obtain ⟨c, hc⟩ := (CFSG.LocalAnalysis.ComponentInitial.ProjectivePlane.conjAut_eq_one_iff
      (by norm_num) _).mp hsq.symm
    have hAt : (A : Matrix (Fin 3) (Fin 3) F) = (c : F) • (A : Matrix (Fin 3) (Fin 3) F)ᵀ := by
      have h1 := congrArg (fun g : GL (Fin 3) F => (g : Matrix (Fin 3) (Fin 3) F)) hc
      simp only [Matrix.GeneralLinearGroup.coe_mul, Matrix.GeneralLinearGroup.coe_inverseTranspose,
        Matrix.GeneralLinearGroup.coe_scalar] at h1
      have h2' : ((A⁻¹ : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F)ᵀ *
          (A : Matrix (Fin 3) (Fin 3) F)ᵀ = 1 := by
        rw [← transpose_mul, ← Matrix.GeneralLinearGroup.coe_mul, mul_inv_cancel,
          Matrix.GeneralLinearGroup.coe_one, transpose_one]
      calc (A : Matrix (Fin 3) (Fin 3) F) = (A : Matrix (Fin 3) (Fin 3) F) *
            (((A⁻¹ : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F)ᵀ *
              (A : Matrix (Fin 3) (Fin 3) F)ᵀ) := by rw [h2', mul_one]
        _ = scalar (Fin 3) (c : F) * (A : Matrix (Fin 3) (Fin 3) F)ᵀ := by
          rw [← mul_assoc, h1]
        _ = _ := by rw [scalar_apply, ← smul_eq_diagonal_mul]
    have hdet : (A : Matrix (Fin 3) (Fin 3) F).det ≠ 0 := by
      rw [← Matrix.GeneralLinearGroup.val_det_apply]
      exact Units.ne_zero _
    have hA0 : (A : Matrix (Fin 3) (Fin 3) F) ≠ 0 := fun h0 => hdet (by rw [h0]; simp)
    have hsym : (A : Matrix (Fin 3) (Fin 3) F)ᵀ = A := by
      have hAt' : (A : Matrix (Fin 3) (Fin 3) F)ᵀ = (c : F) • (A : Matrix (Fin 3) (Fin 3) F) := by
        conv_lhs => rw [hAt]
        rw [transpose_smul, transpose_transpose]
      have hcc : ((c : F) * c - 1) • (A : Matrix (Fin 3) (Fin 3) F) = 0 := by
        rw [sub_smul, one_smul, ← smul_smul, ← hAt', ← hAt, sub_self]
      have hc2 : (c : F) * c = 1 := by
        rcases smul_eq_zero.mp hcc with h0 | h0
        · exact sub_eq_zero.mp h0
        · exact absurd h0 hA0
      have hc1 : (c : F) = 1 ∨ (c : F) = -1 := by
        have : ((c : F) - 1) * ((c : F) + 1) = 0 := by linear_combination hc2
        rcases mul_eq_zero.mp this with h0 | h0
        · exact Or.inl (sub_eq_zero.mp h0)
        · exact Or.inr (eq_neg_of_add_eq_zero_left h0)
      rcases hc1 with h1 | h1
      · rw [hAt', h1, one_smul]
      · exfalso
        apply hdet
        have hd := congrArg Matrix.det hAt
        rw [h1, det_smul, det_transpose, Fintype.card_fin] at hd
        have : (2 : F) * (A : Matrix (Fin 3) (Fin 3) F).det = 0 := by linear_combination hd
        exact (mul_eq_zero.mp this).resolve_left h2
    set S : Matrix (Fin 3) (Fin 3) F := ((A⁻¹ : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) with hS
    obtain ⟨u, hu0, hu⟩ :=
      CFSG.LieType.SeitzGeneration.exists_nonzero_zero_quadratic (σ := Fin 3) (by simp) S
    have h : (u ᵥ* S) ⬝ᵥ u = 0 := by rw [← dotProduct_mulVec]; exact hu
    have hr : u ᵥ* S ≠ 0 := by
      intro h0
      apply hu0
      have hSA : S * (A : Matrix (Fin 3) (Fin 3) F) = 1 := by
        rw [hS, ← Matrix.GeneralLinearGroup.coe_mul, inv_mul_cancel,
          Matrix.GeneralLinearGroup.coe_one]
      rw [← vecMul_one u, ← hSA, ← vecMul_vecMul, h0, zero_vecMul]
    obtain ⟨ho, hop⟩ := orderOf_rankOneSL (p := p) hu0 hr h
    refine ⟨rankOneSL u _ h, ho, hop, ?_⟩
    rw [MulAut.mul_apply, dualAut_proj, conjAut_proj, slConjugation_transpose_rankOneSL hsym h]

end CFSG.Quasithin.H13.S126C
