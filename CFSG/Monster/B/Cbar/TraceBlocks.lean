module

public import CFSG.Monster.B.Cbar.AxisPolynomial
public import CFSG.Monster.Parity.TraceSplitting
import Mathlib.Algebra.BigOperators.Field

public section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.Monster.B

open CFSG.Monster CFSG.Monster.Code CFSG.Monster.Spin CFSG.Monster.SpinLattice
  CFSG.Monster.Griess CFSG.Monster.Visible CFSG.Monster.Parity Matrix

theorem trace_prod_eq {R M N : Type*} [CommRing R] [AddCommGroup M] [Module R M]
    [Module.Free R M] [Module.Finite R M] [AddCommGroup N] [Module R N] [Module.Free R N]
    [Module.Finite R N] (f : M × N →ₗ[R] M × N) :
    LinearMap.trace R (M × N) f =
      LinearMap.trace R M (LinearMap.fst R M N ∘ₗ f ∘ₗ LinearMap.inl R M N) +
        LinearMap.trace R N (LinearMap.snd R M N ∘ₗ f ∘ₗ LinearMap.inr R M N) := by
  have hid : LinearMap.inl R M N ∘ₗ LinearMap.fst R M N + LinearMap.inr R M N ∘ₗ LinearMap.snd R M N =
      LinearMap.id := by
    apply LinearMap.ext
    intro x
    simp
  calc LinearMap.trace R (M × N) f
      = LinearMap.trace R (M × N) (f ∘ₗ (LinearMap.inl R M N ∘ₗ LinearMap.fst R M N +
          LinearMap.inr R M N ∘ₗ LinearMap.snd R M N)) := by rw [hid, LinearMap.comp_id]
    _ = LinearMap.trace R (M × N) ((f ∘ₗ LinearMap.inl R M N) ∘ₗ LinearMap.fst R M N) +
          LinearMap.trace R (M × N) ((f ∘ₗ LinearMap.inr R M N) ∘ₗ LinearMap.snd R M N) := by
        rw [LinearMap.comp_add, map_add]
        rfl
    _ = _ := by
        rw [LinearMap.trace_comp_comm' (LinearMap.fst R M N) (f ∘ₗ LinearMap.inl R M N),
          LinearMap.trace_comp_comm' (LinearMap.snd R M N) (f ∘ₗ LinearMap.inr R M N)]

section MatTrace

variable {n : Type*} [Fintype n] [DecidableEq n]

omit [Fintype n] in
private noncomputable def matEquiv : Matrix n n ℚ ≃ₗ[ℚ] (n × n → ℚ) where
  toFun N k := N k.1 k.2
  invFun f := Matrix.of fun i j => f (i, j)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  left_inv _ := rfl
  right_inv _ := rfl

omit [Fintype n] in
private theorem matEquiv_symm_single (k : n × n) :
    matEquiv.symm (Pi.single k 1) = Matrix.single k.1 k.2 (1 : ℚ) := by
  obtain ⟨a, b⟩ := k
  ext i j
  change (Pi.single (a, b) (1 : ℚ) : n × n → ℚ) (i, j) = _
  rw [Pi.single_apply, Matrix.single_apply]
  by_cases h1 : a = i
  · by_cases h2 : b = j
    · subst h1 h2
      simp
    · rw [ite_eq_right (fun h => h2 (congrArg Prod.snd h).symm), ite_eq_right (fun h => h2 h.2)]
  · rw [ite_eq_right (fun h => h1 (congrArg Prod.fst h).symm), ite_eq_right (fun h => h1 h.1)]

theorem trace_mat_eq_sum (F : Module.End ℚ (Matrix n n ℚ)) :
    LinearMap.trace ℚ (Matrix n n ℚ) F = ∑ k : n × n, F (Matrix.single k.1 k.2 1) k.1 k.2 := by
  rw [LinearMap.trace_eq_matrix_trace ℚ (Module.Basis.ofEquivFun matEquiv), Matrix.trace]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [Matrix.diag_apply, LinearMap.toMatrix_apply, Module.Basis.ofEquivFun_repr_apply,
    Module.Basis.coe_ofEquivFun]
  change matEquiv (F (matEquiv.symm (Pi.single k 1))) k = _
  rw [matEquiv_symm_single]
  rfl

@[expose] noncomputable def lrM (X Y : Matrix n n ℚ) : Module.End ℚ (Matrix n n ℚ) where
  toFun B := X * B * Y
  map_add' B B' := by rw [Matrix.mul_add, Matrix.add_mul]
  map_smul' c B := by rw [Matrix.mul_smul, Matrix.smul_mul]; rfl

@[expose] noncomputable def lrT (X Y : Matrix n n ℚ) : Module.End ℚ (Matrix n n ℚ) where
  toFun B := X * Bᵀ * Y
  map_add' B B' := by rw [transpose_add, Matrix.mul_add, Matrix.add_mul]
  map_smul' c B := by rw [transpose_smul, Matrix.mul_smul, Matrix.smul_mul]; rfl

theorem trace_lrM (X Y : Matrix n n ℚ) :
    LinearMap.trace ℚ (Matrix n n ℚ) (lrM X Y) = trace X * trace Y := by
  rw [trace_mat_eq_sum, Fintype.sum_prod_type]
  have h : ∀ i j : n, (X * Matrix.single i j (1 : ℚ) * Y) i j = X i i * Y j j := by
    intro i j
    rw [Matrix.mul_apply, Finset.sum_eq_single j]
    · rw [mul_single_apply_same, mul_one]
    · intro b _ hb
      rw [mul_single_apply_of_ne _ _ _ _ _ hb, zero_mul]
    · simp
  simp only [lrM, LinearMap.coe_mk, AddHom.coe_mk, h]
  rw [Matrix.trace, Matrix.trace, Finset.sum_mul_sum]
  rfl

theorem trace_lrT (X Y : Matrix n n ℚ) :
    LinearMap.trace ℚ (Matrix n n ℚ) (lrT X Y) = ∑ i, ∑ j, X i j * Y i j := by
  rw [trace_mat_eq_sum, Fintype.sum_prod_type]
  have h : ∀ i j : n, (X * (Matrix.single i j (1 : ℚ))ᵀ * Y) i j = X i j * Y i j := by
    intro i j
    rw [transpose_single, Matrix.mul_apply, Finset.sum_eq_single i]
    · rw [mul_single_apply_same, mul_one]
    · intro b _ hb
      rw [mul_single_apply_of_ne _ _ _ _ _ hb, zero_mul]
    · simp
  simp only [lrT, LinearMap.coe_mk, AddHom.coe_mk, h]

end MatTrace

@[expose] noncomputable def symAnti (A : symMat) : Module.End ℚ symMat where
  toFun B := ⟨(A : Matrix (Fin 24) (Fin 24) ℚ) * B + (B : Matrix (Fin 24) (Fin 24) ℚ) * A, by
    rw [mem_symMat, transpose_add, transpose_mul, transpose_mul, A.2, B.2, add_comm]⟩
  map_add' B B' := Subtype.ext (by
    simp only [Submodule.coe_add, Matrix.mul_add, Matrix.add_mul]
    abel)
  map_smul' c B := Subtype.ext (by
    simp only [Submodule.coe_smul, Matrix.mul_smul, Matrix.smul_mul, RingHom.id_apply,
      smul_add])

theorem coe_symAnti (A B : symMat) :
    (symAnti A B : Matrix (Fin 24) (Fin 24) ℚ) =
      (A : Matrix (Fin 24) (Fin 24) ℚ) * B + (B : Matrix (Fin 24) (Fin 24) ℚ) * A := rfl

@[expose] noncomputable def symProj : Matrix (Fin 24) (Fin 24) ℚ →ₗ[ℚ] symMat where
  toFun B := ⟨(2 : ℚ)⁻¹ • (B + Bᵀ), by
    rw [mem_symMat, transpose_smul, transpose_add, transpose_transpose, add_comm]⟩
  map_add' B B' := Subtype.ext (by
    simp only [transpose_add, Submodule.coe_add, smul_add]
    abel)
  map_smul' c B := Subtype.ext (by
    simp only [transpose_smul, Submodule.coe_smul, RingHom.id_apply, smul_add, smul_comm c])

theorem symProj_coe (B : symMat) : symProj (B : Matrix (Fin 24) (Fin 24) ℚ) = B := by
  apply Subtype.ext
  change (2 : ℚ)⁻¹ • ((B : Matrix (Fin 24) (Fin 24) ℚ) + (B : Matrix (Fin 24) (Fin 24) ℚ)ᵀ) = B
  rw [B.2, ← two_smul ℚ (B : Matrix (Fin 24) (Fin 24) ℚ), smul_smul]
  norm_num

theorem trace_symAnti (A : symMat) :
    LinearMap.trace ℚ symMat (symAnti A) = 25 * trace (A : Matrix (Fin 24) (Fin 24) ℚ) := by
  have hid : symProj ∘ₗ symMat.subtype = LinearMap.id :=
    LinearMap.ext fun B => symProj_coe B
  have h1 : LinearMap.trace ℚ symMat (symAnti A) =
      LinearMap.trace ℚ (Matrix (Fin 24) (Fin 24) ℚ) (symMat.subtype ∘ₗ symAnti A ∘ₗ symProj) := by
    rw [LinearMap.trace_comp_comm' (symAnti A ∘ₗ symProj) symMat.subtype, LinearMap.comp_assoc,
      hid, LinearMap.comp_id]
  have h2 : symMat.subtype ∘ₗ symAnti A ∘ₗ symProj = (2 : ℚ)⁻¹ • (lrM (A : Matrix _ _ ℚ) 1 +
      lrT (A : Matrix _ _ ℚ) 1 + lrM 1 (A : Matrix _ _ ℚ) + lrT 1 (A : Matrix _ _ ℚ)) := by
    apply LinearMap.ext
    intro B
    simp only [LinearMap.comp_apply, Submodule.subtype_apply, coe_symAnti, LinearMap.smul_apply,
      LinearMap.add_apply, lrM, lrT, LinearMap.coe_mk, AddHom.coe_mk, Matrix.mul_one,
      Matrix.one_mul]
    change (A : Matrix (Fin 24) (Fin 24) ℚ) * ((2 : ℚ)⁻¹ • (B + Bᵀ)) +
      ((2 : ℚ)⁻¹ • (B + Bᵀ)) * (A : Matrix (Fin 24) (Fin 24) ℚ) = _
    simp only [Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_add, Matrix.add_mul]
    module
  rw [h1, h2, map_smul, map_add, map_add, map_add, trace_lrM, trace_lrM, trace_lrT, trace_lrT]
  have e1 : ∑ i, ∑ j, (A : Matrix (Fin 24) (Fin 24) ℚ) i j * (1 : Matrix (Fin 24) (Fin 24) ℚ) i j =
      trace (A : Matrix (Fin 24) (Fin 24) ℚ) := by
    simp only [Matrix.one_apply, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq, Finset.mem_univ,
      ite_true]
    rfl
  have e2 : ∑ i, ∑ j, (1 : Matrix (Fin 24) (Fin 24) ℚ) i j * (A : Matrix (Fin 24) (Fin 24) ℚ) i j =
      trace (A : Matrix (Fin 24) (Fin 24) ℚ) := by
    simp only [Matrix.one_apply, ite_mul, one_mul, zero_mul, Finset.sum_ite_eq, Finset.mem_univ,
      ite_true]
    rfl
  rw [e1, e2, trace_one, Fintype.card_fin, smul_eq_mul]
  push_cast
  ring

theorem thetaX_rhoPair_apply {r : Q} (hr : IsShortCoord (coordOf r)) (y : SpaceX)
    (c : ShortIdx) :
    thetaX (rhoPair r) y c = sgn ((alphaS (shortCls hr) c : ℤ) : ZMod 2) * y c := by
  have hdec : y = ∑ d, y d • (Pi.single d 1 : SpaceX) := by
    funext e
    simp [Finset.sum_apply, Pi.single_apply]
  have h1 : thetaX (rhoPair r) y = ∑ d, y d • thetaX (rhoPair r) (Pi.single d 1) := by
    conv_lhs => rw [hdec]
    rw [map_sum]
    exact Finset.sum_congr rfl fun d _ => map_smul _ _ _
  rw [h1, Finset.sum_apply, Finset.sum_eq_single c]
  · rw [thetaX_rhoPair_single hr c, Pi.smul_apply, Pi.smul_apply, Pi.single_eq_same, smul_eq_mul,
      smul_eq_mul, mul_one, mul_comm]
  · intro d _ hd
    rw [thetaX_rhoPair_single hr d, Pi.smul_apply, Pi.smul_apply, Pi.single_eq_of_ne' hd,
      smul_zero, smul_zero]
  · simp

theorem trace_X_eq_sum (G : Module.End ℚ SpaceX) :
    LinearMap.trace ℚ SpaceX G = ∑ c, G (Pi.single c 1) c := by
  rw [LinearMap.trace_eq_matrix_trace ℚ (Pi.basisFun ℚ ShortIdx), Matrix.trace]
  refine Finset.sum_congr rfl fun c _ => ?_
  rw [Matrix.diag_apply, LinearMap.toMatrix_apply, Pi.basisFun_repr, Pi.basisFun_apply]

@[expose] noncomputable def rhoL (r : Q) (v : SpaceB) : Module.End ℚ SpaceB :=
  (rhoEquiv r : SpaceB →ₗ[ℚ] SpaceB) ∘ₗ gmul v

theorem rhoL_apply (r : Q) (v w : SpaceB) : rhoL r v w = rhoEquiv r (gmul v w) := rfl

theorem rhoL_blockA (r : Q) (v : SpaceB) :
    LinearMap.fst ℚ symMat (SpaceX × SpaceW) ∘ₗ rhoL r v ∘ₗ LinearMap.inl ℚ symMat (SpaceX × SpaceW) =
      (2 : ℚ) • symAnti v.1 := by
  apply LinearMap.ext
  intro B
  apply Subtype.ext
  change ((rhoEquiv r (gmul v (B, 0, 0))).1 : Matrix (Fin 24) (Fin 24) ℚ) =
    (2 : ℚ) • ((v.1 : Matrix (Fin 24) (Fin 24) ℚ) * B + (B : Matrix (Fin 24) (Fin 24) ℚ) * v.1)
  rw [rhoEquiv_fst]
  change gmulA v (inA B) = _
  simp [gmulA]

theorem trace_rhoL_blockA (r : Q) (v : SpaceB) :
    LinearMap.trace ℚ symMat
      (LinearMap.fst ℚ symMat (SpaceX × SpaceW) ∘ₗ rhoL r v ∘ₗ
        LinearMap.inl ℚ symMat (SpaceX × SpaceW)) = 50 * trace (Am v) := by
  rw [rhoL_blockA, map_smul, trace_symAnti, smul_eq_mul]
  ring

theorem tau_self_self (d c : ShortIdx) : tau d c c = 0 := by
  rw [tau_comm]
  exact tau_self_right c d

theorem rhoL_blockX_apply {r : Q} (hr : IsShortCoord (coordOf r)) (v : SpaceB) (c : ShortIdx) :
    (rhoL r v (0, Pi.single c 1, 0)).2.1 c =
      sgn ((alphaS (shortCls hr) c : ℤ) : ZMod 2) * (qf c (Am v) / 8) := by
  rw [rhoL_apply, rhoEquiv_snd_fst, thetaX_rhoPair_apply hr]
  congr 1
  change gmulX v (inX (Pi.single c 1)) c = _
  have hsum : ∑ d, ∑ e, xs v d * xs (inX (Pi.single c 1)) e * tau d e c = 0 := by
    refine Finset.sum_eq_zero fun d _ => ?_
    rw [Finset.sum_eq_single c]
    · rw [tau_self_self, mul_zero]
    · intro e _ he
      simp [Pi.single_eq_of_ne he]
    · simp
  rw [gmulX, hsum]
  simp [qf_zero]

theorem trace_rhoL_blockX {r : Q} (hr : IsShortCoord (coordOf r)) (v : SpaceB) :
    LinearMap.trace ℚ SpaceX (LinearMap.fst ℚ SpaceX SpaceW ∘ₗ
      (LinearMap.snd ℚ symMat (SpaceX × SpaceW) ∘ₗ rhoL r v ∘ₗ
        LinearMap.inr ℚ symMat (SpaceX × SpaceW)) ∘ₗ LinearMap.inl ℚ SpaceX SpaceW) =
      ∑ c, sgn ((alphaS (shortCls hr) c : ℤ) : ZMod 2) * (qf c (Am v) / 8) := by
  rw [trace_X_eq_sum]
  exact Finset.sum_congr rfl fun c _ => rhoL_blockX_apply hr v c

theorem transpose_coe_Q {r : Q} (hr : IsShortCoord (coordOf r)) :
    ((r : GL SpinIdx ℚ) : Matrix SpinIdx SpinIdx ℚ)ᵀ = sgn (centralCoord r) • Rmat (shortCls hr) := by
  rw [coe_Q_eq_sgn_smul_Rmat hr, transpose_smul, Rmat_symm]

theorem rhoL_blockW {r : Q} (v : SpaceB) :
    LinearMap.snd ℚ SpaceX SpaceW ∘ₗ (LinearMap.snd ℚ symMat (SpaceX × SpaceW) ∘ₗ rhoL r v ∘ₗ
        LinearMap.inr ℚ symMat (SpaceX × SpaceW)) ∘ₗ LinearMap.inr ℚ SpaceX SpaceW =
      lr ((r : GL SpinIdx ℚ) : Matrix SpinIdx SpinIdx ℚ)ᵀ 1 * Lw v := by
  apply LinearMap.ext
  intro N
  change (rhoEquiv r (gmul v (0, 0, N))).2.2 = _
  rw [rhoEquiv_snd_snd, Module.End.mul_apply, lr_apply, Matrix.mul_one]
  rfl

theorem trace_Kc (c : ShortIdx) : trace (Kc c) = 16 := by
  rw [Kc, trace_sub, trace_one, trace_smul, trace_Umat, Fintype.card_fin, smul_eq_mul]
  norm_num

theorem trace_rhoL_blockW {r : Q} (hr : IsShortCoord (coordOf r)) (v : SpaceB) :
    LinearMap.trace ℚ SpaceW (LinearMap.snd ℚ SpaceX SpaceW ∘ₗ
      (LinearMap.snd ℚ symMat (SpaceX × SpaceW) ∘ₗ rhoL r v ∘ₗ
        LinearMap.inr ℚ symMat (SpaceX × SpaceW)) ∘ₗ LinearMap.inr ℚ SpaceX SpaceW) =
      8192 * sgn (centralCoord r) * xs v (shortCls hr) := by
  rw [rhoL_blockW, Lw_eq, mul_add, Finset.mul_sum, map_add, map_sum]
  simp only [mul_smul_comm, lr_mul_lr, map_smul, trace_lr, smul_eq_mul, Matrix.mul_one,
    transpose_coe_Q hr, trace_smul, trace_Rmat, mul_zero, zero_mul, zero_add, Matrix.smul_mul,
    trace_Rmat_mul_Rmat, trace_Kc]
  rw [Finset.sum_eq_single (shortCls hr)]
  · rw [ite_eq_left rfl]
    ring
  · intro c _ hc
    rw [ite_eq_right (Ne.symm hc)]
    ring
  · simp

theorem trace_rhoL {r : Q} (hr : IsShortCoord (coordOf r)) (v : SpaceB) :
    LinearMap.trace ℚ SpaceB (rhoL r v) = 50 * trace (Am v) +
      ∑ c, sgn ((alphaS (shortCls hr) c : ℤ) : ZMod 2) * (qf c (Am v) / 8) +
        8192 * sgn (centralCoord r) * xs v (shortCls hr) := by
  rw [trace_prod_eq, trace_prod_eq, trace_rhoL_blockA, trace_rhoL_blockX hr, trace_rhoL_blockW hr,
    add_assoc]

@[expose] noncomputable def signedU {r : Q} (hr : IsShortCoord (coordOf r)) :
    Matrix (Fin 24) (Fin 24) ℚ :=
  ∑ c, sgn ((alphaS (shortCls hr) c : ℤ) : ZMod 2) • Umat c

theorem sum_sgn_qf {r : Q} (hr : IsShortCoord (coordOf r)) (A : Matrix (Fin 24) (Fin 24) ℚ) :
    ∑ c, sgn ((alphaS (shortCls hr) c : ℤ) : ZMod 2) * (qf c A / 8) =
      trace (signedU hr * A) / 8 := by
  rw [signedU, Finset.sum_mul, trace_sum, Finset.sum_div]
  refine Finset.sum_congr rfl fun c _ => ?_
  rw [Matrix.smul_mul, trace_smul, trace_Umat_mul, smul_eq_mul, mul_div_assoc]

theorem bform_inA_oneA (v : SpaceB) : bform (inA oneA) v = trace (Am v) := by
  rw [bform_apply]
  simp [coe_oneA]

theorem trace_rhoL_of_signedU {r : Q} (hr : IsShortCoord (coordOf r))
    (hM : signedU hr = (8160 : ℚ) • 1 - (2048 : ℚ) • Umat (shortCls hr)) (v : SpaceB) :
    LinearMap.trace ℚ SpaceB (rhoL r v) =
      bform ((1070 : ℚ) • inA oneA - (4096 : ℚ) • axis r) v := by
  rw [trace_rhoL hr, sum_sgn_qf hr, hM, map_sub, map_smul, map_smul, LinearMap.sub_apply,
    LinearMap.smul_apply, LinearMap.smul_apply, bform_inA_oneA, bform_comm, bform_axis_left hr,
    Matrix.sub_mul, Matrix.smul_mul, Matrix.smul_mul, Matrix.one_mul, trace_sub, trace_smul,
    trace_smul, trace_Umat_mul, smul_eq_mul, smul_eq_mul, smul_eq_mul, smul_eq_mul]
  ring

end CFSG.Monster.B
