module

public import CFSG.Monster.AxisCount.DenseWord
public import CFSG.Monster.B.Cbar.TraceBlocks
public import CFSG.Monster.B.TwoA.Census.SymTrace

public section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.Monster.Existence

open CFSG.Monster CFSG.Monster.B CFSG.Monster.Code CFSG.Monster.Spin CFSG.Monster.SpinLattice
  CFSG.Monster.ScalarKernel CFSG.Monster.Visible CFSG.Monster.Griess CFSG.Monster.AxisCount
  CFSG.Monster.B.Rep4371 CFSG.Monster.B.TwoA.Census CFSG.Monster.Parity Matrix

@[expose] def latTr (g : Native.GD) : ℤ := ∑ i ∈ Finset.range 24, g.G.getD (i * 24 + i) 0

@[expose] def latTr2 (g : Native.GD) : ℤ :=
  ∑ i ∈ Finset.range 24, ∑ k ∈ Finset.range 24, g.G.getD (i * 24 + k) 0 * g.G.getD (k * 24 + i) 0

@[expose] def wTr (g : Native.GD) : ℤ := ∑ r ∈ Finset.range 4096, rowCoef (g.rowT[r]!) r

@[expose] def xTrC (c : Native.Ctx) (g : Native.GD) : ℤ :=
  ∑ p ∈ Finset.range 98280,
    (let y := Native.fastAct g.tT g.tD (false, c.keys[p]!.1, c.keys[p]!.2)
     if c.find y.2.1 y.2.2 = p then Model.sgnI y.1 else 0)

theorem xTrC_eq (g : Native.GD) :
    xTrC (Native.mkCtx ()) g = ∑ p ∈ Finset.range 98280, if tgtPos g p = p then sgPos g p else 0 :=
  rfl

theorem trace_thetaA (gm : Matrix (Fin 24) (Fin 24) ℚ) :
    LinearMap.trace ℚ symMat (thetaA gm) = ((trace gm) ^ 2 + trace (gm * gm)) / 2 := by
  have h := trace_symConj gmᵀ
  rw [Matrix.trace_transpose, ← Matrix.transpose_mul, Matrix.trace_transpose] at h
  exact h

theorem thetaW_eq_lr (s : Matrix SpinIdx SpinIdx ℚ) (gm : Matrix (Fin 24) (Fin 24) ℚ) :
    thetaW s gm = lr sᵀ gm := rfl

theorem trace_thetaW (s : Matrix SpinIdx SpinIdx ℚ) (gm : Matrix (Fin 24) (Fin 24) ℚ) :
    LinearMap.trace ℚ SpaceW (thetaW s gm) = trace s * trace gm := by
  rw [thetaW_eq_lr, trace_lr, Matrix.trace_transpose]

theorem trace_thetaX (P : Pvis) (g : Native.GD)
    (hconj : ∀ y : Model.Pauli, conjQ P (pauliQ y) = pauliQ (Native.fastAct g.tT g.tD y)) :
    LinearMap.trace ℚ SpaceX (thetaX P) =
      ((∑ p ∈ Finset.range 98280, if tgtPos g p = p then sgPos g p else 0 : ℤ) : ℚ) := by
  rw [trace_X_eq_sum, ← Equiv.sum_comp shortEquiv, Int.cast_sum, Finset.sum_range]
  refine Finset.sum_congr rfl fun pp _ => ?_
  rw [shortEquiv_apply, thetaX_shortOf_apply P g hconj pp (shortOf pp), posOf_shortOf]
  by_cases h : tgtPos g pp = pp
  · simp [h]
  · simp [h]

theorem trace_mat_of_GDSpec {g : Native.GD} {P : Pvis} (hg : GDSpec g P) :
    trace (mat P.1.2) = (latTr g : ℚ) / 2 ^ g.latS := by
  rw [Matrix.trace, latTr, Int.cast_sum, Finset.sum_div, ← sum_fin24]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Matrix.diag_apply, hg.lat i i]

theorem trace_mat_mul_of_GDSpec {g : Native.GD} {P : Pvis} (hg : GDSpec g P) :
    trace (mat P.1.2 * mat P.1.2) = (latTr2 g : ℚ) / 2 ^ (2 * g.latS) := by
  rw [Matrix.trace, latTr2, Int.cast_sum, Finset.sum_div, ← sum_fin24]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Matrix.diag_apply, Matrix.mul_apply, Int.cast_sum, Finset.sum_div, ← sum_fin24]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [hg.lat i k, hg.lat k i, Int.cast_mul, pow_mul', sq]
  field_simp

theorem rowSum_apply (k : ℕ) (L : List (ℕ × ℤ)) (r : ℕ) (hr : r < 4096) :
    ((L.map fun t => ((t.2 : ℚ) / 2 ^ k) • eRow t.1).sum) (spinOfRow r) =
      (rowCoef L r : ℚ) / 2 ^ k := by
  induction L with
  | nil => simp [rowCoef]
  | cons t L ih =>
    have hc : rowCoef (t :: L) r = (if t.1 = r then t.2 else 0) + rowCoef L r := by
      simp [rowCoef]
    rw [List.map_cons, List.sum_cons, Pi.add_apply, ih, hc, Pi.smul_apply, smul_eq_mul,
      eRow_apply, rowOf_spinOfRow hr]
    by_cases ht : t.1 = r
    · simp [ht, hr, add_div]
    · simp [ht]

theorem trace_spin_of_GDSpec {g : Native.GD} {P : Pvis} (hg : GDSpec g P) :
    trace ((P.1.1 : GL SpinIdx ℚ) : Matrix SpinIdx SpinIdx ℚ) = (wTr g : ℚ) / 2 ^ g.rowS := by
  rw [Matrix.trace, ← Equiv.sum_comp spinRowEquiv, wTr, Int.cast_sum, Finset.sum_div,
    Finset.sum_range]
  refine Finset.sum_congr rfl fun r _ => ?_
  have h := congrFun (hg.row r r.2) (spinOfRow r)
  rw [single_one_vecMul, Matrix.row_apply, rowSum_apply _ _ _ r.2] at h
  rw [Matrix.diag_apply, spinRowEquiv_apply]
  exact h

theorem trace_thetaEquiv_of_GDSpec
    {g : Native.GD} {P : Pvis} (hg : GDSpec g P) :
    LinearMap.trace ℚ SpaceB (thetaEquiv P : SpaceB →ₗ[ℚ] SpaceB) =
      ((((latTr g : ℚ) / 2 ^ g.latS) ^ 2 + (latTr2 g : ℚ) / 2 ^ (2 * g.latS)) / 2) +
        ((∑ p ∈ Finset.range 98280, if tgtPos g p = p then sgPos g p else 0 : ℤ) : ℚ) +
        ((wTr g : ℚ) / 2 ^ g.rowS) * ((latTr g : ℚ) / 2 ^ g.latS) := by
  have e : (thetaEquiv P : SpaceB →ₗ[ℚ] SpaceB) = theta P := rfl
  rw [e, theta, LinearMap.trace_prodMap', LinearMap.trace_prodMap', trace_thetaA,
    trace_thetaX P g hg.conj, trace_thetaW, trace_mat_of_GDSpec hg, trace_mat_mul_of_GDSpec hg,
    trace_spin_of_GDSpec hg]
  ring

@[expose, noinline] def traceVal (c : Native.Ctx) (g : Native.GD) : ℤ :=
  latTr g ^ 2 + latTr2 g + 2 * xTrC c g + 2 * (wTr g * latTr g)

theorem trace_thetaEquiv_of_GDSpec_int
    {g : Native.GD} {P : Pvis} (hg : GDSpec g P)
    (hl : g.latS = 0) (hr : g.rowS = 0) {T : ℤ}
    (hT : traceVal (Native.mkCtx ()) g = 2 * T) :
    LinearMap.trace ℚ SpaceB (thetaEquiv P : SpaceB →ₗ[ℚ] SpaceB) = (T : ℚ) := by
  rw [trace_thetaEquiv_of_GDSpec hg, hl, hr, ← xTrC_eq]
  unfold traceVal at hT
  have hT' := congrArg (Int.cast : ℤ → ℚ) hT
  push_cast at hT'
  simp only [pow_zero, div_one, mul_zero]
  linarith

@[expose, noinline] def permTraceCheck (arr : Array ℕ) (T : ℤ) : Bool :=
  decide (traceVal (Native.mkCtx ()) (Native.GD.ofGen (Native.mkCtx ()) (.perm arr)) = 2 * T)

theorem permTraceCheck_spec {arr : Array ℕ} {T : ℤ} (h : permTraceCheck arr T = true) :
    traceVal (Native.mkCtx ()) (Native.GD.ofGen (Native.mkCtx ()) (.perm arr)) = 2 * T := by
  unfold permTraceCheck at h
  exact of_decide_eq_true h

theorem trace_wordLin_perm
    {arr : Array ℕ} (hv : Native.permValid arr = true) {T : ℤ}
    (hT : permTraceCheck arr T = true) :
    LinearMap.trace ℚ SpaceB
      ((wordLin [Native.Gen.perm arr] : SpaceB ≃ₗ[ℚ] SpaceB) : SpaceB →ₗ[ℚ] SpaceB) = (T : ℚ) := by
  have h1 : wordLin [Native.Gen.perm arr] = thetaEquiv (permPairOf (permOf arr)) := by
    rw [wordLin_cons, wordLin_nil, one_mul, Native.Gen.toLin_perm]
  rw [h1]
  refine trace_thetaEquiv_of_GDSpec_int (gdSpec_perm arr (permOf arr) (permOf_spec hv)) ?_ ?_
    (permTraceCheck_spec hT)
  · rw [ofGen_perm]
  · rw [ofGen_perm]

end CFSG.Monster.Existence
