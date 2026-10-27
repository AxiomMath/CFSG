module

public import CFSG.Monster.AxisCount.DenseGD
public import CFSG.Monster.B.Rep4371.KeyActXi

public section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.Monster.AxisCount

open CFSG.Monster CFSG.Monster.B CFSG.Monster.Code CFSG.Monster.Spin CFSG.Monster.SpinLattice
  CFSG.Monster.ScalarKernel CFSG.Monster.Lifts CFSG.Monster.Visible CFSG.Monster.Xi
  CFSG.Monster.Griess CFSG.Monster.B.Rep4371 Matrix

theorem Evec_vecMul_Ximat (η : Bool) (c : ℕ) :
    Evec η c ᵥ* Ximat =
      ∑ n : Fin 64, (((Model.xiGammaN c false : ℚ) * sgn (boolZ (Model.xiGTerm η c n).1)) / 64) •
          Evec (Model.xiGTerm η c n).2.1 (Model.xiGTerm η c n).2.2 +
      ∑ n : Fin 64, (((Model.xiGammaN c true : ℚ) * sgn (boolZ (Model.xiGTerm (!η) c n).1)) / 64) •
          Evec (Model.xiGTerm (!η) c n).2.1 (Model.xiGTerm (!η) c n).2.2 := by
  rw [Ximat, ← vecMul_vecMul, Evec_vecMul_XiGamma]
  simp only [smul_vecMul, add_vecMul]
  rw [Evec_vecMul_XiG, Evec_vecMul_XiG]
  exact combine_xi _ _ _ _ _ _

theorem xiRows_get (r : ℕ) (hr : r < 4096) :
    (Native.xiRows ())[r]! =
      [false, true].flatMap fun f =>
        let α := Native.xiGammaN (Native.rowC r) f
        if α == 0 then []
        else (List.range 64).map fun ν =>
          let t := Native.xiGTerm (Native.rowEta r != f) (Native.rowC r) ν
          (Native.rowIdx t.2.1 t.2.2, α * Native.sgnI t.1) := by
  unfold Native.xiRows
  rw [Array.getElem!_eq_getD, Array.getD_eq_getD_getElem?, Array.getElem?_map,
    Array.getElem?_range]
  simp [hr]

theorem sum_map_range {M : Type*} [AddCommMonoid M] (F : ℕ → M) (n : ℕ) :
    ((List.range n).map F).sum = ∑ i ∈ Finset.range n, F i := by
  induction n with
  | zero => simp
  | succ n ih => rw [List.range_succ, List.map_append, List.sum_append, ih, Finset.sum_range_succ]; simp

theorem sum_row_f (η : Bool) (c : ℕ) (f : Bool) :
    (((if Native.xiGammaN c f == 0 then ([] : List (ℕ × ℤ)) else (List.range 64).map fun ν =>
        (Native.rowIdx (Native.xiGTerm (η != f) c ν).2.1 (Native.xiGTerm (η != f) c ν).2.2,
          Native.xiGammaN c f * Native.sgnI (Native.xiGTerm (η != f) c ν).1)).map
      fun t => ((t.2 : ℚ) / 2 ^ 6) • eRow t.1).sum) =
    ∑ ν ∈ Finset.range 64, (((Model.xiGammaN c f : ℚ) *
        sgn (boolZ (Model.xiGTerm (η != f) c ν).1)) / 64) •
      Evec (Model.xiGTerm (η != f) c ν).2.1 (Model.xiGTerm (η != f) c ν).2.2 := by
  rw [native_xiGammaN, native_xiGTerm, native_sgnI]
  by_cases h : Model.xiGammaN c f == 0
  · have h0 : Model.xiGammaN c f = 0 := beq_iff_eq.1 h
    rw [ite_eq_left h]
    simp [h0]
  · have h' : ¬ Model.xiGammaN c f = 0 := fun e => h (beq_iff_eq.2 e)
    rw [ite_eq_right h, List.map_map, sum_map_range]
    refine Finset.sum_congr rfl fun ν _ => ?_
    simp only [Function.comp_apply, ← Evec_eq_eRow, sgn_boolZ]
    push_cast
    ring_nf

theorem xiRows_spec (r : ℕ) (hr : r < 4096) :
    (Pi.single (spinOfRow r) (1 : ℚ) : SpinIdx → ℚ) ᵥ* Ximat =
      (((Native.xiRows ())[r]!).map fun t => ((t.2 : ℚ) / 2 ^ (6 : ℕ)) • eRow t.1).sum := by
  rw [xiRows_get r hr]
  have h1 : (Pi.single (spinOfRow r) (1 : ℚ) : SpinIdx → ℚ) =
      Evec (Native.rowEta r) (Native.rowC r) := rfl
  rw [h1, Evec_vecMul_Ximat]
  simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil, List.map_append, List.sum_append]
  rw [sum_row_f (Native.rowEta r) (Native.rowC r) false, sum_row_f (Native.rowEta r) (Native.rowC r) true]
  have e0 : (Native.rowEta r != false) = Native.rowEta r := by cases Native.rowEta r <;> rfl
  have e1 : (Native.rowEta r != true) = !Native.rowEta r := by cases Native.rowEta r <;> rfl
  rw [e0, e1, Finset.sum_range, Finset.sum_range]

theorem c4N_div32 (a b : ℕ) : (((Model.c4N a b / 32 : ℤ) : ℚ)) / 2 = (Model.c4N a b : ℚ) / 64 := by
  unfold Model.c4N
  split_ifs <;> norm_num

theorem xiG_getD (i j : Fin 24) :
    Native.xiG.getD (i * 24 + j) 0 =
      if (i : ℕ) / 4 = (j : ℕ) / 4 then Model.c4N ((i : ℕ) % 4) ((j : ℕ) % 4) / 32 else 0 := by
  have h : (i : ℕ) * 24 + j < 576 := by omega
  have e1 : ((i : ℕ) * 24 + j) / 24 = i := by omega
  have e2 : ((i : ℕ) * 24 + j) % 24 = j := by omega
  unfold Native.xiG
  rw [Native.getD_ofFn _ _ h]
  simp only [e1, e2, native_c4N]

theorem gdSpec_xi_aux :
    GDSpec ⟨1, Native.xiG, Native.tabT Native.conjXiN, Native.tabD Native.conjXiN, 6,
      Native.xiRows ()⟩ xiPair := by
  refine ⟨fun i j => ?_, fun y => ?_, fun r hr => ?_⟩
  · show gXi i j = _
    rw [xiG_getD, gXi_apply]
    have hc : (Code.col i = Code.col j) ↔ (i : ℕ) / 4 = (j : ℕ) / 4 := by
      constructor
      · intro h
        have := congrArg Fin.val h
        simpa [Code.col] using this
      · intro h
        exact Fin.ext (by simpa [Code.col] using h)
    by_cases hij : (i : ℕ) / 4 = (j : ℕ) / 4
    · rw [ite_eq_left (hc.2 hij), ite_eq_left hij, C4_eq_c4N]
      have := c4N_div32 ((i : ℕ) % 4) ((j : ℕ) % 4)
      simpa [Code.row] using this.symm
    · rw [ite_eq_right (fun h => hij (hc.1 h)), ite_eq_right hij]
      simp
  · have hf : ∀ y, conjQ xiPair (pauliQ y) = pauliQ (Native.conjXiN y) := by
      intro y
      rw [native_conjXiN]
      exact conjQ_xi_toQ y
    exact fastAct_conj _ _ hf y
  · exact xiRows_spec r hr

theorem gdSpec_xi : GDSpec (Native.GD.ofGen (Native.mkCtx ()) .xi) xiPair :=
  gdSpec_xi_aux

end CFSG.Monster.AxisCount
