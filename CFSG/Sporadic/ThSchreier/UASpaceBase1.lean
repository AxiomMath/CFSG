
module

public import CFSG.Sporadic.ThSchreier.UASpaceBase

public import CFSG.Sporadic.ThSchreier.CentralizerData
public import CFSG.Sporadic.ThSchreier.WordsBase1
public meta import CFSG.Sporadic.ThSchreier.CentralizerData
public meta import CFSG.Sporadic.ThSchreier.WordsBase1
public import CFSG.Sporadic.ThSchreier.UASpaceInputs
public import Certificates.Certificate2325
public import Mathlib
public import CFSG.Blueprint.NativeSporadic
public import CFSG.Blueprint.MatrixSeedIdentification
public import CFSG.Sporadic.Th.F2Spec
public import CFSG.Certificates.SchreierStabilizerGenerators
public import Certificates.Data.CFSGNative.Th.Certificate
public import CFSG.Sporadic.Th.Max3.Data

@[expose] public section

namespace CFSG.Sporadic.ThSchreier

open CFSG.Sporadic.Th CFSG.Sporadic.Th.Native CFSG.Sporadic.Th.Max3 Pointwise

private theorem native_ua_facts :
    eqRows (mulRows (mulRows rowsUAP rowsAmI) rowsUAQ) rowsD120 = true ∧
    eqRows (mulRows rowsUAPInv rowsUAP) idRows = true ∧
    eqRows (mulRows rowsUAQ rowsUAQInv) idRows = true ∧
    (∀ n ∈ uaRowsTxt, n < 2 ^ 248) ∧ uaRowsTxt.length = 4 * 248 :=
  Certificates.certificate2325

theorem uaBlock_wf (k : ℕ) : ∀ r ∈ uaBlock k, r.wf = true := by
  intro r hr
  obtain ⟨i, rfl⟩ := Array.mem_ofFn.1 hr
  apply v4OfNat_wf
  by_cases h : 248 * k + i.val < uaRowsTxt.length
  · rw [List.getD_eq_getElem _ _ h]
    exact native_ua_facts.2.2.2.1 _ (List.getElem_mem h)
  · rw [List.getD_eq_default _ _ (by omega)]
    norm_num

theorem rowsMatrix_rowsAmI : rowsMatrix rowsAmI = toMat a - 1 := by
  ext i j
  have hA : rowsMatrix rowsA = toMat a := isRows_a.eq
  rw [rowsMatrix_apply, Matrix.sub_apply, ← hA, rowsMatrix_apply, ← rowsMatrix_idRows,
    rowsMatrix_apply]
  simp only [rowsAmI, Array.getElem?_ofFn, Fin.is_lt, ↓reduceDIte, Option.getD_some]
  rw [V4.toVec_xor, Pi.add_apply, zmod2_sub_eq_add]
  have h1 : rowsA[i.val]? = some rowsA[i.val]! := by
    rw [Array.getElem?_eq_getElem (by rw [isRows_a.size]; exact i.isLt)]
    simp [getElem!_def, Array.getElem?_eq_getElem (by rw [isRows_a.size]; exact i.isLt)]
  have h2 : idRows[i.val]? = some idRows[i.val]! := by
    rw [Array.getElem?_eq_getElem (by rw [idRows_size]; exact i.isLt)]
    simp [getElem!_def, Array.getElem?_eq_getElem (by rw [idRows_size]; exact i.isLt)]
  rw [h1, h2]
  rfl

theorem ua_factor : matUAP * (toMat a - 1) * matUAQ = matD120 := by
  have h := rowsMatrix_eq_of_eqRows native_ua_facts.1
  rwa [rowsMatrix_mulRows, rowsMatrix_mulRows, rowsMatrix_rowsAmI, rowsMatrix_rowsD120] at h

theorem ua_P_inv : rowsMatrix rowsUAPInv * matUAP = 1 := by
  have h := rowsMatrix_eq_of_eqRows native_ua_facts.2.1
  rwa [rowsMatrix_mulRows, rowsMatrix_idRows] at h

theorem ua_Q_inv : matUAQ * rowsMatrix rowsUAQInv = 1 := by
  have h := rowsMatrix_eq_of_eqRows native_ua_facts.2.2.1
  rwa [rowsMatrix_mulRows, rowsMatrix_idRows] at h

theorem AmI_mul_Q : (toMat a - 1) * matUAQ = rowsMatrix rowsUAPInv * matD120 := by
  rw [← ua_factor, ← Matrix.mul_assoc, ← Matrix.mul_assoc, ua_P_inv, Matrix.one_mul]

theorem P_mul_AmI : matUAP * (toMat a - 1) = matD120 * rowsMatrix rowsUAQInv := by
  rw [← ua_factor, Matrix.mul_assoc _ matUAQ, ua_Q_inv, Matrix.mul_one]

theorem mem_planeUA_iff (r : RowV) :
    r ∈ planeUA ↔ ∀ k : Fin 248, 120 ≤ k.val → Matrix.vecMul (ofRow r) matUAQ k = 0 := by
  constructor
  · rintro ⟨s, rfl⟩ k hk
    simp only [ofRow_toRow]
    rw [Matrix.vecMul_vecMul, AmI_mul_Q, ← Matrix.vecMul_vecMul, vecMul_matD120_apply,
      ite_eq_right (by omega)]
  · intro h
    have hproj : Matrix.vecMul (Matrix.vecMul (ofRow r) matUAQ) matD120 =
        Matrix.vecMul (ofRow r) matUAQ := by
      funext k
      rw [vecMul_matD120_apply]
      split_ifs with hk
      · rfl
      · exact (h k (by omega)).symm
    refine ⟨toRow (Matrix.vecMul (Matrix.vecMul (ofRow r) matUAQ) matUAP), ?_⟩
    simp only [ofRow_toRow]
    rw [Matrix.vecMul_vecMul, P_mul_AmI, ← Matrix.vecMul_vecMul, hproj, Matrix.vecMul_vecMul,
      ua_Q_inv, Matrix.vecMul_one]
    rfl

theorem planeUA_map : planeUA.map (rowEquiv : RowV →ₗ[ZMod 2] (Fin 248 → ZMod 2)) =
    Submodule.span (ZMod 2) (Set.range (toMat a - 1).row) := by
  ext w
  rw [Submodule.mem_map, Submodule.mem_span_range_iff_exists_fun]
  constructor
  · rintro ⟨_, ⟨r, rfl⟩, rfl⟩
    exact ⟨ofRow r, (Matrix.vecMul_eq_sum _ _).symm⟩
  · rintro ⟨c, hc⟩
    refine ⟨toRow (Matrix.vecMul c (toMat a - 1)), ⟨toRow c, rfl⟩, ?_⟩
    rw [← hc]
    show Matrix.vecMul c (toMat a - 1) = _
    rw [Matrix.vecMul_eq_sum]
    simp only [Matrix.row_apply']

theorem finrank_planeUA : Module.finrank (ZMod 2) planeUA = 120 := by
  rw [← LinearEquiv.finrank_map_eq rowEquiv planeUA, planeUA_map,
    ← Matrix.rank_eq_finrank_span_row]
  have hP : IsUnit matUAP.det := Matrix.isUnit_det_of_left_inverse ua_P_inv
  have hQ : IsUnit matUAQ.det := Matrix.isUnit_det_of_right_inverse ua_Q_inv
  rw [← Matrix.rank_mul_eq_right_of_isUnit_det matUAP _ hP,
    ← Matrix.rank_mul_eq_left_of_isUnit_det matUAQ _ hQ, ua_factor, matD120,
    Matrix.rank_diagonal, Fintype.card_subtype]
  have e : (Finset.univ.filter fun i : Fin 248 =>
      (if (i : ℕ) < 120 then (1 : ZMod 2) else 0) ≠ 0) =
      Finset.univ.filter fun i : Fin 248 => (i : ℕ) < 120 := by
    apply Finset.filter_congr
    intro i _
    split_ifs with h
    · exact ⟨fun _ => h, fun _ => by decide⟩
    · exact ⟨fun h' => absurd rfl h', fun h' => absurd h' h⟩
  rw [e, Fin.card_filter_val_lt]
  rfl

theorem inUA_iff (w : V4) : inUA w = true ↔ toRow w.toVec ∈ planeUA := by
  rw [mem_planeUA_iff, inUA, inUAT]
  simp only [List.all_eq_true, List.mem_range, Bool.or_eq_true, decide_eq_true_eq,
    Bool.not_eq_true']
  have hvec := frApply_frTable_vecMul rowsUAQ w
  constructor
  · intro h k hk
    have := h k.val k.isLt
    rcases this with h1 | h1
    · omega
    · have h2 := congrFun hvec k
      rw [V4.toVec_apply, h1] at h2
      simp only [Bool.false_eq_true, ↓reduceIte] at h2
      exact h2.symm
  · intro h k hk
    by_cases hk' : k < 120
    · exact Or.inl hk'
    · right
      have h2 := congrFun hvec ⟨k, hk⟩
      rw [V4.toVec_apply] at h2
      have h3 := h ⟨k, hk⟩ (by simp; omega)
      simp only [ofRow_toRow] at h3
      rw [← h2] at h3
      cases hb : (frApply (frTable rowsUAQ) w).testBit k
      · rfl
      · rw [hb] at h3
        exact absurd h3 (by decide)

end CFSG.Sporadic.ThSchreier
