module

public import CFSG.Sporadic.J4.Action
import Certificates.Data.CFSGNative.J4.F2
import Certificates.Data.CFSGNative.J4.Faithful

public section

namespace CFSG.Sporadic.J4

open Native Matrix CFSG.Sporadic.Th

noncomputable abbrev formF : Matrix (Fin 112) (Fin 112) (ZMod 2) := rowsMatrix formRows

section Form

variable (hM : MatFacts)
include hM

theorem matA_form : matA * formF * matAᵀ = formF := by
  have h := congrArg rowsMatrix (eqRows_iff.1 hM.formA)
  rwa [rowsMatrix_mulRows, rowsMatrix_mulRows, rowsMatrix_transposeRows, rowsMatrix_rowsA] at h

theorem matB_form : matB * formF * matBᵀ = formF := by
  have h := congrArg rowsMatrix (eqRows_iff.1 hM.formB)
  rwa [rowsMatrix_mulRows, rowsMatrix_mulRows, rowsMatrix_transposeRows, rowsMatrix_rowsB] at h

theorem form_invariant : ∀ g ∈ J,
    (g : Matrix (Fin 112) (Fin 112) (ZMod 2)) * formF * (g : Matrix (Fin 112) (Fin 112) (ZMod 2))ᵀ
      = formF := by
  intro g hg
  induction hg using Subgroup.closure_induction with
  | mem x hx =>
    rcases hx with h | h
    · rw [h, gA_val hM]; exact matA_form hM
    · rw [Set.mem_singleton_iff] at h
      rw [h, gB_val hM]; exact matB_form hM
  | one => simp
  | mul x y _ _ hx hy =>
    rw [Units.val_mul, Matrix.transpose_mul]
    calc x.val * y.val * formF * ((y.val)ᵀ * (x.val)ᵀ)
        = x.val * (y.val * formF * (y.val)ᵀ) * (x.val)ᵀ := by simp only [Matrix.mul_assoc]
      _ = formF := by rw [hy, hx]
  | inv x _ hx =>
    have h1 : (x⁻¹ : GL (Fin 112) (ZMod 2)).val * x.val = 1 := by
      rw [← Units.val_mul, inv_mul_cancel, Units.val_one]
    calc (x⁻¹ : GL (Fin 112) (ZMod 2)).val * formF * ((x⁻¹ : GL (Fin 112) (ZMod 2)).val)ᵀ
        = (x⁻¹ : GL (Fin 112) (ZMod 2)).val * (x.val * formF * (x.val)ᵀ) *
            ((x⁻¹ : GL (Fin 112) (ZMod 2)).val)ᵀ := by rw [hx]
      _ = ((x⁻¹ : GL (Fin 112) (ZMod 2)).val * x.val) * formF *
            ((x⁻¹ : GL (Fin 112) (ZMod 2)).val * x.val)ᵀ := by
        rw [Matrix.transpose_mul]; simp only [Matrix.mul_assoc]
      _ = formF := by rw [h1, Matrix.transpose_one, Matrix.one_mul, Matrix.mul_one]

@[expose] noncomputable def pairing (u w : Row) : ZMod 2 := (ofRow u ᵥ* formF) ⬝ᵥ ofRow w

theorem pairing_smul (g : J) (u w : Row) : pairing (g • u) (g • w) = pairing u w := by
  unfold pairing
  rw [smul_row, smul_row]
  have hinv := form_invariant hM ((g⁻¹ : J) : GL (Fin 112) (ZMod 2)) (g⁻¹ : J).property
  set m := (((g⁻¹ : J) : GL (Fin 112) (ZMod 2)) : Matrix (Fin 112) (Fin 112) (ZMod 2))
  rw [show ofRow w ᵥ* m = mᵀ *ᵥ ofRow w from (Matrix.mulVec_transpose m (ofRow w)).symm,
    Matrix.dotProduct_mulVec, Matrix.vecMul_vecMul, Matrix.vecMul_vecMul, ← Matrix.mul_assoc,
    hinv]

end Form

theorem sigRows_apply (fs : Array V2) (i t : Fin 112) :
    rowsMatrix (sigRows fs) i t = if t.val < fs.size then (fs[t.val]?.getD V2.zero).toVec i
      else 0 := by
  rw [rowsMatrix_apply]
  unfold sigRows
  rw [Array.getElem?_ofFn, dite_eq_left i.isLt, Option.getD_some, V2.toVec_ofFn]
  by_cases ht : t.val < fs.size
  · rw [ite_eq_left ht, V2.toVec_apply]; simp [ht]
  · rw [ite_eq_right ht]; simp [ht]

theorem sig_toVec (fs : Array V2) (w : V2) {t : Fin 112} (ht : t.val < fs.size) :
    (frApply (frTable (sigRows fs)) w).toVec t = w.toVec ⬝ᵥ (fs[t.val]?.getD V2.zero).toVec := by
  rw [frApply_toVec_eq_vecMul, Matrix.vecMul, dotProduct, dotProduct]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [sigRows_apply, ite_eq_left ht]

theorem sigRows_wf (fs : Array V2) : ∀ x ∈ sigRows fs, x.wf = true := by
  intro x hx
  unfold sigRows at hx
  obtain ⟨i, rfl⟩ := Array.mem_ofFn.1 hx
  exact V2.ofFn_wf _

@[expose] noncomputable def fsOf (qs : Array ℕ) : Array V2 :=
  #[frApply (frTable formRows) rootV] ++ qs.map fun i => frApply (frTable formRows) (rdV2 bs0.keys i)

@[expose] noncomputable def sigOf (qs : Array ℕ) (w : ℕ) : V2 :=
  frApply (frTable (sigRows (fsOf qs))) (rdV2 bs0.keys w)

@[expose] noncomputable def qpt (qs : Array ℕ) (t : ℕ) : ℕ := if t = 0 then 0 else qs[t - 1]!

theorem fsOf_size (qs : Array ℕ) : (fsOf qs).size = qs.size + 1 := by
  simp [fsOf]; omega

theorem fsOf_toVec (hO : OrbitFacts) (qs : Array ℕ) {t : ℕ} (ht : t < qs.size + 1) :
    ((fsOf qs)[t]?.getD V2.zero).toVec = ofRow (vecAt (qpt qs t)) ᵥ* formF := by
  unfold fsOf qpt
  by_cases h0 : t = 0
  · subst h0
    rw [ite_eq_left rfl, Array.getElem?_append_left (by simp), show (#[frApply (frTable formRows) rootV] :
      Array V2)[0]? = some (frApply (frTable formRows) rootV) from rfl, Option.getD_some,
      frApply_toVec_eq_vecMul, vecAt_zero hO]
    rfl
  · rw [ite_eq_right h0, Array.getElem?_append_right (by simp; omega)]
    simp only [List.size_toArray, List.length_cons, List.length_nil, zero_add]
    rw [Array.getElem?_map, Array.getElem?_eq_getElem (by omega), Option.map_some,
      Option.getD_some, frApply_toVec_eq_vecMul, ← getElem!_pos qs (t - 1) (by omega)]
    rfl

theorem sigOf_toVec (hO : OrbitFacts) (qs : Array ℕ) (w : ℕ) (t : Fin 112) :
    (sigOf qs w).toVec t = if t.val < qs.size + 1 then pairing (vecAt (qpt qs t)) (vecAt w)
      else 0 := by
  by_cases ht : t.val < qs.size + 1
  · rw [ite_eq_left ht, sigOf, sig_toVec _ _ (by rw [fsOf_size]; exact ht), fsOf_toVec hO qs ht,
      pairing, dotProduct_comm]
    rfl
  · rw [ite_eq_right ht, sigOf, frApply_toVec_eq_vecMul, Matrix.vecMul, dotProduct]
    refine Finset.sum_eq_zero fun i _ => ?_
    rw [sigRows_apply, ite_eq_right (by rw [fsOf_size]; exact ht), mul_zero]

theorem sigOf_wf (qs : Array ℕ) (w : ℕ) : (sigOf qs w).wf = true :=
  frApply_frTable_wf (sigRows_wf _) _

theorem sigOf_smul (hO : OrbitFacts) (qs : Array ℕ) (hqs : ∀ t < qs.size, qs[t]! < nPts)
    {g : J} (hg0 : idx nPts g 0 = 0) (hgq : ∀ t < qs.size, idx nPts g qs[t]! = qs[t]!)
    {w : ℕ} (hw : w < nPts) : sigOf qs (idx nPts g w) = sigOf qs w := by
  have hn := (orbit_parts hO).1
  apply V2.eq_of_toVec_eq (sigOf_wf _ _) (sigOf_wf _ _)
  funext t
  rw [sigOf_toVec hO, sigOf_toVec hO]
  split_ifs with ht
  · have hq : qpt qs t < nPts := by
      unfold qpt; split_ifs with h0
      · exact hn
      · exact hqs _ (by omega)
    have hfix : g • vecAt (qpt qs t) = vecAt (qpt qs t) := by
      refine (idx_eq_iff hO hq hq).1 ?_
      unfold qpt; split_ifs with h0
      · exact hg0
      · exact hgq _ (by omega)
    have hgw : g • vecAt w = vecAt (idx nPts g w) := (idx_eq_iff hO hw (idx_lt g hw)).1 rfl
    rw [← hgw, ← hfix, pairing_smul hO.mat, hfix]
  · rfl

theorem eq_of_uniqueSigOK {qs : Array ℕ} {d : ByteArray}
    (h : uniqueSigOK bs0.keys nPts (frTable (sigRows (fsOf qs))) basisIdx 26 d 3 = true)
    {t : ℕ} (ht : t < basisIdx.size) {i : ℕ} (hi : i < nPts)
    (he : sigOf qs i = sigOf qs basisIdx[t]!) : i = basisIdx[t]! := by
  unfold uniqueSigOK at h
  rw [Bool.and_eq_true, Bool.and_eq_true, Bool.and_eq_true] at h
  obtain ⟨⟨⟨-, -⟩, hb⟩, hall⟩ := h
  have hbt := (List.all_eq_true.1 hb) t (List.mem_range.2 ht)
  simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at hbt
  obtain ⟨⟨hhi, hlo⟩, hd⟩ := hbt
  have hpt := parAllS_eq_true hall i hi
  simp only at hpt
  change sigOf qs i = sigOf qs basisIdx[t]! at he
  have e1 : frApply (frTable (sigRows (fsOf qs))) (rdV2 bs0.keys i) = sigOf qs i := rfl
  have e2 : frApply (frTable (sigRows (fsOf qs))) (rdV2 bs0.keys basisIdx[t]!) =
    sigOf qs basisIdx[t]! := rfl
  rw [e1, he, ← e2, hhi, hd] at hpt
  simp only [beq_self_eq_true, Bool.true_and, decide_eq_true_eq, ite_eq_left hlo] at hpt
  rw [Bool.or_eq_true, beq_iff_eq, beq_iff_eq] at hpt
  rcases hpt with h0 | h1
  · omega
  · rw [Nat.add_sub_cancel, Array.getElem?_eq_getElem ht, Option.getD_some] at h1
    rw [← h1, getElem!_pos basisIdx t ht]

theorem basisIdx_size : basisIdx.size = 112 := by decide

@[expose] noncomputable def basisRows : Array V2 := basisIdx.map (rdV2 bs0.keys ·)

theorem basisRows_row (t : Fin 112) :
    (fun j => rowsMatrix basisRows t j) = ofRow (vecAt basisIdx[t.val]!) := by
  funext j
  rw [rowsMatrix_apply, basisRows, Array.getElem?_map,
    Array.getElem?_eq_getElem (by rw [basisIdx_size]; exact t.isLt), Option.map_some,
    Option.getD_some, ← getElem!_pos basisIdx t.val (by rw [basisIdx_size]; exact t.isLt)]
  rfl

theorem eq_one_of_fix_basis (hb : eqRows (mulRows basisRows (invRows basisRows)) idRows = true)
    (g : J) (hg : ∀ t : Fin 112, g • vecAt basisIdx[t.val]! = vecAt basisIdx[t.val]!) :
    g = 1 := by
  set m := (((g⁻¹ : J) : GL (Fin 112) (ZMod 2)) : Matrix (Fin 112) (Fin 112) (ZMod 2)) with hm
  have hinv : rowsMatrix basisRows * rowsMatrix (invRows basisRows) = 1 := by
    have := congrArg rowsMatrix (eqRows_iff.1 hb)
    rwa [rowsMatrix_mulRows, rowsMatrix_idRows] at this
  have hinv' : rowsMatrix (invRows basisRows) * rowsMatrix basisRows = 1 := by
    rw [← Matrix.inv_eq_right_inv hinv]
    exact Matrix.nonsing_inv_mul _ (Matrix.isUnit_det_of_right_inverse hinv)
  have hfix : rowsMatrix basisRows * m = rowsMatrix basisRows := by
    ext t j
    have h2 := congrArg (fun w => ofRow w j) (hg t)
    simp only [smul_row] at h2
    have e : (rowsMatrix basisRows * m) t j = ((fun k => rowsMatrix basisRows t k) ᵥ* m) j := by
      rw [Matrix.mul_apply, Matrix.vecMul, dotProduct]
    calc (rowsMatrix basisRows * m) t j = ((fun k => rowsMatrix basisRows t k) ᵥ* m) j := e
      _ = (ofRow (vecAt basisIdx[t.val]!) ᵥ* m) j := by rw [basisRows_row]
      _ = ofRow (vecAt basisIdx[t.val]!) j := by rw [hm]; exact h2
      _ = rowsMatrix basisRows t j := (congrFun (basisRows_row t) j).symm
  have hm1 : m = 1 := by
    calc m = rowsMatrix (invRows basisRows) * rowsMatrix basisRows * m := by
            rw [hinv', Matrix.one_mul]
      _ = rowsMatrix (invRows basisRows) * (rowsMatrix basisRows * m) := Matrix.mul_assoc _ _ _
      _ = 1 := by rw [hfix, hinv']
  have : (g⁻¹ : J) = 1 := Subtype.ext (Units.ext hm1)
  rwa [inv_eq_one] at this

theorem eq_one_of_fix_tuple (hO : OrbitFacts) {qs : Array ℕ} (hqs : ∀ t < qs.size, qs[t]! < nPts)
    {d : ByteArray}
    (hsig : uniqueSigOK bs0.keys nPts (frTable (sigRows (fsOf qs))) basisIdx 26 d 3 = true)
    (hbn : ∀ t < basisIdx.size, basisIdx[t]! < nPts)
    (hb : eqRows (mulRows basisRows (invRows basisRows)) idRows = true)
    {g : J} (hg0 : idx nPts g 0 = 0) (hgq : ∀ t < qs.size, idx nPts g qs[t]! = qs[t]!) :
    g = 1 := by
  apply eq_one_of_fix_basis hb
  intro t
  have htb : t.val < basisIdx.size := by rw [basisIdx_size]; exact t.isLt
  have hbt := hbn t htb
  have hfix : idx nPts g basisIdx[t.val]! = basisIdx[t.val]! :=
    eq_of_uniqueSigOK hsig htb (idx_lt g hbt) (sigOf_smul hO qs hqs hg0 hgq hbt)
  exact (idx_eq_iff hO hbt hbt).1 hfix

end CFSG.Sporadic.J4
