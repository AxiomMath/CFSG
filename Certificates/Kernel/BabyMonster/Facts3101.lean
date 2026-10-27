module

public import Certificates.Kernel.BabyMonster.Fix.Bind
public import Certificates.Kernel.BabyMonster.Fix.Lin
public import Certificates.Kernel.BabyMonster.Facts3103

public section

namespace CertificateChecks.KernelBM.Fix

open CFSG.KC.BM CFSG.KC.BM.Fix CFSG.KC.BSeed CFSG.KC.BM.Lat CFSG.KC.YModel CFSG.Monster.B.Dyadic
  CFSG.Monster.B.Dyadic.Native Module
open scoped Matrix

theorem testBit_projRow (p f r t : Nat) : (projRow p f r).testBit t =
    (r.testBit (if t < p then t else t + 1) ^^
      (r.testBit p && f.testBit (if t < p then t else t + 1))) := by
  have hb : Nat.land (Nat.shiftRight r p) 1 = if r.testBit p then 1 else 0 := by
    change (r >>> p) &&& 1 = _
    rw [Nat.and_one_is_mod, Nat.shiftRight_eq_div_pow]
    rcases Nat.mod_two_eq_zero_or_one (r / 2 ^ p) with h | h
    · have tb : r.testBit p = false := by
        rw [Nat.testBit_eq_decide_div_mod_eq, h]
        rfl
      rw [h, tb]
      rfl
    · have tb : r.testBit p = true := by
        rw [Nat.testBit_eq_decide_div_mod_eq, h]
        rfl
      rw [h, tb]
      rfl
  have hy : ∀ m, (Nat.xor r (Nat.mul (Nat.land (Nat.shiftRight r p) 1) f)).testBit m =
      (r.testBit m ^^ (r.testBit p && f.testBit m)) := by
    intro m
    rw [hb]
    change (r ^^^ _).testBit m = _
    rw [Nat.testBit_xor]
    cases r.testBit p
    · simp
    · simp
  unfold projRow
  generalize Nat.xor r (Nat.mul (Nat.land (Nat.shiftRight r p) 1) f) = y at hy ⊢
  change ((y &&& (1 <<< p - 1)) ||| ((y >>> (p + 1)) <<< p)).testBit t = _
  rw [Nat.one_shiftLeft, Nat.testBit_lor, Nat.testBit_land, Nat.testBit_two_pow_sub_one,
    Nat.testBit_shiftLeft, Nat.testBit_shiftRight]
  by_cases h : t < p
  · rw [ite_eq_left h, ← hy t]
    simp [h]
  · rw [ite_eq_right h, ← hy (t + 1)]
    have e : p + 1 + (t - p) = t + 1 := by omega
    simp [h, e, Nat.le_of_not_lt h]

theorem val_succAbove (k : Fin 4370) :
    ((pIdx.succAbove k : Fin 4371) : ℕ) = if (k : ℕ) < 1197 then (k : ℕ) else (k : ℕ) + 1 := by
  by_cases hk : (k : ℕ) < 1197
  · have h1 : Fin.castSucc k < pIdx := by
      rw [Fin.lt_def, Fin.val_castSucc]
      exact hk
    rw [Fin.succAbove_of_castSucc_lt _ _ h1, ite_eq_left hk]
    rfl
  · have h1 : pIdx ≤ Fin.castSucc k := by
      rw [Fin.le_def, Fin.val_castSucc]
      exact Nat.le_of_not_lt hk
    rw [Fin.succAbove_of_le_castSucc _ _ h1, ite_eq_right hk]
    rfl

theorem cmat_rows (g : Fin 26) :
    Cmat g = rowsMat 4371 (recOf (Dy.Ck.getD g [])) := by
  obtain ⟨Z, hZ, hS⟩ := Dy.cnumRep g
  change Cmat g = Dy.Sg g
  rw [← hS]
  ext i t
  simp only [Cmat, hZ, Matrix.map_apply, eq_intCast, Rat.num_intCast]

theorem fvec_eq : fvec = vecOf FixedLine.f := by
  rw [f_eq]
  rfl

theorem mem_Ck {C : List (List Nat)} (hC : C ∈ Dy.Ck) : ∃ g : Fin 26, C = Dy.Ck.getD g [] := by
  obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hC
  exact ⟨⟨i, hi⟩, (List.getD_eq_getElem _ _ hi).symm⟩

theorem fvec_fixed (g : Fin 26) :
    fvec ᵥ* Cmat g = fvec := by
  rw [cmat_rows g, fvec_eq]
  exact fix g g.2

theorem msum_mat : rowsMat 4371 (recOf FixedLine.M.rows) =
    (Dy.Ck.map fun C => rowsMat 4371 (recOf C)).sum := by
  refine xorBlocks_sound (fun C hC => ?_) msum
  obtain ⟨g, rfl⟩ := mem_Ck hC
  exact (lens_of (lensAll g g.2)).2

theorem vecMul_listSum (y : Fin 4371 → ZMod 2) :
    ∀ L : List (Matrix (Fin 4371) (Fin 4371) (ZMod 2)), y ᵥ* L.sum = (L.map (y ᵥ* ·)).sum
  | [] => by simp
  | A :: L => by rw [List.sum_cons, Matrix.vecMul_add, vecMul_listSum y L]; simp

theorem listSum_mulVec (x : Fin 4371 → ZMod 2) :
    ∀ L : List (Matrix (Fin 4371) (Fin 4371) (ZMod 2)), L.sum *ᵥ x = (L.map (· *ᵥ x)).sum
  | [] => by simp
  | A :: L => by rw [List.sum_cons, Matrix.add_mulVec, listSum_mulVec x L]; simp

theorem smul26 (y : Fin 4371 → ZMod 2) : (26 : ℕ) • y = 0 := by
  rw [← Nat.cast_smul_eq_nsmul (ZMod 2)]
  have e : ((26 : ℕ) : ZMod 2) = 0 := by decide
  rw [e, zero_smul]

theorem Mfix {y : Fin 4371 → ZMod 2}
    (hy : ∀ g, y ᵥ* Cmat g = y) : y ᵥ* rowsMat 4371 (recOf FixedLine.M.rows) = 0 := by
  rw [msum_mat, vecMul_listSum, List.map_map]
  have h : ∀ C ∈ Dy.Ck, ((y ᵥ* ·) ∘ fun C => rowsMat 4371 (recOf C)) C = y := by
    intro C hC
    obtain ⟨g, rfl⟩ := mem_Ck hC
    rw [Function.comp_apply, ← cmat_rows g]
    exact hy g
  rw [List.map_congr_left h, List.map_const', List.sum_replicate]
  exact smul26 y

theorem Mfix_col {x : Fin 4371 → ZMod 2}
    (hx : ∀ g, Cmat g *ᵥ x = x) : rowsMat 4371 (recOf FixedLine.M.rows) *ᵥ x = 0 := by
  rw [msum_mat, listSum_mulVec, List.map_map]
  have h : ∀ C ∈ Dy.Ck, ((· *ᵥ x) ∘ fun C => rowsMat 4371 (recOf C)) C = x := by
    intro C hC
    obtain ⟨g, rfl⟩ := mem_Ck hC
    rw [Function.comp_apply, ← cmat_rows g]
    exact hx g
  rw [List.map_congr_left h, List.map_const', List.sum_replicate]
  exact smul26 x

theorem rank_M : 4370 ≤ (rowsMat 4371 (recOf FixedLine.M.rows)).rank := by
  rw [rows_M]
  have h1 := card_le_rank (A := stripMatn FixedLine.QM)
    (fun i : {i : Fin 4371 // i.val < 4370} => i.1) shapeM
  rw [card_lt 4371 4370 (by norm_num), ← rkM] at h1
  exact h1.trans (Matrix.rank_mul_le_right _ _)

theorem fixed_vectors (y : Fin 4371 → ZMod 2) (hy : ∀ g : Fin 26, y ᵥ* Cmat g = y) :
    y = 0 ∨ y = fvec := by
  have hK : finrank (ZMod 2) (kerL (rowsMat 4371 (recOf FixedLine.M.rows))) ≤ 1 := by
    have := finrank_kerL (rowsMat 4371 (recOf FixedLine.M.rows))
    have := rank_M
    omega
  have hf : fvec ∈ kerL (rowsMat 4371 (recOf FixedLine.M.rows)) :=
    mem_kerL.2 (Mfix fvec_fixed)
  have hf0 : fvec ≠ 0 := by
    intro h
    have e := congrFun h pIdx
    have hb : fvec pIdx = 1 := by
      change (if CFSG.Monster.B.Binary.Native.fixedVector.testBit 1197 then 1 else 0) = 1
      rw [CertificateChecks.KernelBM.Lat.fixed_bits.1]
      rfl
    rw [hb] at e
    exact one_ne_zero e
  obtain ⟨c, hc⟩ := mem_span_of_finrank_le_one hK hf (mem_kerL.2 (Mfix hy)) hf0
  have zmod2 : c = 0 ∨ c = 1 := by
    fin_cases c
    exacts [Or.inl rfl, Or.inr rfl]
  rcases zmod2 with rfl | rfl
  · left
    rw [← hc]
    exact zero_smul _ _
  · right
    rw [← hc]
    exact one_smul _ _

theorem fixed_covectors (x : Fin 4371 → ZMod 2) (hx : ∀ g : Fin 26, Cmat g *ᵥ x = x) :
    x = 0 := by
  have h0 : stripMatn FixedLine.M *ᵥ x = 0 := by
    rw [← rows_M]
    exact Mfix_col hx
  have h25 : stripMatn FixedLine.C25 *ᵥ x = x := by
    rw [← rows_C25]
    have := hx 25
    rw [cmat_rows 25] at this
    exact this
  have hMp : stripMatn FixedLine.Mp *ᵥ x = 0 := by
    rw [mp, Matrix.add_mulVec, Matrix.add_mulVec, h0, ← rc, ← Matrix.mulVec_mulVec, h25,
      zero_add]
    exact CharTwo.add_self_eq_zero _
  have hdet := Matrix.isUnit_det_of_right_inverse mpinv
  calc x = ((stripMatn FixedLine.Mp)⁻¹ * stripMatn FixedLine.Mp) *ᵥ x := by
        rw [Matrix.nonsing_inv_mul (A := stripMatn FixedLine.Mp) hdet, Matrix.one_mulVec]
    _ = 0 := by rw [← Matrix.mulVec_mulVec, hMp, Matrix.mulVec_zero]

theorem zmod2_xor (a b c : Bool) : ((if (a ^^ (b && c)) then 1 else 0) : ZMod 2) =
    (if a then 1 else 0) + (if b then 1 else 0) * (if c then 1 else 0) := by
  cases a <;> cases b <;> cases c <;> decide

theorem qmat_rows (g : Fin 26)
    {Q : List (List Nat)} (hq : ∀ k < 4370, recOf Q k =
      projRow 1197 FixedLine.f (recOf (Dy.Ck.getD g []) (if k < 1197 then k else k + 1))) :
    Qmat g = rowsMat 4370 (recOf Q) := by
  ext k t
  rw [Qmat, cmat_rows g, fvec_eq]
  change (if (recOf (Dy.Ck.getD g []) (pIdx.succAbove k : ℕ)).testBit (pIdx.succAbove t : ℕ)
      then 1 else 0) + (if (recOf (Dy.Ck.getD g []) (pIdx.succAbove k : ℕ)).testBit 1197
      then 1 else 0) * (if FixedLine.f.testBit (pIdx.succAbove t : ℕ) then 1 else 0) =
    (if (recOf Q k).testBit t then 1 else 0)
  rw [hq k k.2, testBit_projRow, val_succAbove k, val_succAbove t, zmod2_xor]

theorem rank_sub_one {Q P R : List Nat} {k : ℕ} (hk : k ≤ 4370)
    (hrk : stripMat P * (stripMat Q + 1) = stripMat R)
    (hs : LinearIndependent (ZMod 2) (fun i : {i : Fin 4370 // i.val < k} => stripMat R i) ∧
      ∀ i : Fin 4370, k ≤ i.val → stripMat R i = 0)
    (he : LinearIndependent (ZMod 2) (fun i : {i : Fin 4370 // k ≤ i.val} => stripMat P i)) :
    (stripMat Q - 1).rank = k := by
  have e : stripMat Q - 1 = stripMat Q + 1 := by
    ext i j
    rw [Matrix.sub_apply, Matrix.add_apply]
    exact CharTwo.sub_eq_add _ _
  rw [e]
  apply le_antisymm
  · have hK := card_le_kerL (A := stripMat Q + 1)
      (fun i : {i : Fin 4370 // k ≤ i.val} => stripMat P i)
      (fun i => by rw [← rowMul, hrk]; exact hs.2 i i.2) he
    rw [card_ge 4370 k hk] at hK
    have := finrank_kerL (stripMat Q + 1)
    omega
  · have h1 := card_le_rank (A := stripMat R) (fun i : {i : Fin 4370 // i.val < k} => i.1) hs.1
    rw [card_lt 4370 k hk, ← hrk] at h1
    exact h1.trans (Matrix.rank_mul_le_right _ _)

theorem fact3101_of : Fact3101 := by
  have h0 : Qmat 0 = stripMat NativePair.Q0 := (qmat_rows 0 quot0).trans rowsQ0
  have h25 : Qmat 25 = stripMat NativePair.Q25 := (qmat_rows 25 quot25).trans rowsQ25
  refine ⟨fvec_fixed, fixed_vectors, fixed_covectors, ?_, ?_, ?_, ?_⟩
  · rw [h0]
    exact rank_sub_one (by norm_num) rkQ0 shapeQ0 echQ0
  · rw [h25]
    exact rank_sub_one (by norm_num) rkQ25 shapeQ25 echQ25
  · rw [h0]
    exact q0sq
  · rw [h25]
    exact q25cube

end CertificateChecks.KernelBM.Fix

end
