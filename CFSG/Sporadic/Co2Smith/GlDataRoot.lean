module

public import CFSG.Sporadic.Co2Smith.GlData
public import CFSG.Sporadic.Co2Smith.GlDataRootInputs

public section

namespace CFSG.Sporadic.Co2Smith

open CFSG.Sporadic.Co2Cert CFSG.Sporadic.SmallF2 CFSG.Sporadic.SmallF2.Native Matrix

attribute [local irreducible] Matrix.instHMulOfFintypeOfMulOfAddCommMonoid

@[expose] noncomputable def x24K (t : ℕ) : K :=
  γ3K * δ1hK * glE (Native.glPosNF[1]!)[t]! * (δ1hK * γ3K)

@[expose] noncomputable def xPosK (i t : ℕ) : K :=
  if t == 0 then 1
  else if i < 4 then glE (Native.glPosNF[i]!)[t]!
  else if i == 4 then x24K t
  else w3K * x24K t * w3K

@[expose] noncomputable def xLongK (k : ℕ) : K :=
  if k == 0 then x16K else if k == 1 then x25K else if k == 2 then x34K
  else if k == 3 then x61K else if k == 4 then x52K else x43K

@[expose] noncomputable def xRootK (r t : ℕ) : K :=
  if t == 0 then 1
  else if r < 6 then xPosK r t
  else if r < 12 then w0K * xPosK (r - 6) t * w0K
  else xLongK (r - 12)

@[expose] noncomputable def frameConjK (k : ℕ) : K :=
  if k == 0 then 1 else if k == 1 then δ1hK else if k == 2 then δ1hK * δ0hK
  else if k == 3 then w1K else if k == 4 then w1K * δ1hK else w1K * δ1hK * δ0hK

theorem glPosNF_lt4 : ∀ i < 4, ∀ t < 4, ∀ k ∈ (Native.glPosNF[i]!)[t]!, k < 22 := by
  decide

theorem glPosNF_size : ∀ i < 4, (Native.glPosNF[i]!).size = 4 := by
  decide

theorem glPosNF_lt {i : ℕ} (hi : i < 4) (t : ℕ) : ∀ k ∈ (Native.glPosNF[i]!)[t]!, k < 22 := by
  by_cases ht : t < 4
  · exact glPosNF_lt4 i hi t ht
  · rw [getElem!_neg _ t (by rw [glPosNF_size i hi]; exact ht)]
    intro k hk
    exact absurd hk List.not_mem_nil

section Rows


theorem x24K_val (t : ℕ) : (x24K t).val.val = rowsMatrix 22 (Native.glX24R t) := by
  rw [x24K, val_val_mul, val_val_mul, val_val_mul, val_val_mul, γ3K_val, δ1hK_val,
    glE_val (glPosNF_lt (by norm_num : 1 < 4) t), Native.glX24R, Native.glGD, Native.glDG,
    rowsMatrix_mulRows, rowsMatrix_mulRows, rowsMatrix_mulRows, rowsMatrix_mulRows]

theorem xPosK_val (i t : ℕ) :
    (xPosK i t).val.val = rowsMatrix 22 (Native.glPosRows i t) := by
  unfold xPosK Native.glPosRows
  split_ifs with h0 h1 h2
  · rw [rowsMatrix_idRows]
    rfl
  · exact glE_val (glPosNF_lt h1 t)
  · exact x24K_val t
  · rw [val_mul3 w3K_val (x24K_val t) w3K_val]
    rfl

theorem xLongK_val (k : ℕ) : (xLongK k).val.val = rowsMatrix 22 (Native.glLongRows k) := by
  unfold xLongK Native.glLongRows
  split_ifs
  · exact x16K_val
  · exact x25K_val
  · exact x34K_val
  · exact x61K_val
  · exact x52K_val
  · exact x43K_val

theorem xRootK_val (r t : ℕ) :
    (xRootK r t).val.val = rowsMatrix 22 (Native.glRootRows r t) := by
  unfold xRootK Native.glRootRows
  split_ifs
  · rw [rowsMatrix_idRows]
    rfl
  · exact xPosK_val r t
  · rw [val_mul3 w0K_val (xPosK_val _ t) w0K_val]
    rfl
  · exact xLongK_val _

theorem frameConjK_val (k : ℕ) :
    (frameConjK k).val.val = rowsMatrix 22 (Native.glFrameConjRows k) := by
  unfold frameConjK Native.glFrameConjRows
  split_ifs
  · rw [rowsMatrix_idRows]
    rfl
  · exact δ1hK_val
  · rw [val_val_mul, δ1hK_val, δ0hK_val, rowsMatrix_mulRows]
  · exact w1K_val
  · rw [val_val_mul, w1K_val, δ1hK_val, rowsMatrix_mulRows]
  · rw [val_mul3 w1K_val δ1hK_val δ0hK_val]

end Rows

end CFSG.Sporadic.Co2Smith
