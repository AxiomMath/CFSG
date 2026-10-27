module

public import CFSG.Sporadic.Co2Smith.Res
public import CFSG.Certificates.ExtraspecialNormalForm
public import CFSG.Sporadic.Co2Smith.ClassSize

public section

namespace CFSG.Sporadic.Co2Smith

open CFSG.Sporadic.Co2Cert CFSG.Sporadic.SmallF2 CFSG.Sporadic.SmallF2.Native Matrix
open scoped Matrix

attribute [local irreducible] Matrix.instHMulOfFintypeOfMulOfAddCommMonoid

@[expose] def aR : Array ℕ := Native.mRows seedRowsArr [2]

@[expose] def bR : Array ℕ := Native.mRows seedRowsArr [3]

@[expose] def hR : Array (Array ℕ) := Native.hRows seedRowsArr

theorem elements_spec :
    powRows 22 aR 3 = idRows 22 ∧ powRows 22 bR 7 = idRows 22 ∧
    Native.commRows aR co2RowsA = true ∧ Native.commRows bR co2RowsA = true ∧
    Native.colAct aR Native.wFix = Native.wFix ∧ Native.colAct bR Native.wFix = Native.wFix ∧
    hR.size = 8 ∧
    (∀ i < 8, mulRows 22 hR[i]! hR[i]! = idRows 22 ∧ Native.commRows hR[i]! co2RowsA = true ∧
      mulRows 22 hR[i]! (Native.subId co2RowsA) = Native.subId co2RowsA ∧
      ∀ j < 8, mulRows 22 hR[i]! hR[j]! =
        (if Native.hypC i j = true then mulRows 22 (mulRows 22 hR[j]! hR[i]!) co2RowsA
          else mulRows 22 hR[j]! hR[i]!)) ∧
    (∀ s < 2, ∀ v < 255,
      Native.colAct (Native.nfRows seedRowsArr hR s (v + 1)) Native.wFix ≠ Native.wFix) := by
  have h := elements_check
  simp only [Native.elementsOK, Bool.and_eq_true, beq_iff_eq, List.all_eq_true, List.mem_range,
    and_assoc, bne_iff_ne, ne_eq] at h
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, -, -, h9⟩ := h
  exact ⟨h1, h2, h3, h4, h5, h6, h7, fun i hi => h8 i hi, fun s hs v hv => h9 s hs v hv⟩

theorem pow_val (u : K) (n : ℕ) : (u ^ n).val.val = u.val.val ^ n := by
  induction n with
  | zero => rfl
  | succ n ih => rw [pow_succ, val_val_mul, ih, pow_succ]

theorem aE_val' : aE.val.val = rowsMatrix 22 aR := by
  rw [← mWord_two, mWord_val _ (by decide)]
  rfl

theorem bE_val' : bE.val.val = rowsMatrix 22 bR := by
  rw [← mWord_three, mWord_val _ (by decide)]
  rfl

theorem comm_of_commRows {u v : K} {X Y : Array ℕ} (hu : u.val.val = rowsMatrix 22 X)
    (hv : v.val.val = rowsMatrix 22 Y) (h : Native.commRows X Y = true) : u * v = v * u :=
  eq_of_val_eq (by
    rw [val_val_mul, val_val_mul, hu, hv, ← rowsMatrix_mulRows, ← rowsMatrix_mulRows,
      beq_iff_eq.mp h])

theorem aE_comm :
    aE * z0 = z0 * aE := comm_of_commRows aE_val' z0_val elements_spec.2.2.1

theorem bE_comm :
    bE * z0 = z0 * bE := comm_of_commRows bE_val' z0_val elements_spec.2.2.2.1

theorem aE_mem_Cz :
    aE ∈ Cz := mem_Cz_of_comm aE_comm

theorem bE_mem_Cz :
    bE ∈ Cz := mem_Cz_of_comm bE_comm

theorem aE_fix :
    aE.val.val *ᵥ vec Native.wFix = vec Native.wFix := by
  rw [mulVec_vec aE_val', elements_spec.2.2.2.2.1]

theorem bE_fix :
    bE.val.val *ᵥ vec Native.wFix = vec Native.wFix := by
  rw [mulVec_vec bE_val', elements_spec.2.2.2.2.2.1]

@[expose] noncomputable def hE
    (i : Fin 8) : K := mWord Native.hWords[(i : ℕ)]!

theorem hWords_lt : ∀ i < 8, ∀ k ∈ Native.hWords[i]!, k < 4 := by decide +kernel

theorem getElem!_map_of_lt {α β : Type*} [Inhabited α] [Inhabited β] (f : α → β) (a : Array α)
    {i : ℕ} (hi : i < a.size) : (a.map f)[i]! = f a[i]! := by
  rw [getElem!_pos (a.map f) i (by simpa using hi), getElem!_pos a i hi, Array.getElem_map]

theorem hWords_size : Native.hWords.size = 8 := rfl

theorem hR_get (i : Fin 8) : hR[(i : ℕ)]! = Native.mRows seedRowsArr Native.hWords[(i : ℕ)]! :=
  getElem!_map_of_lt _ _ (by rw [hWords_size]; exact i.2)

theorem hE_val
    (i : Fin 8) : (hE i).val.val = rowsMatrix 22 hR[(i : ℕ)]! := by
  rw [hR_get, hE, mWord_val _ (hWords_lt i i.2)]

theorem hE_sq
    (i : Fin 8) : hE i * hE i = 1 := by
  apply eq_of_val_eq
  rw [val_val_mul, hE_val, ← rowsMatrix_mulRows, (elements_spec.2.2.2.2.2.2.2.1 i i.2).1,
    rowsMatrix_idRows]
  rfl

theorem hE_comm
    (i : Fin 8) : hE i * z0 = z0 * hE i :=
  comm_of_commRows (hE_val i) z0_val (elements_spec.2.2.2.2.2.2.2.1 i i.2).2.1

theorem hE_mem_Cz
    (i : Fin 8) : hE i ∈ Cz := mem_Cz_of_comm (hE_comm i)

theorem hE_fix_Zsub
    (i : Fin 8) {v : V} (hv : v ∈ Zsub) : (hE i).val.val *ᵥ v = v := by
  obtain ⟨u, rfl⟩ := hv
  have hm : (hE i).val.val * (z0.val.val - 1) = z0.val.val - 1 := by
    rw [hE_val, z0_val, ← rowsMatrix_subId, ← rowsMatrix_mulRows,
      (elements_spec.2.2.2.2.2.2.2.1 i i.2).2.2.1]
  simp only [zEnd, Matrix.mulVecLin_apply, Matrix.mulVec_mulVec, hm]

@[expose] def hypMat (i j : Fin 8) : ZMod 2 := if Native.hypC i j = true then 1 else 0

theorem hE_rel :
    CFSG.Certificates.ExtraspecialNF.Rel z0 hE hypMat where
  z_sq := seedA_mul_self
  z_comm i := (hE_comm i).symm
  q_sq := hE_sq
  comm i j := by
    apply eq_of_val_eq
    have h := (elements_spec.2.2.2.2.2.2.2.1 i i.2).2.2.2 j j.2
    rw [val_val_mul, hE_val, hE_val, ← rowsMatrix_mulRows, h, hypMat]
    split_ifs
    · rw [rowsMatrix_mulRows, rowsMatrix_mulRows, ← hE_val, ← hE_val, ← z0_val,
        ZMod.val_one, pow_one, val_val_mul, val_val_mul]
    · rw [rowsMatrix_mulRows, ← hE_val, ← hE_val, ZMod.val_zero, pow_zero, mul_one,
        val_val_mul]

end CFSG.Sporadic.Co2Smith
