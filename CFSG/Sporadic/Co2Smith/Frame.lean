module

public import CFSG.Sporadic.Co2Smith.Valid
public import CFSG.Sporadic.Co2Smith.Chain
public import Certificates.Certificate16011

public section

namespace CFSG.Sporadic.Co2Smith

open CFSG.Sporadic.Co2Cert CFSG.Sporadic.SmallF2 CFSG.Sporadic.SmallF2.Native Matrix

attribute [local irreducible] Matrix.instHMulOfFintypeOfMulOfAddCommMonoid

@[expose] noncomputable def frE
    (i : ℕ) : K := mWord Native.frameWords[i]!

theorem frameWords_letters :
    ∀ i < 10, ∀ k ∈ Native.frameWords[i]!, k = 2 ∨ k = 3 :=
  Certificates.certificate16011

theorem frameWords_size : Native.frameWords.size = 10 := rfl

theorem frameWords_lt
    {i : ℕ} (hi : i < 10) : ∀ k ∈ Native.frameWords[i]!, k < 4 := by
  intro k hk
  rcases frameWords_letters i hi k hk with rfl | rfl <;> norm_num

theorem fRows_get {i : ℕ} (hi : i < 10) :
    (Native.fRows seedRowsArr)[i]! = Native.mRows seedRowsArr Native.frameWords[i]! :=
  getElem!_map_of_lt _ _ (by rw [frameWords_size]; exact hi)

theorem frE_val
    {i : ℕ} (hi : i < 10) :
    (frE i).val.val = rowsMatrix 22 (Native.fRows seedRowsArr)[i]! := by
  rw [fRows_get hi, frE, mWord_val _ (frameWords_lt hi)]

theorem frE_mem_S0
    {i : ℕ} (hi : i < 10) : frE i ∈ S0 :=
  mWord_mem_S0 _ (frameWords_letters i hi)

theorem validM_fRows
    {i : ℕ} (hi : i < 10) :
    Native.validM (Native.fRows seedRowsArr)[i]! = true := by
  rw [fRows_get hi]
  exact validM_mRows (frameWords_lt hi)

theorem frame_spec :
    (Native.fRows seedRowsArr).size = 10 ∧
    (∀ x < 3,
        powRows 22 (Native.fRows seedRowsArr)[2 * x]! 3 = idRows 22 ∧
          mulRows 22 (Native.fRows seedRowsArr)[2 * x + 1]! (Native.fRows seedRowsArr)[2 * x + 1]! =
            idRows 22 ∧
            mulRows 22 (mulRows 22 (Native.fRows seedRowsArr)[2 * x + 1]!
              (Native.fRows seedRowsArr)[2 * x]!) (Native.fRows seedRowsArr)[2 * x + 1]! =
              mulRows 22 (Native.fRows seedRowsArr)[2 * x]! (Native.fRows seedRowsArr)[2 * x]!) ∧
      (∀ x < 3, ∀ x_1 < 3, x = x_1 ∨ ∀ x_2 < 2, ∀ x_3 < 2,
        Native.commRows (Native.fRows seedRowsArr)[2 * x + x_2]!
          (Native.fRows seedRowsArr)[2 * x_1 + x_3]! = true) ∧
        (∀ x < 6,
            Native.conjTo (Native.fRows seedRowsArr)[6]! (Native.fRows seedRowsArr)[x]!
                  (Native.fRows seedRowsArr)[(2 * if x / 2 = 0 then 1 else if x / 2 = 1 then 0
                    else x / 2) + x % 2]! = true ∧
              Native.conjTo (Native.fRows seedRowsArr)[7]! (Native.fRows seedRowsArr)[x]!
                  (Native.fRows seedRowsArr)[(2 * if x / 2 = 1 then 2 else if x / 2 = 2 then 1
                    else x / 2) + x % 2]! = true) ∧
          powRows 22 (Native.fRows seedRowsArr)[8]! 5 = idRows 22 ∧
            Native.commRows (Native.fRows seedRowsArr)[8]! (Native.fRows seedRowsArr)[0]! = true ∧
              Native.commRows (Native.fRows seedRowsArr)[8]! (Native.fRows seedRowsArr)[1]! = true ∧
                mulRows 22 (Native.fRows seedRowsArr)[9]! (Native.fRows seedRowsArr)[8]! =
                    mulRows 22 (mulRows 22 (Native.fRows seedRowsArr)[8]!
                      (Native.fRows seedRowsArr)[8]!) (Native.fRows seedRowsArr)[9]! ∧
                  Native.commRows (Native.fRows seedRowsArr)[9]! (Native.fRows seedRowsArr)[0]! =
                    true ∧
                    (∀ x ∈ Native.pinRels,
                        powRows 22 (mulRows 22 (Native.fRows seedRowsArr)[8]!
                          (Native.wRows (Native.fRows seedRowsArr) x.1)) x.2 = idRows 22) ∧
                      Native.wRows (Native.fRows seedRowsArr) Native.genAWord =
                          Native.mRows seedRowsArr [2] ∧
                        Native.wRows (Native.fRows seedRowsArr) Native.genBWord =
                          Native.mRows seedRowsArr [3] := by
  have h := frame_check
  simp only [Native.frameOK, Bool.and_eq_true, beq_iff_eq, List.all_eq_true, List.mem_range,
    Bool.or_eq_true, and_assoc] at h
  exact h

theorem frE_x_pow :
    frE 8 ^ 5 = 1 := by
  apply eq_of_val_eq
  rw [pow_val, frE_val (by norm_num), ← rowsMatrix_powRows, frame_spec.2.2.2.2.1,
    rowsMatrix_idRows]
  rfl

end CFSG.Sporadic.Co2Smith
