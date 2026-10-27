module

public import CFSG.Sporadic.Co2Smith.Cat
public import CFSG.Sporadic.Co2Smith.CheckInputs
public import Certificates.Data.CFSGNative.Co2Smith.Check

public section

namespace CFSG.Sporadic.Co2Smith

open CFSG.Sporadic.Co2Cert CFSG.Sporadic.SmallF2 CFSG.Sporadic.SmallF2.Native Matrix

noncomputable abbrev z0 : K := co2SeedA

theorem z0_val : z0.val.val = rowsMatrix 22 co2RowsA := by
  rw [co2SeedA_val, rowsMatrix_co2RowsA]

theorem seedB_val : co2SeedB.val.val = rowsMatrix 22 co2RowsB := by
  rw [co2SeedB_val, rowsMatrix_co2RowsB]

theorem seedLetters_rows : seedLetters.rows = seedRowsArr := rfl

@[expose] noncomputable def aE : K := lWord seedLetters Native.aWord

@[expose] noncomputable def bE : K := lWord seedLetters Native.bWord

theorem aE_val :
    aE.val.val = rowsMatrix 22 (Native.wRows seedRowsArr Native.aWord) :=
  lWord_val seedLetters _ (by rw [seedLetters_rows]; decide +kernel)

theorem bE_val :
    bE.val.val = rowsMatrix 22 (Native.wRows seedRowsArr Native.bWord) :=
  lWord_val seedLetters _ (by rw [seedLetters_rows]; decide +kernel)

@[expose] noncomputable def mixLetters : Letters where
  elt k := if k = 0 then co2SeedA else if k = 1 then co2SeedB else if k = 2 then aE else bE
  rows := Native.letters seedRowsArr
  val_eq k hk := by
    have hk' : k < 4 := hk
    rcases (show k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3 by omega) with rfl | rfl | rfl | rfl
    · exact z0_val
    · exact seedB_val
    · exact aE_val
    · exact bE_val

@[expose] noncomputable def mWord
    (w : List ℕ) : K := lWord mixLetters w

theorem mWord_val (w : List ℕ) (hw : ∀ k ∈ w, k < 4) :
    (mWord w).val.val = rowsMatrix 22 (Native.mRows seedRowsArr w) :=
  lWord_val mixLetters w hw

theorem mWord_two : mWord [2] = aE := by
  rw [mWord, lWord, lWord, mul_one]
  rfl

theorem mWord_three : mWord [3] = bE := by
  rw [mWord, lWord, lWord, mul_one]
  rfl

end CFSG.Sporadic.Co2Smith
