module

public import CFSG.Monster.B.TwoA.Fischer.GramDataFiles
public import CFSG.Monster.B.Fischer.CanonicalGroup
public import CFSG.Sporadic.HS.SmallF2Spec

public section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.Monster.B.TwoA.Fischer.Cert

open CFSG.Monster.B.Fischer CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native
  CFSG.Sporadic.SmallF2.Native

@[expose] def hexDigitVal (c : Char) : ℕ :=
  if '0' ≤ c ∧ c ≤ '9' then c.toNat - '0'.toNat
  else if 'a' ≤ c ∧ c ≤ 'f' then c.toNat - 'a'.toNat + 10
  else if 'A' ≤ c ∧ c ≤ 'F' then c.toNat - 'A'.toNat + 10 else 0

@[expose] def parseHexNat (s : String) : ℕ :=
  (if s.startsWith "0x" then s.drop 2 else s).foldl (fun acc c => acc * 16 + hexDigitVal c) 0

@[expose] def basisPtArr : Array ℕ := dAlgRec.basisNativePoints.toArray

@[expose] def basisPt (i : ℕ) : ℕ := basisPtArr[i]!

@[expose] def labelWordArr : Array (List ℕ) := dAdjRec.nativeBasisLabelWords.toArray

@[expose] def labelWord (i : ℕ) : List ℕ := labelWordArr[i]!

@[expose] def ncRowArr : Array ℕ := (dAlgRec.noncommutationBasisRowsHex.map parseHexNat).toArray

@[expose] def ncRow (i : ℕ) : ℕ := ncRowArr[i]!

@[expose] def gramRowArr : Array ℕ := dAdjRec.nativeGramMinorRows.toArray

@[expose] def gramRow (i : ℕ) : ℕ := gramRowArr[i]!

@[expose] def labelCoordArr : Array ℕ := dAlgRec.noncommutationRowCoordinates.toArray

@[expose] def labelCoord (y : ℕ) : ℕ := labelCoordArr[y]!

@[expose] def fColArr : Array (Array ℕ) := (dAdjRec.fGeneratorColumns.map List.toArray).toArray

@[expose] def fourColArr : Array (Array ℕ) :=
  (dAlgRec.fourModuleGeneratorColumns.map List.toArray).toArray

@[expose] def bTableArr : Array (Array ℕ) := (dAlgRec.basisProductTable.map List.toArray).toArray

@[expose] def bTable (i j : ℕ) : ℕ := (bTableArr[i]!)[j]!

@[expose] noncomputable def jWord :
    List ℕ → Equiv.Perm Y
  | [] => 1
  | j :: w => jGen j * jWord w

@[expose] noncomputable def jLabel
    (w : List ℕ) : Equiv.Perm Y := jWord w * tPerm * (jWord w)⁻¹

@[expose] def jWordArr : List ℕ → Array ℕ
  | [] => idA 3510
  | j :: w => compA 3510 (indCandidate j) (jWordArr w)

@[expose] def jLabelArr (w : List ℕ) : Array ℕ :=
  compA 3510 (compA 3510 (jWordArr w) indCentral) (invCand 3510 (jWordArr w))

@[expose] def RepY
    (t : Array ℕ) (g : Equiv.Perm Y) : Prop := ∀ y : Y, t[(ι y : ℕ)]! = ι (g y)

theorem repY_jGen
    {k : ℕ} (hk : k < 13) : RepY (indCandidate k) (jGen k) := fun y =>
  (ι_jGen hk y).symm

theorem repY_compA
    {t u : Array ℕ} {g h : Equiv.Perm Y} (ht : RepY t g) (hu : RepY u h) :
    RepY (compA 3510 t u) (g * h) := fun y => by
  rw [compA_get (ι y).2, hu y, ht (h y), Equiv.Perm.mul_apply]

theorem repY_idA :
    RepY (idA 3510) 1 := fun y => by
  rw [idA_get (ι y).2]
  rfl

theorem repY_inv
    {t r : Array ℕ} {g : Equiv.Perm Y} (ht : RepY t g) (h : isInvA 3510 t r = true) :
    RepY r g⁻¹ := fun y => by
  have hz := (isInvA_spec h (ι (g⁻¹ y)).2).2
  have hg : g (g⁻¹ y) = y := by rw [← Equiv.Perm.mul_apply, mul_inv_cancel, Equiv.Perm.one_apply]
  rw [ht (g⁻¹ y), hg] at hz
  exact hz

theorem repY_jWordArr :
    ∀ w : List ℕ, (∀ j ∈ w, j < 13) → RepY (jWordArr w) (jWord w)
  | [], _ => repY_idA
  | j :: w, hw => repY_compA (repY_jGen (hw j List.mem_cons_self))
      (repY_jWordArr w fun k hk => hw k (List.mem_cons_of_mem j hk))

theorem indCandidate_twelve : indCandidate 12 = indCentral := by
  simp [indCandidate]

theorem repY_tPerm :
    RepY indCentral tPerm := by
  have h := repY_jGen (k := 12) (by norm_num)
  rwa [indCandidate_twelve, jGen_twelve] at h

theorem repY_jLabelArr
    {w : List ℕ} (hw : ∀ j ∈ w, j < 13)
    (hinv : isInvA 3510 (jWordArr w) (invCand 3510 (jWordArr w)) = true) :
    RepY (jLabelArr w) (jLabel w) :=
  repY_compA (repY_compA (repY_jWordArr w hw) repY_tPerm) (repY_inv (repY_jWordArr w hw) hinv)

@[expose] def supportBits (t : Array ℕ) : ℕ := ofBits 3510 fun q => t[q]! != q

theorem testBit_supportBits_ι
    {t : Array ℕ} {g : Equiv.Perm Y} (ht : RepY t g) (y : Y) :
    (supportBits t).testBit (ι y) = true ↔ g y ≠ y := by
  rw [supportBits, CFSG.Sporadic.SmallF2.ofBits_testBit, decide_eq_true (ι y).2, Bool.true_and,
    ht y, bne_iff_ne]
  exact ⟨fun h e => h (by rw [e]), fun h e => h (ι_bijective.1 (Fin.ext e))⟩

theorem ι_o :
    (ι o : ℕ) = 22 := by
  have h := ι_wv (u := 0) (by norm_num)
  rwa [wv_zero] at h

end CFSG.Monster.B.TwoA.Fischer.Cert
