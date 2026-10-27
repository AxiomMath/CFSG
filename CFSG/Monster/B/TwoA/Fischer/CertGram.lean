
module

public import CFSG.Monster.B.TwoA.Fischer.CertGramBase

public import CFSG.Monster.B.TwoA.Fischer.CertData
public import Certificates.Data.CFSGNative.MonsterB.Co2Matrix
public meta import CFSG.Monster.B.TwoA.Fischer.CertData
public meta import Certificates.Data.CFSGNative.MonsterB.Co2Matrix
public meta import Certificates.Data.CFSGNative.HS.SmallF2
public import CFSG.Monster.B.TwoA.Fischer.CertGramInputs
public import Certificates.Certificate3065
public import CFSG.Monster.B.Fischer.HexadStabInputs
public import CFSG.Monster.B.Fischer.HexadDiagInputs
public import CFSG.Monster.B.Fischer.InducedEncodingInputs
public import Certificates.Data.CFSGNative.Mathieu.M24
public import Certificates.Data.CFSGNative.Mathieu.M22
public import CFSG.Monster.B.Fischer.InducedChecksInputs
public import CFSG.Monster.B.Fischer.InducedOrbitChecksInputs
public import CFSG.Monster.B.Fischer.InducedOrbitChecks
public import CFSG.Monster.B.Fischer.InducedSet
public import CFSG.Monster.B.Fischer.InducedCodeInputs
public import CFSG.Monster.B.Fischer.InducedChecks
public import Certificates.Certificate3065Base

public section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.Monster.B.TwoA.Fischer.Cert

open CFSG.Monster.B.Fischer CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native CFSG.Sporadic.SmallF2
  CFSG.Sporadic.SmallF2.Native
open scoped Matrix

theorem gramWordCheck_eq_true : gramWordCheck = true :=
  Certificates.certificate3065.1

theorem gramInvCheck_eq_true : gramInvCheck = true :=
  Certificates.certificate3065.2.1

theorem coordCheck_eq_true : coordCheck = true :=
  Certificates.certificate3065.2.2.1

theorem basisPt_list :
    (List.range 78).map basisPt =
      [0, 1, 2, 3, 4, 6, 7, 8, 10, 12, 14, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32, 34, 38,
        39, 40, 42, 54, 55, 56, 57, 58, 59, 60, 62, 63, 64, 66, 70, 71, 72, 74, 86, 87, 88, 90,
        94, 102, 118, 150, 151, 152, 154, 158, 166, 182, 278, 279, 282, 286, 294, 310, 406, 534,
        535, 538, 566, 1046, 1047, 1078, 1110, 1174, 1270, 1334, 1462, 1686, 1942, 2326] :=
  Certificates.certificate3065.2.2.2

theorem gramWordCheck_spec {i : ℕ} (hi : i < 78) :
    (∀ j ∈ labelWord i, j < 13) ∧ (jWordArr (labelWord i))[22]! = basisPt i ∧
      isInvA 3510 (jWordArr (labelWord i)) (invCand 3510 (jWordArr (labelWord i))) = true ∧
      supportBits (jLabelArr (labelWord i)) = ncRow i ∧
      gramRow i = ofBits 78 (fun k => (ncRow i).testBit (basisPt k)) := by
  have h := List.all_eq_true.1 gramWordCheck_eq_true i (List.mem_range.2 hi)
  simp only [Bool.and_eq_true, beq_iff_eq, List.all_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩ := h
  exact ⟨h1, h2, h3, h4, h5⟩

theorem ι_jWord_o
    {i : ℕ} (hi : i < 78) :
    (ι (jWord (labelWord i) o) : ℕ) = basisPt i := by
  obtain ⟨hw, h22, -⟩ := gramWordCheck_spec hi
  have h := repY_jWordArr (labelWord i) hw o
  rw [ι_o] at h
  rw [← h, h22]

theorem repY_label
    {i : ℕ} (hi : i < 78) : RepY
    (jLabelArr (labelWord i)) (jLabel (labelWord i)) :=
  repY_jLabelArr (gramWordCheck_spec hi).1 (gramWordCheck_spec hi).2.2.1

theorem jLabel_ne_iff
    {i : ℕ} (hi : i < 78) (y : Y) :
    jLabel (labelWord i) y ≠ y ↔ (ncRow i).testBit (ι y) = true := by
  rw [← (gramWordCheck_spec hi).2.2.2.1, testBit_supportBits_ι (repY_label hi) y]

theorem testBit_gramRow {i k : ℕ} (hi : i < 78) (hk : k < 78) :
    (gramRow i).testBit k = (ncRow i).testBit (basisPt k) := by
  rw [(gramWordCheck_spec hi).2.2.2.2, ofBits_testBit, decide_eq_true hk, Bool.true_and]

theorem fischer_gram_minor_certificate :
    (List.range 78).map basisPt =
      [0, 1, 2, 3, 4, 6, 7, 8, 10, 12, 14, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32, 34, 38,
        39, 40, 42, 54, 55, 56, 57, 58, 59, 60, 62, 63, 64, 66, 70, 71, 72, 74, 86, 87, 88, 90,
        94, 102, 118, 150, 151, 152, 154, 158, 166, 182, 278, 279, 282, 286, 294, 310, 406, 534,
        535, 538, 566, 1046, 1047, 1078, 1110, 1174, 1270, 1334, 1462, 1686, 1942, 2326] ∧
    (∀ i < 78, ∀ j ∈ labelWord i, j < 13) ∧
    (∀ i < 78, (ι (jWord (labelWord i) o) : ℕ) = basisPt i) ∧
    (∀ i < 78, ∀ y : Y, jLabel (labelWord i) y ≠ y ↔ (ncRow i).testBit (ι y) = true) ∧
    (∀ i < 78, ∀ k < 78, (gramRow i).testBit k = (ncRow i).testBit (basisPt k)) ∧
    (rowsMatrix 78 gramRowArr).det ≠ 0 := by
  refine ⟨basisPt_list, fun _ hi => (gramWordCheck_spec hi).1, fun _ hi => ι_jWord_o hi,
    fun _ hi => jLabel_ne_iff hi, fun _ hi _ hk => testBit_gramRow hi hk, ?_⟩
  have h : mulRows 78 gramRowArr (invMat 78 gramRowArr) = idRows 78 :=
    beq_iff_eq.1 gramInvCheck_eq_true
  refine Matrix.det_ne_zero_of_right_inverse (B := rowsMatrix 78 (invMat 78 gramRowArr)) ?_
  rw [← rowsMatrix_mulRows, h, rowsMatrix_idRows]

theorem fischer_label_coordinates_certificate :
    (∀ i < 78, labelCoord (basisPt i) = 2 ^ i) ∧
    ∀ y : Y, rowsMatrix 78 gramRowArr *ᵥ toVecD 78 (labelCoord (ι y)) =
      fun i : Fin 78 => if (ncRow i).testBit (ι y) then (1 : ZMod 2) else 0 := by
  have h := coordCheck_eq_true
  simp only [coordCheck, Bool.and_eq_true, List.all_eq_true, List.mem_range, beq_iff_eq] at h
  refine ⟨h.1, fun y => ?_⟩
  rw [rowsMatrix_mulVec, h.2 _ (ι y).2]
  funext i
  exact toVecD_ofBits 78 _ i

end CFSG.Monster.B.TwoA.Fischer.Cert
