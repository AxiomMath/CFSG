module

public import CFSG.Monster.B.TwoA.Fischer.CertSieve
public meta import CFSG.Monster.B.TwoA.Fischer.CertSieve
public import CFSG.Monster.B.TwoA.Fischer.CertSeedInputs
public import Certificates.Certificate3068
public import Certificates.Certificate3030
public import Certificates.Certificate3031
public import Certificates.Certificate3033
public import Certificates.Certificate3017
public import Certificates.Certificate3029
public import Certificates.Certificate3034
public import Certificates.Certificate3035
public import Certificates.Certificate3036
public import Certificates.Certificate16010
public import Certificates.Certificate16023

public section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.Monster.B.TwoA.Fischer.Cert

open CFSG.Monster.B.Fischer CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native CFSG.Sporadic.SmallF2
  CFSG.Sporadic.SmallF2.Native CFSG.Monster.B.Binary CFSG.Monster.B.Binary.Native
open scoped Matrix

@[expose] def fourMat (k : ℕ) : Matrix (Fin 78) (Fin 78) (ZMod 2) :=
  (rowsMatrix 78 (fourColArr[k]!))ᵀ

@[expose] def gramForm (x y : Fin 78 → ZMod 2) : ZMod 2 := x ⬝ᵥ (rowsMatrix 78 gramRowArr *ᵥ y)

@[expose] def rootOp (z x : Fin 78 → ZMod 2) : Fin 78 → ZMod 2 :=
  x + tableBracket z x + gramForm z x • z

theorem fourCheck_eq_true : fourCheck = true :=
  Certificates.certificate3068.1

theorem seedPre_eq : seedPre = 16058837531770935235962 :=
  Certificates.certificate3068.2.1

theorem rootOpNum_eq :
    rootOpNum 949 16058837531770935235962 = 16058837527637121392057 :=
  Certificates.certificate3068.2.2.1

theorem seedZeroCheck_eq_true : seedZeroCheck = true :=
  Certificates.certificate3068.2.2.2

theorem seedLabels_length : seedLabels.length = 126 := by
  decide +kernel

theorem fourColArr_size_of {k : ℕ} (hk : k < 4) :
    (fourColArr[k]!).size = 78 := by
  have h := fourCheck_eq_true
  rw [fourCheck, Bool.and_eq_true, Bool.and_eq_true, beq_iff_eq, Array.all_eq_true] at h
  have hk' : k < fourColArr.size := h.1.1 ▸ hk
  rw [getElem!_pos fourColArr k hk']
  exact beq_iff_eq.1 (h.1.2 k hk')

theorem fourCol_eq {k i : ℕ} (hk : k < 4) (hi : i < 78) :
    (fourColArr[k]!)[i]! = labelCoord ((indCandidate (fourGen k))[basisPt i]!) := by
  have h := fourCheck_eq_true
  rw [fourCheck, Bool.and_eq_true] at h
  exact beq_iff_eq.1 (List.all_eq_true.1 (List.all_eq_true.1 h.2 k (List.mem_range.2 hk)) i
    (List.mem_range.2 hi))

theorem fourGen_lt {k : ℕ} (hk : k < 4) : fourGen k < 13 := by
  interval_cases k <;> decide

theorem fourMat_col
    {k : ℕ} (hk : k < 4) (i : Fin 78)
    (y : Y)
    (hy : (ι y : ℕ) = basisPt i) :
    fourMat k *ᵥ Pi.single i 1 = toVecD 78 (labelCoord (ι (jGen (fourGen k) y))) := by
  rw [Matrix.mulVec_single_one]
  funext r
  have hi : (i : ℕ) < (fourColArr[k]!).size := by
    rw [fourColArr_size_of hk]
    exact i.2
  change rowsMatrix 78 (fourColArr[k]!) i r = _
  rw [rowsMatrix_apply, getElem?_pos (fourColArr[k]!) (i : ℕ) hi, Option.getD_some,
    ← getElem!_pos (fourColArr[k]!) (i : ℕ) hi, fourCol_eq hk i.2, ← hy,
    ι_jGen (fourGen_lt hk)]

theorem fourMat_mulVec (k v : ℕ) :
    fourMat k *ᵥ toVecD 78 v = toVecD 78 (vecMulN 78 (fourColArr[k]!) v) :=
  transpose_mulVec 78 _ v

theorem wordProd_mulVec : ∀ (w : List ℕ) (x : ℕ),
    (w.map fourMat).prod *ᵥ toVecD 78 x =
      toVecD 78 (w.foldr (fun k acc => vecMulN 78 (fourColArr[k]!) acc) x)
  | [], x => by rw [List.map_nil, List.prod_nil, Matrix.one_mulVec, List.foldr_nil]
  | k :: w, x => by
    rw [List.map_cons, List.prod_cons, ← Matrix.mulVec_mulVec, wordProd_mulVec w x,
      fourMat_mulVec, List.foldr_cons]

theorem rootOp_toVecD (z x : ℕ) :
    rootOp (toVecD 78 z) (toVecD 78 x) = toVecD 78 (rootOpNum z x) := by
  rw [rootOp, gramForm, tableBracket_toVecD, rowsMatrix_mulVec, toVecD_dotProduct, rootOpNum,
    toVecD_xor, toVecD_xor]
  by_cases h : dotBit 78 z (vecMulN 78 (transposeRows 78 gramRowArr) x) = true
  · rw [ite_eq_left h, ite_eq_left h, one_smul]
  · rw [ite_eq_right h, ite_eq_right h, zero_smul, toVecD_zero]

theorem fischer_seed_certificate :
    (List.range 4).map fourGen = [0, 1, 2, 12] ∧
    (∀ k < 4, ∀ i : Fin 78, ∀ y : Y, (ι y : ℕ) = basisPt i →
      fourMat k *ᵥ Pi.single i 1 = toVecD 78 (labelCoord (ι (jGen (fourGen k) y)))) ∧
    seedWord = [3, 2, 0, 2, 3, 1, 2, 0, 2, 3] ∧
    (seedWord.map fourMat).prod *ᵥ toVecD 78 949 = toVecD 78 16058837531770935235962 ∧
    rootOp (toVecD 78 949) (toVecD 78 16058837531770935235962) =
      toVecD 78 16058837527637121392057 ∧
    (∀ y : Y, tableBracket (toVecD 78 16058837527637121392057) (toVecD 78 (labelCoord (ι y))) = 0
      ↔ (ι y : ℕ) ∈ seedLabels) ∧
    seedLabels.length = 126 := by
  refine ⟨by decide, fun _ hk i y hy => fourMat_col hk i y hy, rfl, ?_, ?_, fun y => ?_,
    seedLabels_length⟩
  · rw [wordProd_mulVec, ← seedPre, seedPre_eq]
  · rw [rootOp_toVecD, rootOpNum_eq]
  · have h : ((List.range 3510).all fun q =>
        decide (vecMulN 78 (adCols 16058837527637121392057) (labelCoord q) < 2 ^ 78) &&
          (vecMulN 78 (adCols 16058837527637121392057) (labelCoord q) == 0) ==
            seedLabels.contains q) = true := seedZeroCheck_eq_true
    have hq := List.all_eq_true.1 h (ι y) (List.mem_range.2 (ι y).2)
    rw [Bool.and_eq_true, decide_eq_true_eq] at hq
    rw [tableBracket_toVecD, toVecD_eq_zero_iff hq.1, ← beq_iff_eq, beq_iff_eq.1 hq.2,
      List.contains_iff_mem]

end CFSG.Monster.B.TwoA.Fischer.Cert
