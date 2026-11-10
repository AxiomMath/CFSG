
module

public import CFSG.Monster.B.TwoA.Fischer.CertGramBase
public meta import CFSG.Monster.B.TwoA.Fischer.CertGramBase
public meta import Certificates.Data.CFSGNative.MonsterB.BinaryRank
public import CFSG.Monster.B.TwoA.Fischer.CertFixedInputs
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

@[expose] public section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.Monster.B.TwoA.Fischer.Cert

open CFSG.Monster.B.Fischer CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native CFSG.Sporadic.SmallF2
  CFSG.Sporadic.SmallF2.Native CFSG.Monster.B.Binary CFSG.Monster.B.Binary.Native
open scoped Matrix

def fMat (k : ℕ) : Matrix (Fin 78) (Fin 78) (ZMod 2) := (rowsMatrix 78 (fColArr[k]!))ᵀ

theorem mask_bits :
    (List.range 22).filter (fun c => (5461 : ℕ).testBit c) = [0, 2, 4, 6, 8, 10, 12] := by
  decide

theorem fMat_mulVec (k v : ℕ) : fMat k *ᵥ toVecD 78 v = toVecD 78 (vecMulN 78 (fColArr[k]!) v) :=
  transpose_mulVec 78 _ v

theorem subOneRows_row (k : ℕ) (i : Fin 78) :
    (fMat k - 1) i = toVecD 78 ((transposeRows 78 (fColArr[k]!))[(i : ℕ)]! ^^^ (1 <<< (i : ℕ))) :=
  transpose_sub_one_row 78 _ i

theorem mem_subOneRows {ks : List ℕ} {r : ℕ} :
    r ∈ subOneRows ks ↔ ∃ k ∈ ks, ∃ i : Fin 78, toVecD 78 r = (fMat k - 1) i ∧
      r = (transposeRows 78 (fColArr[k]!))[(i : ℕ)]! ^^^ (1 <<< (i : ℕ)) := by
  rw [subOneRows, List.mem_flatMap]
  constructor
  · rintro ⟨k, hk, hr⟩
    obtain ⟨i, hi, rfl⟩ := List.mem_map.1 hr
    exact ⟨k, hk, ⟨i, List.mem_range.1 hi⟩, (subOneRows_row k ⟨i, List.mem_range.1 hi⟩).symm,
      rfl⟩
  · rintro ⟨k, hk, i, -, rfl⟩
    exact ⟨k, hk, List.mem_map.2 ⟨i, List.mem_range.2 i.2, rfl⟩⟩

theorem dotProduct_subOneRows {ks : List ℕ} {v : Fin 78 → ZMod 2}
    (hv : ∀ k ∈ ks, fMat k *ᵥ v = v) : ∀ r ∈ subOneRows ks, toVecD 78 r ⬝ᵥ v = 0 := by
  intro r hr
  obtain ⟨k, hk, i, hri, -⟩ := mem_subOneRows.1 hr
  have h0 : (fMat k - 1) *ᵥ v = 0 := by
    rw [Matrix.sub_mulVec, Matrix.one_mulVec, hv k hk, sub_self]
  rw [hri]
  exact congrFun h0 i

theorem range_stack_row (ks : List ℕ) {ι' : Type*} (e : ι' → ℕ) (he : ∀ k, k ∈ ks ↔ ∃ t, e t = k) :
    Set.range (stackSubOne fun t : ι' => fMat (e t)).row =
      {w | ∃ v ∈ subOneRows ks, toVecD 78 v = w} := by
  ext w
  constructor
  · rintro ⟨⟨t, i⟩, rfl⟩
    refine ⟨_, mem_subOneRows.2 ⟨e t, (he _).2 ⟨t, rfl⟩, i, (subOneRows_row (e t) i).symm, rfl⟩,
      (subOneRows_row (e t) i).symm⟩
  · rintro ⟨v, hv, rfl⟩
    obtain ⟨k, hk, i, hvi, -⟩ := mem_subOneRows.1 hv
    obtain ⟨t, rfl⟩ := (he k).1 hk
    exact ⟨(t, i), hvi.symm⟩

theorem span_clique_eq :
    Submodule.span (ZMod 2) (Set.range fun c : Fin 22 => toVecD 78 (labelCoord c)) =
      listSpan 78 ((List.range 22).map labelCoord) := by
  rw [listSpan]
  congr 1
  ext w
  constructor
  · rintro ⟨c, rfl⟩
    exact ⟨_, List.mem_map.2 ⟨c, List.mem_range.2 c.2, rfl⟩, rfl⟩
  · rintro ⟨v, hv, rfl⟩
    obtain ⟨c, hc, rfl⟩ := List.mem_map.1 hv
    exact ⟨⟨c, List.mem_range.1 hc⟩, rfl⟩

end CFSG.Monster.B.TwoA.Fischer.Cert
