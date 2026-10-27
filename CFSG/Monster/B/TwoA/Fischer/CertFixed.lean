
module

public import CFSG.Monster.B.TwoA.Fischer.CertFixedBase

public import CFSG.Monster.B.TwoA.Fischer.CertGram
public meta import CFSG.Monster.B.TwoA.Fischer.CertGram
public meta import Certificates.Data.CFSGNative.MonsterB.BinaryRank
public import CFSG.Monster.B.TwoA.Fischer.CertFixedInputs
public import Certificates.Certificate3066
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
public import Certificates.Certificate3066Base

public section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.Monster.B.TwoA.Fischer.Cert

open CFSG.Monster.B.Fischer CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native CFSG.Sporadic.SmallF2
  CFSG.Sporadic.SmallF2.Native CFSG.Monster.B.Binary CFSG.Monster.B.Binary.Native
open scoped Matrix

theorem fShapeCheck_eq_true : fShapeCheck = true :=
  Certificates.certificate3066.1

theorem fColCheck_eq_true : fColCheck = true :=
  Certificates.certificate3066.2.1

theorem fFixCheck_eq_true : fFixCheck = true :=
  Certificates.certificate3066.2.2.1

theorem fRank_check :
    spanRankIs 78 (subOneRows (List.range 12)) 77 = true :=
  Certificates.certificate3066.2.2.2.1

theorem fFree_check :
    freeIs 78 (subOneRows (List.range 12)) [0] = true :=
  Certificates.certificate3066.2.2.2.2.1

theorem cliqueRank_check :
    spanRankIs 78 ((List.range 22).map labelCoord) 11 = true :=
  Certificates.certificate3066.2.2.2.2.2.1

theorem coordNeCheck_eq_true : coordNeCheck = true :=
  Certificates.certificate3066.2.2.2.2.2.2.1

theorem maskSum_eq : maskSum = 949 :=
  Certificates.certificate3066.2.2.2.2.2.2.2

theorem fColArr_size_of {k : ℕ} (hk : k < 12) : (fColArr[k]!).size =
    78 := by
  have h := fShapeCheck_eq_true
  rw [fShapeCheck, Bool.and_eq_true, beq_iff_eq, Array.all_eq_true] at h
  have hk' : k < fColArr.size := h.1 ▸ hk
  have := h.2 k hk'
  rw [getElem!_pos fColArr k hk']
  exact beq_iff_eq.1 this

theorem fCol_eq {k i : ℕ} (hk : k < 12) (hi : i < 78) :
    fCol k i = labelCoord ((indCandidate k)[basisPt i]!) := by
  have h := List.all_eq_true.1 (List.all_eq_true.1 fColCheck_eq_true k (List.mem_range.2 hk)) i
    (List.mem_range.2 hi)
  exact beq_iff_eq.1 h

theorem fColArr_fix {k : ℕ} (hk : k < 12) : vecMulN 78 (fColArr[k]!)
    949 = 949 :=
  beq_iff_eq.1 (List.all_eq_true.1 fFixCheck_eq_true k (List.mem_range.2 hk))

theorem labelCoord_ne {q : ℕ} (hq : q < 3510) : labelCoord q ≠ 949 ∧
    labelCoord q < 2 ^ 78 := by
  have h := List.all_eq_true.1 coordNeCheck_eq_true q (List.mem_range.2 hq)
  rw [Bool.and_eq_true, bne_iff_ne, decide_eq_true_eq] at h
  exact h

theorem fMat_col {k : ℕ} (hk : k < 12) (i : Fin 78) :
    fMat k *ᵥ Pi.single i 1 = toVecD 78 (fCol k i) := by
  rw [Matrix.mulVec_single_one]
  funext r
  have hi : (i : ℕ) < (fColArr[k]!).size := by
    rw [fColArr_size_of hk]
    exact i.2
  change rowsMatrix 78 (fColArr[k]!) i r = _
  rw [rowsMatrix_apply, getElem?_pos (fColArr[k]!) (i : ℕ) hi, Option.getD_some, fCol,
    getElem!_pos (fColArr[k]!) (i : ℕ) hi]

theorem fMat_col_jGen
    {k : ℕ} (hk : k < 12) (i : Fin 78)
    (y : Y)
    (hy : (ι y : ℕ) = basisPt i) :
    fMat k *ᵥ Pi.single i 1 = toVecD 78 (labelCoord (ι (jGen k y))) := by
  rw [fMat_col hk, fCol_eq hk i.2, ← hy, ι_jGen (by omega)]

theorem fMat_fixed {k : ℕ} (hk : k < 12) : fMat k *ᵥ toVecD 78 949 =
    toVecD 78 949 := by
  rw [fMat_mulVec, fColArr_fix hk]

theorem fixed_rank : (stackSubOne fun k : Fin 12 => fMat k).rank = 77
    := by
  rw [rank_eq_finrank_listSpan _ (subOneRows (List.range 12))
    (range_stack_row (List.range 12) (fun k : Fin 12 => (k : ℕ)) fun k =>
      ⟨fun hk => ⟨⟨k, List.mem_range.1 hk⟩, rfl⟩, fun ⟨t, ht⟩ => ht ▸ List.mem_range.2 t.2⟩)]
  exact finrank_listSpan fRank_check

theorem fixed_iff (v : Fin 78 → ZMod 2) :
    (∀ k < 12, fMat k *ᵥ v = v) ↔ v = 0 ∨ v = toVecD 78 949 := by
  constructor
  · intro hv
    obtain ⟨hrs, T, hT, hfree⟩ := freeIs_spec fFree_check
    have hfree0 : ∀ p : Fin 78, T[(p : ℕ)]! = 0 → (p : ℕ) = 0 := fun p hp => by
      have := (hfree p p.2).1 hp
      simpa using this
    have hz : ∀ r ∈ subOneRows (List.range 12), toVecD 78 r ⬝ᵥ toVecD 78 949 = 0 :=
      dotProduct_subOneRows fun k hk => fMat_fixed (List.mem_range.1 hk)
    have key := eq_sum_of_table hrs hT (fun _ => toVecD 78 949) (fun p hp => ⟨hz, fun p' hp' => by
        have e1 := hfree0 p hp
        have e2 := hfree0 p' hp'
        have : p' = p := Fin.ext (e2.trans e1.symm)
        rw [ite_eq_left this, toVecD_apply, e2]
        rfl⟩)
      (dotProduct_subOneRows fun k hk => hv k (List.mem_range.1 hk))
    have h0 : T[0]! = 0 := (hfree 0 (by norm_num)).2 (List.mem_singleton.2 rfl)
    rw [Finset.sum_eq_single (0 : Fin 78) (fun b _ hb => by
        have : T[(b : ℕ)]! ≠ 0 := fun h => hb (Fin.ext (hfree0 b h))
        exact ite_eq_right this)
      (fun h => absurd (Finset.mem_univ _) h)] at key
    have h0' : T[((0 : Fin 78) : ℕ)]! = 0 := h0
    rw [ite_eq_left h0'] at key
    rcases (show ∀ c : ZMod 2, c = 0 ∨ c = 1 by decide) (v 0) with hc | hc
    · left
      rw [key, hc, zero_smul]
    · right
      rw [key, hc, one_smul]
  · rintro (rfl | rfl) k hk
    · exact Matrix.mulVec_zero _
    · exact fMat_fixed hk

theorem finrank_span_clique :
    Module.finrank (ZMod 2)
      (Submodule.span (ZMod 2) (Set.range fun c : Fin 22 => toVecD 78 (labelCoord c))) = 11 := by
  rw [span_clique_eq]
  exact finrank_listSpan cliqueRank_check

theorem maskSum_vec :
    ([0, 2, 4, 6, 8, 10, 12].map fun p => toVecD 78 (labelCoord p)).sum = toVecD 78 949 := by
  rw [← maskSum_eq, maskSum]
  simp only [List.foldr_cons, List.foldr_nil, toVecD_xor, toVecD_zero, List.map_cons,
    List.map_nil, List.sum_cons, List.sum_nil]

theorem ne_labelCoord
    (y : Y) : toVecD 78
    (labelCoord (ι y)) ≠ toVecD
    78 949 := fun h => by
  obtain ⟨hne, hlt⟩ := labelCoord_ne (ι y).2
  exact hne (toVecD_injective hlt (by norm_num) h)

theorem fischer_clique_fixed_certificate :
    (∀ k < 12, ∀ i : Fin 78, ∀ y : Y, (ι y : ℕ) = basisPt i →
      fMat k *ᵥ Pi.single i 1 = toVecD 78 (labelCoord (ι (jGen k y)))) ∧
    (∀ k < 12, fMat k *ᵥ toVecD 78 949 = toVecD 78 949) ∧
    (stackSubOne fun k : Fin 12 => fMat k).rank = 77 ∧
    (∀ v : Fin 78 → ZMod 2, (∀ k < 12, fMat k *ᵥ v = v) ↔ v = 0 ∨ v = toVecD 78 949) ∧
    toVecD 78 949 ≠ 0 ∧
    Module.finrank (ZMod 2)
      (Submodule.span (ZMod 2) (Set.range fun c : Fin 22 => toVecD 78 (labelCoord c))) = 11 ∧
    (List.range 22).filter (fun c => (5461 : ℕ).testBit c) = [0, 2, 4, 6, 8, 10, 12] ∧
    ([0, 2, 4, 6, 8, 10, 12].map fun p => toVecD 78 (labelCoord p)).sum = toVecD 78 949 ∧
    ∀ y : Y, toVecD 78 (labelCoord (ι y)) ≠ toVecD 78 949 :=
  ⟨fun _ hk i y hy => fMat_col_jGen hk i y hy, fun _ hk => fMat_fixed hk, fixed_rank, fixed_iff,
    fun h => by simpa using (toVecD_eq_zero_iff (d := 78) (x := 949) (by norm_num)).1 h,
    finrank_span_clique, mask_bits, maskSum_vec, ne_labelCoord⟩

end CFSG.Monster.B.TwoA.Fischer.Cert
