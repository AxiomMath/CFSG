
module

public import CFSG.Sporadic.Schreier.PairJ2CertBase

public import CFSG.Certificates.NativeSchreierArrays
public import CFSG.Certificates.SchreierChainOrderGenerators
public import CFSG.Sporadic.J1.VecSpec
public import CFSG.Sporadic.Schreier.Enumeration
public import CFSG.Sporadic.Schreier.PairText
public import Certificates.Data.CFSGNative.PairSchreier.J2Data
public meta import CFSG.Sporadic.Schreier.PairText
public meta import Certificates.Data.CFSGNative.PairSchreier.J2Data
public meta import Certificates.Data.CFSGNative.J1.Vec
public meta import Certificates.Data.CFSGNative.Schreier.Check
public import CFSG.Sporadic.Schreier.PairJ2CertInputs
public import Certificates.Certificate2233
public import Certificates.Certificate2233Base

public noncomputable section

namespace CFSG.Sporadic.Schreier

open CFSG.Certificates CFSG.Certificates.Native CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native
  CFSG.Sporadic.Schreier.PairNative CFSG.Sporadic.Schreier.PairText

theorem j2CertOK_eq : j2CertOK = true :=
  Certificates.certificate2233

theorem j2CertOK_parts :
    j2Vectors.size = 315 ∧ (∀ i < 315, CFSG.Sporadic.J1.Native.wfV 5 14 j2Vectors[i]! = true) ∧
    (∀ j < 7, j2PermOK j2StrongArrs[j]! = true) ∧
    (∀ j < 7, isInvA 315 j2StrongArrs[j]! (rawInvs 315 j2StrongArrs)[j]! = true) ∧
    (j2Sylows.toList.map fun e => e.prime) = [2, 3, 5, 7] ∧
    (j2Sylows.toList.map fun e => e.gens.size) = [7, 3, 2, 1] ∧
    (j2Sylows.toList.map fun e => e.records.size) = [35, 13, 6, 1] ∧
    ∀ e < j2Sylows.size, (j2Sylows[e]!.gens.all j2PermOK && j2Sylows[e]!.records.all j2RecordOK)
      = true := by
  have h := j2CertOK_eq
  simp only [j2CertOK, Bool.and_eq_true, beq_iff_eq] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨h1, h2⟩, -⟩, h3⟩, h4⟩, -⟩, h5⟩, h6⟩, h7⟩, h8⟩ := h
  refine ⟨h1, fun i hi => allLt_spec h2 hi, fun j hj => allLt_spec h3 hj,
    fun j hj => allLt_spec h4 hj, h5, h6, h7, fun e he => ?_⟩
  rw [Array.all_eq_true] at h8
  rw [getElem!_pos j2Sylows e he]
  exact h8 e he

theorem j2Sylows_size : j2Sylows.size = 4 := by
  have h := congrArg List.length j2CertOK_parts.2.2.2.2.1
  simpa using h

theorem rep_j2StrongPerm {j : ℕ} (hj : j < 7) : Rep 315 j2StrongArrs[j]! (j2StrongPerm j) :=
  rep_of_j2PermOK (j2CertOK_parts.2.2.1 j hj)

theorem j2Sylow_parts {e : ℕ} (he : e < 4) :
    j2Sylows[e]!.gens.all j2PermOK = true ∧ j2Sylows[e]!.records.all j2RecordOK = true := by
  have h := j2CertOK_parts.2.2.2.2.2.2.2 e (by rw [j2Sylows_size]; exact he)
  simpa only [Bool.and_eq_true] using h

theorem j2Record_ok {e r : ℕ} (he : e < 4) (hr : r < j2Sylows[e]!.records.size) :
    j2RecordOK j2Sylows[e]!.records[r]! = true := by
  have h := (j2Sylow_parts he).2
  rw [Array.all_eq_true] at h
  rw [getElem!_pos _ r hr]
  exact h r hr

theorem j2NGBase_nodup {e r : ℕ} (he : e < 4) (hr : r < j2Sylows[e]!.records.size) :
    (j2NGBase e r).Nodup ∧ (j2NGBase e r).map Fin.val = j2Sylows[e]!.records[r]!.chain.base := by
  have h := j2Record_ok he hr
  simp only [j2RecordOK, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨-, -⟩, -⟩, hlt⟩, hnd⟩, -⟩, -⟩, -⟩ := h
  have hval : (j2NGBase e r).map Fin.val = j2Sylows[e]!.records[r]!.chain.base := by
    rw [j2NGBase, List.map_map]
    conv_rhs => rw [← List.map_id j2Sylows[e]!.records[r]!.chain.base]
    refine List.map_congr_left fun b hb => ?_
    have := hlt b hb
    simp only [Function.comp_apply, Fin.val_ofNat, id_eq]
    exact Nat.mod_eq_of_lt (by simpa using this)
  refine ⟨?_, hval⟩
  rw [← hval] at hnd
  exact List.Nodup.of_map _ hnd

theorem j2NGChain_eq {e r : ℕ} (he : e < 4) (hr : r < j2Sylows[e]!.records.size) :
    ∃ h : j2Sylows[e]!.records[r]!.chain.gens.size ≤ j2Sylows[e]!.records[r]!.chain.strong.size,
      j2NGChain e r = RawSchreierDatum.ofArrays 315 (by decide)
        j2Sylows[e]!.records[r]!.chain.strong j2Sylows[e]!.records[r]!.chain.gens.size h
        (j2NGBase e r) (j2NGBase_nodup he hr).1
        (Array.replicate j2Sylows[e]!.records[r]!.chain.gens.size [] ++
          j2Sylows[e]!.records[r]!.chain.words) := by
  have h := j2Record_ok he hr
  simp only [j2RecordOK, Bool.and_eq_true, decide_eq_true_eq] at h
  have hle := h.1.1.1.1.1.2
  exact ⟨hle, dite_eq_left ⟨hle, (j2NGBase_nodup he hr).1⟩⟩

theorem CERT_J2_matrix_action_data :
    j2SchemaVersion = 1 ∧ j2GroupName = "J2" ∧ j2Prime = 5 ∧ j2Dimension = 14 ∧
    j2Vectors.size = 315 ∧
    (∀ i < 315, j2Vectors[i]!.length = 14 ∧ ∀ x ∈ j2Vectors[i]!, x < 5) ∧
    j2BasisIdx = [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 15] ∧
    j2Chain.originalCount = 2 ∧ j2Chain.strongCount = 7 ∧
    j2Chain.base.toList.map Fin.val = [1, 0, 2] ∧
    (∀ j < 7, Rep 315 j2StrongArrs[j]! (j2StrongPerm j)) ∧
    (∀ j : Fin j2Chain.strongCount, j2Chain.strong.get j = j2StrongPerm j) ∧
    (∀ k : Fin j2Chain.originalCount, j2Chain.original.get k = j2Gen k) ∧
    j2P = j2Chain.originalSubgroup ∧
    j2Sylows.size = 4 ∧
    (j2Sylows.toList.map fun e => e.prime) = [2, 3, 5, 7] ∧
    (j2Sylows.toList.map fun e => e.gens.size) = [7, 3, 2, 1] ∧
    (j2Sylows.toList.map fun e => e.records.size) = [35, 13, 6, 1] ∧
    (∀ e < 4, ∀ k < j2Sylows[e]!.gens.size, Rep 315 j2Sylows[e]!.gens[k]! (j2SylowGen e k)) ∧
    (∀ e < 4, ∀ r < j2Sylows[e]!.records.size,
      Rep 315 j2Sylows[e]!.records[r]!.rep (j2NGRep e r) ∧
      (∀ j < j2Sylows[e]!.records[r]!.conj.size, ∀ l ∈ j2Sylows[e]!.records[r]!.conj[j]!,
        l = 1 ∨ l = -1 ∨ l = 2 ∨ l = -2) ∧
      (j2NGChain e r).originalCount = j2Sylows[e]!.records[r]!.chain.gens.size ∧
      (j2NGChain e r).strongCount = j2Sylows[e]!.records[r]!.chain.strong.size ∧
      (j2NGChain e r).base.toList.map Fin.val = j2Sylows[e]!.records[r]!.chain.base ∧
      (∀ j : Fin (j2NGChain e r).strongCount,
        Rep 315 j2Sylows[e]!.records[r]!.chain.strong[(j : ℕ)]! ((j2NGChain e r).strong.get j)) ∧
      ∀ k < j2Sylows[e]!.records[r]!.chain.gens.size,
        j2Sylows[e]!.records[r]!.chain.gens[k]! = j2Sylows[e]!.records[r]!.chain.strong[k]!) := by
  obtain ⟨h1, h2, -, -, h5, h6, h7, -⟩ := j2CertOK_parts
  refine ⟨rfl, rfl, rfl, rfl, h1, fun i hi => ?_, rfl, rfl, by simp [j2Chain, j2StrongArrs,
    RawSchreierDatum.ofArrays], j2Chain_base, fun j hj => rep_j2StrongPerm hj, j2Chain_strong_get,
    j2Chain_original_get, j2P_eq_original, j2Sylows_size, h5, h6, h7, fun e he k hk => ?_,
    fun e he r hr => ?_⟩
  · have := CFSG.Sporadic.J1.wfV_iff.1 (h2 i hi)
    exact this
  · have h := (j2Sylow_parts he).1
    rw [Array.all_eq_true] at h
    have := h k hk
    rw [← getElem!_pos j2Sylows[e]!.gens k hk] at this
    exact rep_of_j2PermOK this
  · have h := j2Record_ok he hr
    simp only [j2RecordOK, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq, Array.all_eq_true,
      List.all_eq_true] at h
    obtain ⟨⟨⟨⟨⟨⟨⟨hrep, hconj⟩, -⟩, -⟩, -⟩, hstrong⟩, hgens⟩, -⟩ := h
    obtain ⟨hle, hc⟩ := j2NGChain_eq he hr
    refine ⟨rep_of_j2PermOK hrep, fun j hj l hl => ?_, by rw [hc]; rfl, by rw [hc]; rfl, ?_,
      fun j => ?_, fun k hk => ?_⟩
    · have := hconj j hj l (by rw [← getElem!_pos _ j hj]; exact hl)
      simp only [Bool.or_eq_true, beq_iff_eq] at this
      omega
    · rw [hc, RawSchreierDatum.ofArrays_base_toList]
      exact (j2NGBase_nodup he hr).2
    · have hsc : (j2NGChain e r).strongCount = j2Sylows[e]!.records[r]!.chain.strong.size := by
        rw [hc]
        rfl
      have hj : (j : ℕ) < j2Sylows[e]!.records[r]!.chain.strong.size := lt_of_lt_of_eq j.2 hsc
      rw [show (j2NGChain e r).strong.get j = permOfArr 315
        j2Sylows[e]!.records[r]!.chain.strong[(j : ℕ)]! by
          revert j
          rw [hc]
          intro j _
          exact RawSchreierDatum.ofArrays_strong_get j]
      have := hstrong (j : ℕ) hj
      rw [← getElem!_pos j2Sylows[e]!.records[r]!.chain.strong (j : ℕ) hj] at this
      exact rep_of_j2PermOK this
    · have := hgens k (List.mem_range.2 hk)
      exact this

end CFSG.Sporadic.Schreier
