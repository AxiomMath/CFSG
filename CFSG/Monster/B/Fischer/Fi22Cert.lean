
module

public import CFSG.Monster.B.Fischer.Fi22CertBase

public import CFSG.Monster.B.Fischer.PinnedChain
public import CFSG.Monster.B.Fischer.Fi22CertData
public import CFSG.Monster.B.Fischer.Fi22FormsData
public import CFSG.Monster.B.Fischer.Fi22Monomials
public import Mathlib.Data.Matrix.Mul
public import Mathlib.Data.ZMod.Basic
public meta import CFSG.Monster.B.Fischer.PinnedChain
public meta import CFSG.Monster.B.Fischer.Fi22CertData
public meta import CFSG.Monster.B.Fischer.Fi22FormsData
public meta import Certificates.Data.CFSGNative.Fi22Pinned.Forms
public import CFSG.Monster.B.Fischer.Fi22CertInputs
public import Certificates.Certificate3149
public import CFSG.Monster.B.Fischer.PinnedChainInputs
public import Certificates.Certificate3149Base

public section

namespace CFSG.Monster.B.Fischer

open CFSG.Monster.B.Fischer.Native CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native

theorem fi22Cert_parse :
    linesOK fi22FormsBytes 3510 = true ∧ linesOK fi22InvFormBytes 1 = true ∧
    fi22StabOrbitsBytes.size = 3 * 3510 ∧ fi22MergeBytes.size = 7 * 2 * fi22MergeLength ∧
    (∀ t < 3, ∀ x ∈ fi22StabOrbit t, x < 3510) ∧
    (∀ t < 3, (fi22StabOrbit t).Pairwise (· < ·)) ∧
    ((List.range 3).map fun t => (fi22StabOrbit t).length) = [1, 2816, 693] ∧
    (fi22Merges.map fun m => (m.1 : Nat)) = [1, 11] ∧
    (fi22Merges.map fun m => m.2.length) = [3508, 3508] ∧
    (∀ m < 2, ∀ k < fi22MergeLength, (fi22MergeRaw m k).1 < 2 ∧ (fi22MergeRaw m k).2.1 < 3510 ∧
      (fi22MergeRaw m k).2.2 < 3510) :=
  Certificates.certificate3149

theorem CERT_Fi22_matrix_action_data :
    fi22SchemaVersion = 1 ∧ fi22GroupName = "Fi22" ∧ fi22Prime = 3 ∧ fi22Dimension = 77 ∧
    fi22Monomials.length = 3003 ∧
    (∀ i < 77, ∀ j < 77, i ≤ j → fi22Monomials[pairIdx i j]? = some (i, j)) ∧
    linesOK fi22FormsBytes 3510 = true ∧ linesOK fi22InvFormBytes 1 = true ∧
    (∀ r k, fi22FormCoeff r k < 3) ∧ (∀ k, fi22InvCoeff k < 3) ∧
    fi22CentralizerIdx = [0, 1, 2, 3, 4, 10] ∧ fi22CentralizerRank = 5928 ∧
    fi22Chain.originalCount = 2 ∧ fi22Chain.strongCount = 19 ∧
    fi22Chain.base.toList.map Fin.val = [0, 1, 2, 3, 6, 4] ∧
    (∀ k < 2, Rep 3510 (fi22ChainGen k) (fi22GenPerm k)) ∧
    (∀ j < 19, Rep 3510 (fi22ChainStrong j) (fi22StrongPerm j)) ∧
    fi22C0 = fi22GenPerm 0 ∧ fi22C1 = fi22GenPerm 0 * fi22GenPerm 1 ∧ fi22Point = 0 ∧
    fi22StabIdx = [0, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18] ∧
    (∀ t < 3, ∀ x ∈ fi22StabOrbit t, x < 3510) ∧
    (∀ t < 3, (fi22StabOrbit t).Pairwise (· < ·)) ∧
    ((List.range 3).map fun t => (fi22StabOrbit t).length) = [1, 2816, 693] ∧
    (fi22Merges.map fun m => (m.1 : Nat)) = [1, 11] ∧
    (fi22Merges.map fun m => m.2.length) = [3508, 3508] ∧
    (∀ m < 2, ∀ k < fi22MergeLength, (fi22MergeRaw m k).1 < 2 ∧ (fi22MergeRaw m k).2.1 < 3510 ∧
      (fi22MergeRaw m k).2.2 < 3510) := by
  obtain ⟨hl, hi, -, -, hlt, hinc, hlen, hrep, hmlen, hm⟩ := fi22Cert_parse
  refine ⟨rfl, rfl, rfl, rfl, fi22Monomials_pairIdx.1, fi22Monomials_pairIdx.2, hl, hi,
    fun _ _ => Nat.mod_lt _ (by decide), fun _ => Nat.mod_lt _ (by decide), rfl, rfl, rfl, rfl,
    fi22Chain_base, fun k hk => rep_fi22Gen hk, fun j hj => ?_, rfl, rfl, rfl, rfl, hlt, hinc,
    hlen, hrep, hmlen, hm⟩
  have h := rep_fi22Strong hj
  rw [fi22StrongArrs_get hj] at h
  exact h

end CFSG.Monster.B.Fischer
