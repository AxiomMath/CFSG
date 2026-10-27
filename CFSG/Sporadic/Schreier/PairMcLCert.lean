
module

public import CFSG.Sporadic.Schreier.PairMcLCertBase

public import CFSG.Certificates.NativeSchreierArrays
public import CFSG.Certificates.SchreierChainOrderGenerators
public import CFSG.Sporadic.J1.VecSpec
public import CFSG.Sporadic.Schreier.PairText
public import CFSG.Sporadic.Schreier.PairClasses
public import Certificates.Data.CFSGNative.MonsterB.Co2Data
public import Certificates.Data.CFSGNative.PairSchreier.Core
public meta import CFSG.Sporadic.Schreier.PairText
public meta import Certificates.Data.CFSGNative.MonsterB.Co2Data
public meta import Certificates.Data.CFSGNative.PairSchreier.Core
public meta import Certificates.Data.CFSGNative.Schreier.Check
public meta import Certificates.Data.CFSGNative.J1.Vec
public import CFSG.Sporadic.Schreier.PairMcLCertInputs
public import Certificates.Certificate2240

public noncomputable section

namespace CFSG.Sporadic.Schreier

open CFSG.Certificates CFSG.Certificates.Native CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native
  CFSG.Sporadic.Schreier.PairText

theorem mclCertOK_eq : mclCertOK = true :=
  Certificates.certificate2240

theorem mclCertOK_parts :
    mclVectors.size = 275 ∧ (∀ i < 275, CFSG.Sporadic.J1.Native.wfV 3 21 mclVectors[i]! = true) ∧
    (∀ j < 13, mclStrongArrs[j]!.size = 275 ∧
      isInvA 275 mclStrongArrs[j]! (rawInvs 275 mclStrongArrs)[j]! = true) ∧
    mclStabOrbits.length = 3 ∧
    (∀ o ∈ mclStabOrbits, PairNative.strictInc o = true ∧ ∀ x ∈ o, x < 275) ∧
    mclStabOrbits.map List.length = [1, 112, 162] ∧
    mclMerges.map Prod.fst = [1, 3] ∧
    mclMerges.map (fun m => m.2.length) =
      [273, 273] ∧
    ∀ m ∈ mclMerges, ∀ t ∈ m.2, t.1 < 2 ∧ t.2.1 < 275 ∧ t.2.2 < 275 := by
  have h := mclCertOK_eq
  simp only [mclCertOK, mclCertOKWith, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq,
    List.all_eq_true] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨h1, h2⟩, -⟩, h3⟩, h4⟩, h5⟩, h6⟩, h7⟩, h8⟩, h9⟩ := h
  rw [mclStabOrbits_def, mclMerges_def]
  refine ⟨h1, fun i hi => allLt_spec h2 hi, fun j hj => ?_, h4,
    fun o ho => ⟨(h5 o ho).1, fun x hx => (h5 o ho).2 x hx⟩, h6, h7, h8,
    fun m hm t ht => (h9 m hm t ht).1.elim fun a b => ⟨a, b, (h9 m hm t ht).2⟩⟩
  have := allLt_spec h3 hj
  simp only [Bool.and_eq_true, beq_iff_eq] at this
  exact this

theorem rep_mclStrongPerm {j : ℕ} (hj : j < 13) : Rep 275 mclStrongArrs[j]! (mclStrongPerm j) :=
  (rep_permOfArr (mclCertOK_parts.2.2.1 j hj).2).1

theorem CERT_McL_matrix_action_data :
    mclSchemaVersion = 1 ∧ mclGroupName = "McL" ∧ mclPrime = 3 ∧ mclDimension = 21 ∧
    mclVectors.size = 275 ∧
    (∀ i < 275, mclVectors[i]!.length = 21 ∧ ∀ x ∈ mclVectors[i]!, x < 3) ∧
    mclBasisIdx = [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 19, 20, 21] ∧
    mclChain.originalCount = 2 ∧ mclChain.strongCount = 13 ∧
    mclChain.base.toList.map Fin.val = [0, 1, 2, 3, 4] ∧
    (∀ j < 13, Rep 275 mclStrongArrs[j]! (mclStrongPerm j)) ∧
    (∀ j : Fin mclChain.strongCount, mclChain.strong.get j = mclStrongPerm j) ∧
    (∀ k : Fin mclChain.originalCount, mclChain.original.get k = mclGen k) ∧
    mclP = mclChain.originalSubgroup ∧
    mclPoint = 0 ∧ mclStabIdx = [0, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12] ∧
    mclStabOrbits.length = 3 ∧
    (∀ o ∈ mclStabOrbits, o.Pairwise (· < ·) ∧ ∀ x ∈ o, x < 275) ∧
    mclStabOrbits.map List.length = [1, 112, 162] ∧
    mclMerges.map Prod.fst = [1, 3] ∧
    mclMerges.map (fun m => m.2.length) =
      [273, 273] ∧
    ∀ m ∈ mclMerges, ∀ t ∈ m.2, t.1 < 2 ∧ t.2.1 < 275 ∧ t.2.2 < 275 := by
  obtain ⟨h1, h2, -, h4, h5, h6, h7, h8, h9⟩ := mclCertOK_parts
  refine ⟨rfl, rfl, rfl, rfl, h1, fun i hi => CFSG.Sporadic.J1.wfV_iff.1 (h2 i hi), rfl, rfl,
    by simp [mclChain, mclStrongArrs, RawSchreierDatum.ofArrays], mclChain_base,
    fun j hj => rep_mclStrongPerm hj, mclChain_strong_get, mclChain_original_get,
    mclP_eq_original, rfl, rfl,
    h4, fun o ho => ⟨pairwise_of_strictInc (h5 o ho).1, (h5 o ho).2⟩, h6, h7, h8, h9⟩

end CFSG.Sporadic.Schreier
