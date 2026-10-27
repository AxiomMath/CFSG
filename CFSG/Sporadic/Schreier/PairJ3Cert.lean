
module

public import CFSG.Sporadic.Schreier.PairJ3CertBase

public import CFSG.Certificates.NativeSchreierArrays
public import CFSG.Certificates.SchreierChainOrderGenerators
public import CFSG.Sporadic.Schreier.PairF2Quad
public import CFSG.Sporadic.Schreier.PairText
public import CFSG.Sporadic.Schreier.PairClasses
public import Certificates.Data.CFSGNative.MonsterB.Co2Data
public import Certificates.Data.CFSGNative.PairSchreier.Core
public meta import Certificates.Data.CFSGNative.PairSchreier.Core
public meta import CFSG.Sporadic.Schreier.PairF2Quad
public meta import CFSG.Sporadic.Schreier.PairText
public meta import Certificates.Data.CFSGNative.MonsterB.Co2Data
public meta import Certificates.Data.CFSGNative.Schreier.Check
public import CFSG.Sporadic.Schreier.PairJ3CertInputs
public import Certificates.Certificate2236

public noncomputable section

namespace CFSG.Sporadic.Schreier

open CFSG.Certificates CFSG.Certificates.Native CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native
  CFSG.Sporadic.Schreier.PairText CFSG.Sporadic.Schreier.PairF2

theorem j3CertOK_eq : j3CertOK = true :=
  Certificates.certificate2236

theorem j3CertOK_parts :
    j3Monomials.length = 3240 ∧
    (∀ i < 80, ∀ j < 80, i ≤ j → j3Monomials[pairIdx 80 i j]? = some (i, j)) ∧
    (∀ r < 6156, j3FormWord r < 2 ^ 3240) ∧ j3InvWord < 2 ^ 3240 ∧
    (∀ j < 5, j3StrongArrs[j]!.size = 6156 ∧
      isInvA 6156 j3StrongArrs[j]! (rawInvs 6156 j3StrongArrs)[j]! = true) ∧
    j3StabOrbits.length = 8 ∧
    (∀ o ∈ j3StabOrbits, PairNative.strictInc o = true ∧ ∀ x ∈ o, x < 6156) ∧
    j3StabOrbits.map List.length = [1, 1360, 2040, 1360, 510, 680, 120, 85] ∧
    j3Merges.map Prod.fst = [1, 4, 7, 8, 26, 47, 205] ∧
    j3Merges.map (fun m => m.2.length) = [6154, 6154, 6154, 6154, 6154, 6154, 6154] ∧
    ∀ m ∈ j3Merges, ∀ t ∈ m.2, t.1 < 2 ∧ t.2.1 < 6156 ∧ t.2.2 < 6156 := by
  have h := j3CertOK_eq
  simp only [j3CertOK, j3CertOKWith, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq,
    List.all_eq_true, List.mem_range, Bool.or_eq_true, Bool.not_eq_true'] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, -⟩, h5⟩, h6⟩, h7⟩, h8⟩, h9⟩, h10⟩, h11⟩ := h
  refine ⟨h1, fun i hi j hj hij => ?_, fun r hr => of_decide_eq_true (allLt_spec h3 hr), h4,
    fun j hj => ?_, h6, fun o ho => ⟨(h7 o ho).1, fun x hx => (h7 o ho).2 x hx⟩, h8, h9, h10,
    fun m hm t ht => (h11 m hm t ht).1.elim fun a b => ⟨a, b, (h11 m hm t ht).2⟩⟩
  · rcases h2 i hi j hj with h | h
    · exact absurd hij (by simpa using h)
    · exact h
  · have := allLt_spec h5 hj
    simp only [Bool.and_eq_true, beq_iff_eq] at this
    exact this

theorem rep_j3StrongPerm {j : ℕ} (hj : j < 5) : Rep 6156 j3StrongArrs[j]! (j3StrongPerm j) :=
  (rep_permOfArr (j3CertOK_parts.2.2.2.2.1 j hj).2).1

theorem CERT_J3_matrix_action_data :
    j3SchemaVersion = 1 ∧ j3GroupName = "J3" ∧ j3Prime = 2 ∧ j3Dimension = 80 ∧
    j3Monomials.length = 3240 ∧
    (∀ i < 80, ∀ j < 80, i ≤ j → j3Monomials[pairIdx 80 i j]? = some (i, j)) ∧
    (∀ z (v : J3V), j3Quad z v = ∑ i : Fin 80, ∑ j : Fin 80,
      if i ≤ j then (if z.testBit (pairIdx 80 i j) then 1 else 0) * v i * v j else 0) ∧
    (∀ r < 6156, j3FormWord r < 2 ^ 3240) ∧ j3InvWord < 2 ^ 3240 ∧
    j3B = polarMatrix j3InvForm ∧
    j3CentralizerIdx = [0, 1, 2, 3] ∧ j3CentralizerRank = 6399 ∧
    j3Chain.originalCount = 2 ∧ j3Chain.strongCount = 5 ∧
    j3Chain.base.toList.map Fin.val = [0, 1, 3, 2] ∧
    (∀ j < 5, Rep 6156 j3StrongArrs[j]! (j3StrongPerm j)) ∧
    (∀ j : Fin j3Chain.strongCount, j3Chain.strong.get j = j3StrongPerm j) ∧
    (∀ k : Fin j3Chain.originalCount, j3Chain.original.get k = j3Gen k) ∧
    j3P = j3Chain.originalSubgroup ∧
    j3Point = 0 ∧ j3StabIdx = [0, 2, 3, 4] ∧
    j3StabOrbits.length = 8 ∧
    (∀ o ∈ j3StabOrbits, o.Pairwise (· < ·) ∧ ∀ x ∈ o, x < 6156) ∧
    j3StabOrbits.map List.length = [1, 1360, 2040, 1360, 510, 680, 120, 85] ∧
    j3Merges.map Prod.fst = [1, 4, 7, 8, 26, 47, 205] ∧
    j3Merges.map (fun m => m.2.length) = [6154, 6154, 6154, 6154, 6154, 6154, 6154] ∧
    ∀ m ∈ j3Merges, ∀ t ∈ m.2, t.1 < 2 ∧ t.2.1 < 6156 ∧ t.2.2 < 6156 := by
  obtain ⟨h1, h2, h3, h4, -, h6, h7, h8, h9, h10, h11⟩ := j3CertOK_parts
  refine ⟨rfl, rfl, rfl, rfl, h1, h2, fun z v => rfl, h3, h4, rfl, rfl, rfl, rfl,
    by simp [j3Chain, j3StrongArrs, RawSchreierDatum.ofArrays], j3Chain_base,
    fun j hj => rep_j3StrongPerm hj, j3Chain_strong_get, j3Chain_original_get, j3P_eq_original,
    rfl, rfl, h6, fun o ho => ⟨pairwise_of_strictInc (h7 o ho).1, (h7 o ho).2⟩,
    h8, h9, h10, h11⟩

end CFSG.Sporadic.Schreier
