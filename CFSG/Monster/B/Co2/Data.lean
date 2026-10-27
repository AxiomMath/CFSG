module

public import CFSG.Monster.B.Co2.DataCert
public import CFSG.Monster.VisQuot.Monomial

public noncomputable section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.Monster.B.Co2

open CFSG.Monster CFSG.Monster.ScalarKernel CFSG.Monster.VisCert CFSG.Monster.VisQuot
  CFSG.Certificates

@[expose] def frameQ (j : ℕ) : OLq := if h : j < 15 then QuotientGroup.mk (frameGen ⟨j, h⟩) else 1

@[expose] def frameWordQ : List ℤ → OLq
  | [] => 1
  | l :: w => frameQ l.toNat * frameWordQ w

@[expose] def pairLetterQ (l : ℤ) : OLq := if 0 < l then frameQ l.natAbs else (frameQ l.natAbs)⁻¹

@[expose] def pairWordQ : List ℤ → OLq
  | [] => 1
  | l :: w => pairLetterQ l * pairWordQ w

@[expose] def genRecord (i : Fin 24) : Native.GenRecord := Native.genRecords[i.val]!

@[expose] def alpha (i : Fin 24) : OLq :=
  match (genRecord i).kind with
  | .pairStabilizer => pairWordQ (genRecord i).word
  | _ => frameWordQ (genRecord i).word

@[expose] def genMatrix (i : Fin 24) : Array ℕ := (genRecord i).matrix

@[expose] def genQuotMatrix (i : Fin 24) : Array ℕ := (genRecord i).quotientMatrix

@[expose] def quotBasis (t : Fin 22) : ℕ := Native.quotientBasis[t.val]!

abbrev Ω : Type := Fin 2300

@[expose] def shortVec (j : Ω) : ℕ := Native.vectors[j.val]!

@[expose] def pPerm (i : Fin 24) : Equiv.Perm Ω := permOfArr 2300 Native.permutations[i.val]!

@[expose] def alphaN (j : ℕ) : OLq := if h : j < 24 then alpha ⟨j, h⟩ else 1

@[expose] def alphaWord : List ℤ → OLq
  | [] => 1
  | l :: w => (if 0 < l then alphaN (l.natAbs - 1) else (alphaN (l.natAbs - 1))⁻¹) * alphaWord w

@[expose] def A0 : OLq := alphaWord Native.pairWords[0]!

@[expose] def A1 : OLq := alphaWord Native.pairWords[1]!

@[expose] def Agrp : Subgroup OLq := Subgroup.closure {A0, A1}

@[expose] def pa : Equiv.Perm Ω := permOfArr 2300 Native.pairPerms[0]!

@[expose] def pb : Equiv.Perm Ω := permOfArr 2300 Native.pairPerms[1]!

@[expose] def Pgrp : Subgroup (Equiv.Perm Ω) := Subgroup.closure {pa, pb}

@[expose] def strongPerm (j : ℕ) : Equiv.Perm Ω := permOfArr 2300 Native.chainStrong[j]!

@[expose] def chainQ : RawSchreierDatum 2300 where
  degree_pos := by norm_num
  originalCount := 2
  strongCount := 20
  baseCount := 10
  originalCount_le := by norm_num
  original := #v[pa, pb]
  strong := Vector.ofFn fun j : Fin 20 => strongPerm j
  base := #v[0, 1, 2, 4, 5, 3, 6, 7, 9, 8]
  base_distinct := by decide
  derivation := fun j _ => toLetters j.val Native.chainWords[j.val]!

@[expose] def stabIdx : List ℕ := Native.chainStabIdx.toList

@[expose] def stabOrbit (t : ℕ) : List ℕ := (Native.chainOrbits[t]!).toList

theorem permutations_size : Native.permutations.size = 24 := by simp [Native.permutations]

theorem vectors_size : Native.vectors.size = 2300 := by simp [Native.vectors, Native.hexTable]

theorem pairPerms_size : Native.pairPerms.size = 2 := by simp [Native.pairPerms]

theorem dataCheck_parts :
    Native.genRecords.size = 24 ∧ Native.quotientBasis.size = 22 ∧ Native.pairWords.size = 2 ∧
    (∀ i < 24, Native.genRecords[i]!.matrix.size = 24 ∧
      Native.genRecords[i]!.quotientMatrix.size = 22 ∧
      Native.recordWordOK Native.genRecords[i]! = true) ∧
    (∀ i < 24, Native.isInvA 2300 Native.permutations[i]!
      (Native.invCand 2300 Native.permutations[i]!) = true) ∧
    (∀ i < 2, Native.isInvA 2300 Native.pairPerms[i]!
      (Native.invCand 2300 Native.pairPerms[i]!) = true) ∧
    (∀ i < 2, ∀ l ∈ Native.pairWords[i]!, l ≠ 0 ∧ l.natAbs ≤ 24) := by
  have h := dataCheck_eq_true
  simp only [Native.dataCheck, Bool.and_eq_true, beq_iff_eq] at h
  obtain ⟨⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩, h7⟩ := h
  refine ⟨h1, h2, h3, fun i hi => ?_, fun i hi => allLt_spec h5 hi,
    fun i hi => allLt_spec h6 hi, fun i hi l hl => ?_⟩
  · have := allLt_spec h4 hi
    simpa only [Bool.and_eq_true, beq_iff_eq, and_assoc] using this
  · have := allLt_spec h7 hi
    rw [List.all_eq_true] at this
    simpa [bne_iff_ne] using this l hl

theorem rep_pa : Rep 2300 Native.pairPerms[0]! pa :=
  (rep_permOfArr (dataCheck_parts.2.2.2.2.2.1 0 (by norm_num))).1

theorem rep_pb : Rep 2300 Native.pairPerms[1]! pb :=
  (rep_permOfArr (dataCheck_parts.2.2.2.2.2.1 1 (by norm_num))).1

theorem rep_pPerm
    (i : Fin 24) : Rep 2300 Native.permutations[i.val]! (pPerm i) :=
  (rep_permOfArr (dataCheck_parts.2.2.2.2.1 i i.2)).1

end CFSG.Monster.B.Co2
