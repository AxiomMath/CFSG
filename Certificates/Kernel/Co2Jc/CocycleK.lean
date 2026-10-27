module

public import CFSG.Sporadic.Co2Jc.Native.Cocycle
public import Certificates.Kernel.Co2Jc.Gen

public section

namespace CertificateChecks.KernelCo2Jc

open CFSG.Sporadic.Co2Jc.Native CFSG.Sporadic.Co2Jc.Data

@[expose] noncomputable def wordActK (w : List Nat) (m : Nat) : Nat := w.foldr (fun k acc => njK k acc) m

@[expose] noncomputable def rowOfK : List Nat → Nat → Nat
  | [], _ => 0
  | k :: w, m => rowOfK w m ^^^ (wordActK w m <<< (10 * k))

@[expose] noncomputable def rowStepK (k : Nat) (first tail : List Nat) : List Nat :=
  ten.map fun rho =>
    first[rho]! ^^^
      ten.foldr
        (fun rhop acc => if (njK k (2 ^ rhop)).testBit rho then tail[rhop]! ^^^ acc else acc) 0

@[expose] noncomputable def rowAllK : List Nat → Nat → List Nat
  | [], _ => List.replicate 10 0
  | k :: w, j => rowStepK k (preMaskVec k (wordActK w (2 ^ j))) (rowAllK w j)

@[expose] noncomputable def dualRowsK : List Nat :=
  rels.flatMap fun r => (List.range 10).map fun j => rowOfK r (2 ^ j)

@[expose] noncomputable def splitRowsK : List Nat :=
  rels.flatMap fun r => (List.range 10).flatMap fun j => rowAllK r j

theorem gl_eq (k x : Nat) : gl k x = njK k x := glNJT_eq_njK k x

theorem wordActK_eq (w : List Nat) (m : Nat) : CFSG.Sporadic.Co2Jc.wordAct w m = wordActK w m :=
  wordAct_eq w m

theorem rowOf_eq (w : List Nat) (m : Nat) : rowOf w m = rowOfK w m := by
  induction w with
  | nil => rfl
  | cons k w ih => rw [rowOf, rowOfK, ih, wordActK_eq]

theorem rowStep_eq (k : Nat) (first tail : List Nat) :
    rowStep k first tail = rowStepK k first tail := by
  simp only [rowStep, rowStepK, gl_eq]

theorem rowAll_eq (w : List Nat) (j : Nat) : rowAll w j = rowAllK w j := by
  induction w with
  | nil => rfl
  | cons k w ih => rw [rowAll, rowAllK, ih, wordActK_eq, rowStep_eq]

theorem dualRows_eq : dualRows = dualRowsK := by
  simp only [dualRows, dualRowsK, rowOf_eq]

theorem splitRows_eq : splitRows = splitRowsK := by
  simp only [splitRows, splitRowsK, rowAll_eq]

end CertificateChecks.KernelCo2Jc
