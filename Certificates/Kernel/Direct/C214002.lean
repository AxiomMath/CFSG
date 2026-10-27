module

public import Mathlib.GroupTheory.SpecificGroups.Alternating
public import CFSG.RankThree.PartTwo.Sec15.Item153Push2ProofPerm

public section

namespace CertificateChecks.KernelDirect.C214002

open Equiv
open CFSG.RankThree.PartTwo.Sec15.Push153B (pcode cmul csq pcode_mul pcode_one pcode_injective
  pcode_sq pcode_mem_permutations')

def pow8 (c : List ℕ) : Bool := csq (csq (csq c)) == List.range 6

def badCodes : List (List ℕ) := (List.range 6).permutations'.filter fun d => !pow8 d

def twoCodes : List (List ℕ) := [
    [0,1,3,2,5,4], [0,1,4,5,2,3], [0,1,5,4,3,2], [0,2,1,3,5,4], [0,2,1,4,3,5], [0,2,1,5,4,3], [0,3,2,1,5,4], [0,3,4,1,2,5],
    [0,3,5,1,4,2], [0,4,2,5,1,3], [0,4,3,2,1,5], [0,4,5,3,1,2], [0,5,2,4,3,1], [0,5,3,2,4,1], [0,5,4,3,2,1], [1,0,2,3,5,4],
    [1,0,2,4,3,5], [1,0,2,5,4,3], [1,0,3,2,4,5], [1,0,3,4,5,2], [1,0,3,5,2,4], [1,0,4,2,5,3], [1,0,4,3,2,5], [1,0,4,5,3,2],
    [1,0,5,2,3,4], [1,0,5,3,4,2], [1,0,5,4,2,3], [1,2,3,0,5,4], [1,2,4,5,0,3], [1,2,5,4,3,0], [1,3,0,2,5,4], [1,3,4,5,2,0],
    [1,3,5,4,0,2], [1,4,0,5,2,3], [1,4,3,2,5,0], [1,4,5,0,3,2], [1,5,0,4,3,2], [1,5,3,2,0,4], [1,5,4,0,2,3], [2,0,3,1,5,4],
    [2,0,4,5,1,3], [2,0,5,4,3,1], [2,1,0,3,5,4], [2,1,0,4,3,5], [2,1,0,5,4,3], [2,3,0,1,4,5], [2,3,0,4,5,1], [2,3,0,5,1,4],
    [2,3,1,0,5,4], [2,3,4,1,5,0], [2,3,5,1,0,4], [2,4,0,1,5,3], [2,4,0,3,1,5], [2,4,0,5,3,1], [2,4,1,5,0,3], [2,4,3,5,1,0],
    [2,4,5,0,1,3], [2,5,0,1,3,4], [2,5,0,3,4,1], [2,5,0,4,1,3], [2,5,1,4,3,0], [2,5,3,4,0,1], [2,5,4,0,3,1], [3,0,1,2,5,4],
    [3,0,4,5,2,1], [3,0,5,4,1,2], [3,1,2,0,5,4], [3,1,4,0,2,5], [3,1,5,0,4,2], [3,2,0,1,5,4], [3,2,1,0,4,5], [3,2,1,4,5,0],
    [3,2,1,5,0,4], [3,2,4,0,5,1], [3,2,5,0,1,4], [3,4,0,5,1,2], [3,4,1,0,5,2], [3,4,2,0,1,5], [3,4,5,0,2,1], [3,4,5,1,0,2],
    [3,4,5,2,1,0], [3,5,0,4,2,1], [3,5,1,0,2,4], [3,5,2,0,4,1], [3,5,4,0,1,2], [3,5,4,1,2,0], [3,5,4,2,0,1], [4,0,1,5,2,3],
    [4,0,3,2,5,1], [4,0,5,1,3,2], [4,1,2,5,0,3], [4,1,3,2,0,5], [4,1,5,3,0,2], [4,2,0,5,1,3], [4,2,1,0,5,3], [4,2,1,3,0,5],
    [4,2,1,5,3,0], [4,2,3,5,0,1], [4,2,5,1,0,3], [4,3,0,1,5,2], [4,3,1,5,0,2], [4,3,2,1,0,5], [4,3,5,0,1,2], [4,3,5,1,2,0],
    [4,3,5,2,0,1], [4,5,0,2,3,1], [4,5,1,2,0,3], [4,5,2,3,0,1], [4,5,3,0,2,1], [4,5,3,1,0,2], [4,5,3,2,1,0], [5,0,1,4,3,2],
    [5,0,3,2,1,4], [5,0,4,1,2,3], [5,1,2,4,3,0], [5,1,3,2,4,0], [5,1,4,3,2,0], [5,2,0,4,3,1], [5,2,1,0,3,4], [5,2,1,3,4,0],
    [5,2,1,4,0,3], [5,2,3,4,1,0], [5,2,4,1,3,0], [5,3,0,1,2,4], [5,3,1,4,2,0], [5,3,2,1,4,0], [5,3,4,0,2,1], [5,3,4,1,0,2],
    [5,3,4,2,1,0], [5,4,0,2,1,3], [5,4,1,2,3,0], [5,4,2,3,1,0], [5,4,3,0,1,2], [5,4,3,1,2,0], [5,4,3,2,0,1]]

set_option maxRecDepth 100000 in
theorem alt6_two_mem : ∀ s : Perm (Fin 6), s ≠ 1 → pow8 (pcode s) = true → Perm.sign s = 1 →
    pcode s ∈ twoCodes := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem alt6_bad_comm : (badCodes.all fun d => twoCodes.all fun c => !(cmul d c == cmul c d)) =
    true := by
  decide +kernel

theorem pow8_pcode (σ : Perm (Fin 6)) : pow8 (pcode σ) = true ↔ σ ^ 8 = 1 := by
  have h8 : pcode (σ ^ 8) = csq (csq (csq (pcode σ))) := by
    rw [← pcode_sq, ← pcode_sq, ← pcode_sq, ← pow_mul, ← pow_mul]
  rw [pow8, ← h8, ← pcode_one, beq_iff_eq]
  exact pcode_injective.eq_iff

theorem alt6_centralizer_pow_eight :
    ∀ s g : alternatingGroup (Fin 6), s ≠ 1 → s ^ 8 = 1 → g * s = s * g → g ^ 8 = 1 := by
  intro s g hs hs8 hgs
  have hsm := alt6_two_mem s.1 (fun e => hs (Subtype.ext e))
    ((pow8_pcode _).2 (by simpa using congrArg Subtype.val hs8)) s.2
  have hcomm : cmul (pcode g.1) (pcode s.1) = cmul (pcode s.1) (pcode g.1) := by
    rw [← pcode_mul, ← pcode_mul]
    exact congrArg (fun x => pcode (Subtype.val x)) hgs
  apply Subtype.ext
  by_contra hne
  have hg : pow8 (pcode g.1) = false := by
    rw [Bool.eq_false_iff, ne_eq, pow8_pcode]
    simpa using hne
  have hgm : pcode g.1 ∈ badCodes :=
    List.mem_filter.2 ⟨pcode_mem_permutations' g.1, by rw [hg]; rfl⟩
  have := List.all_eq_true.1 (List.all_eq_true.1 alt6_bad_comm _ hgm) _ hsm
  simp [hcomm] at this

end CertificateChecks.KernelDirect.C214002
