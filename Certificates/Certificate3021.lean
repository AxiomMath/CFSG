module

public import CFSG.Monster.B.TwoA.Census.LatticeInvInputs

public section

open CFSG.Monster.B.TwoA.Census Matrix

namespace CertificateChecks.Batch3021

open CFSG.Monster.B.TwoA.Census Matrix

@[expose] def sg (d : ℕ) (i : Fin 24) : ℚ := if d.testBit i then -1 else 1

@[expose] def sqCheck (d : ℕ) (a : Array ℕ) (neg : Bool) : Bool :=
  (List.range 24).all fun i =>
    decide (a[i]! < 24) && a[a[i]!]! == i && ((d.testBit i ^^ d.testBit a[i]!) == neg)

theorem entry (d : ℕ) (a : Array ℕ) (i j : Fin 24) :
    (dsgn d * pmatA a) i j = if a[(i : ℕ)]! = j then sg d i else 0 := by
  rw [dsgn, diagonal_mul, pmatA, of_apply, sg]
  split_ifs <;> simp

theorem sq_entry (d : ℕ) (a : Array ℕ) (i k : Fin 24) (ha : a[(i : ℕ)]! < 24) :
    ((dsgn d * pmatA a) * (dsgn d * pmatA a)) i k =
      sg d i * (if a[a[(i : ℕ)]!]! = k then sg d ⟨a[(i : ℕ)]!, ha⟩ else 0) := by
  rw [mul_apply, Fintype.sum_eq_single ⟨a[(i : ℕ)]!, ha⟩]
  · rw [entry, ite_eq_left rfl, entry]
  · intro j hj
    rw [entry, ite_eq_right (fun h => hj (Fin.ext h.symm)), zero_mul]

theorem sq_eq (d : ℕ) (a : Array ℕ) (neg : Bool) (h : sqCheck d a neg = true) :
    (dsgn d * pmatA a) * (dsgn d * pmatA a) = if neg then -1 else 1 := by
  ext i k
  have hi := List.all_eq_true.1 h i (List.mem_range.2 i.2)
  simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at hi
  obtain ⟨⟨ha, hinv⟩, hs⟩ := hi
  rw [sq_entry d a i k ha, hinv]
  by_cases hik : i = k
  · subst hik
    rw [ite_eq_left rfl, sg, sg]
    revert hs
    cases d.testBit i <;> cases d.testBit a[(i : ℕ)]! <;> cases neg <;> simp
  · rw [ite_eq_right (fun e => hik (Fin.ext e))]
    cases neg <;> simp [one_apply, hik]

theorem kSq : sqCheck 255 (seedA 0) false = true ∧ sqCheck 212822 (seedA 0) false = true ∧
    sqCheck 3346236 (seedA 2) true = true := by decide +kernel

theorem trace_eq (d : ℕ) (a : Array ℕ) :
    trace (dsgn d * pmatA a) = ∑ i : Fin 24, if a[(i : ℕ)]! = i then sg d i else 0 := by
  rw [trace]
  exact Finset.sum_congr rfl fun i _ => entry d a i i

theorem kTr : (∑ i : Fin 24, if (seedA 0)[(i : ℕ)]! = i then sg 255 i else 0) = 8 ∧
    (∑ i : Fin 24, if (seedA 0)[(i : ℕ)]! = i then sg 212822 i else 0) = 0 ∧
    (∑ i : Fin 24, if (seedA 2)[(i : ℕ)]! = i then sg 3346236 i else 0) = 0 := by decide +kernel

theorem chiF_values_0 :
    chiF (dsgn 255 * pmatA (seedA 0)) = 43 ∧
    chiF (dsgn 212822 * pmatA (seedA 0)) = 11 ∧ chiF (dsgn 3346236 * pmatA (seedA 2)) = -13 := by
  obtain ⟨h1, h2, h3⟩ := kSq
  obtain ⟨t1, t2, t3⟩ := kTr
  simp only [chiF, trace_eq, sq_eq _ _ _ h1, sq_eq _ _ _ h2, sq_eq _ _ _ h3, t1, t2, t3,
    Bool.false_eq_true, ite_false, ite_true, trace_one, trace_neg, Fintype.card_fin]
  norm_num

theorem monoA_sq_check_1 :
    (dsgn 255 * pmatA (seedA 0)) * (dsgn 255 * pmatA (seedA 0)) = 1 ∧
    (dsgn 212822 * pmatA (seedA 0)) * (dsgn 212822 * pmatA (seedA 0)) = 1 ∧
    (dsgn 3346236 * pmatA (seedA 2)) * (dsgn 3346236 * pmatA (seedA 2)) = -1 :=
  ⟨sq_eq _ _ _ kSq.1, sq_eq _ _ _ kSq.2.1, sq_eq _ _ _ kSq.2.2⟩

end CertificateChecks.Batch3021

namespace Certificates

open CertificateChecks

open CFSG.Monster.B.TwoA.Census in
theorem certificate3021 : (chiF (dsgn 255 * pmatA (seedA 0)) = 43 ∧
       chiF (dsgn 212822 * pmatA (seedA 0)) = 11 ∧ chiF (dsgn 3346236 * pmatA (seedA 2)) = -13)
    ∧ ((dsgn 255 * pmatA (seedA 0)) * (dsgn 255 * pmatA (seedA 0)) = 1 ∧
       (dsgn 212822 * pmatA (seedA 0)) * (dsgn 212822 * pmatA (seedA 0)) = 1 ∧
       (dsgn 3346236 * pmatA (seedA 2)) * (dsgn 3346236 * pmatA (seedA 2)) = -1) := by
  exact ⟨CertificateChecks.Batch3021.chiF_values_0, CertificateChecks.Batch3021.monoA_sq_check_1⟩

end Certificates
