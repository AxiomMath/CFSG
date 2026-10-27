module

public import Certificates.Kernel.Co1K105.Glob
public import Certificates.Kernel.Co1K105.R1a
public import Certificates.Kernel.Co1K105.F0
public import Certificates.Kernel.Co1K105.F1
public import Certificates.Kernel.Co1K105.R2a
public import Certificates.Kernel.Co1K105.RT

public section

namespace CFSG.KD.Co1K105

open CFSG.KC.SLD2

theorem of_shift {f g : Nat → Bool} {o c : Nat} (hf : ∀ i, f i = g (Nat.add o i))
    (h : ∀ i < c, f i = true) {i : Nat} (h1 : o ≤ i) (h2 : i < o + c) : g i = true := by
  have e : Nat.add o (i - o) = i := by simp only [Nat.add_eq]; omega
  have := h (i - o) (by omega)
  rw [hf, e] at this
  exact this

theorem len_eq : D.bo.length = 0 ∧ D.R1.length = 8 ∧ D.roots.length = 1 := by
  have h := lens
  simp only [Bool.and_eq_true] at h
  exact ⟨Nat.eq_of_beq_eq_true h.1.1, Nat.eq_of_beq_eq_true h.1.2, Nat.eq_of_beq_eq_true h.2⟩

theorem bo_all :
    (List.range D.bo.length).all (fun i => borbOK C D (D.bo.getD i default)) = true := by
  rw [len_eq.1]
  rfl

theorem r1_all :
    (List.range D.R1.length).all (fun c => rec1OK C D (D.R1.getD c default)) = true := by
  rw [len_eq.2.1, List.all_eq_true]
  intro i hi
  exact R1a.all i (List.mem_range.1 hi)

theorem fr_all : (List.range C.nf).all (fRowOK C D) = true := by
  rw [List.all_eq_true]
  intro i hi
  have hi' : i < 16 := List.mem_range.1 hi
  by_cases h : i < 8
  · exact of_shift (g := fRowOK C D) (o := 0) (fun _ => rfl) F0.all (by omega) (by omega)
  · exact of_shift (g := fRowOK C D) (o := 8) (fun _ => rfl) F1.all (by omega) (by omega)

theorem r2_all : (List.range D.R1.length).all (rec2OK C D) = true := by
  rw [len_eq.2.1, List.all_eq_true]
  intro i hi
  exact R2a.all i (List.mem_range.1 hi)

theorem rt_all : (List.range D.roots.length).all (rootsOK C D) = true := by
  rw [len_eq.2.2, List.all_eq_true]
  intro i hi
  exact RT.all i (List.mem_range.1 hi)

theorem dc2_ok : dc2Check C D = true := by
  unfold dc2Check
  rw [glob, bo_all, r1_all, frest, fr_all, r2_all, rt_all, ridx]
  rfl

end CFSG.KD.Co1K105

end
