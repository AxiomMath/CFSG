module

public import Certificates.Certificate1954

public section

namespace CFSG.Monster.B.Classical.E6Adjoint

theorem invRows_0 : invRows 0 13 = true :=
  Certificates.certificate1954.1

theorem invRows_13 : invRows 13 13 = true :=
  Certificates.certificate1954.2.1

theorem invRows_26 : invRows 26 13 = true :=
  Certificates.certificate1954.2.2.1

theorem invRows_39 : invRows 39 13 = true :=
  Certificates.certificate1954.2.2.2.1

theorem invRows_52 : invRows 52 13 = true :=
  Certificates.certificate1954.2.2.2.2.1

theorem invRows_65 : invRows 65 13 = true :=
  Certificates.certificate1954.2.2.2.2.2.1

theorem invOK_of_rows {lo n : ℕ} (h : invRows lo n = true) {a b c : ℕ} (ha : lo ≤ a)
    (ha' : a < lo + n) (hb : b < 78) (hc : c < 78) : invOK a b c = true := by
  simp only [invRows, List.all_eq_true, List.mem_range] at h
  have := h (a - lo) (by omega) b hb c hc
  rwa [Nat.add_sub_cancel' ha] at this

theorem invOK_all (a b c : Fin 78) : invOK a b c = true := by
  have ha := a.2
  have hb := b.2
  have hc := c.2
  by_cases h1 : (a : ℕ) < 13
  · exact invOK_of_rows invRows_0 (by omega) (by omega) hb hc
  by_cases h2 : (a : ℕ) < 26
  · exact invOK_of_rows invRows_13 (by omega) (by omega) hb hc
  by_cases h3 : (a : ℕ) < 39
  · exact invOK_of_rows invRows_26 (by omega) (by omega) hb hc
  by_cases h4 : (a : ℕ) < 52
  · exact invOK_of_rows invRows_39 (by omega) (by omega) hb hc
  by_cases h5 : (a : ℕ) < 65
  · exact invOK_of_rows invRows_52 (by omega) (by omega) hb hc
  · exact invOK_of_rows invRows_65 (by omega) (by omega) hb hc

theorem genRows_6 : genRows 6 = true :=
  Certificates.certificate1954.2.2.2.2.2.2.1

theorem genRows_7 : genRows 7 = true :=
  Certificates.certificate1954.2.2.2.2.2.2.2.1

theorem genRows_8 : genRows 8 = true :=
  Certificates.certificate1954.2.2.2.2.2.2.2.2.1

theorem genRows_9 : genRows 9 = true :=
  Certificates.certificate1954.2.2.2.2.2.2.2.2.2.1

theorem genRows_10 : genRows 10 = true :=
  Certificates.certificate1954.2.2.2.2.2.2.2.2.2.2.1

theorem genRows_11 : genRows 11 = true :=
  Certificates.certificate1954.2.2.2.2.2.2.2.2.2.2.2.1

theorem genRows_12 : genRows 12 = true :=
  Certificates.certificate1954.2.2.2.2.2.2.2.2.2.2.2.2.1

theorem genRows_14 : genRows 14 = true :=
  Certificates.certificate1954.2.2.2.2.2.2.2.2.2.2.2.2.2.1

theorem genRows_16 : genRows 16 = true :=
  Certificates.certificate1954.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

theorem genRows_18 : genRows 18 = true :=
  Certificates.certificate1954.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

theorem genRows_20 : genRows 20 = true :=
  Certificates.certificate1954.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

theorem genRows_22 : genRows 22 = true :=
  Certificates.certificate1954.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2

theorem genRows_all : ∀ A ∈ simpleIdx, genRows A = true := by
  simp only [simpleIdx, List.mem_cons, List.not_mem_nil, or_false]
  rintro A (rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl)
  exacts [genRows_6, genRows_7, genRows_8, genRows_9, genRows_10, genRows_11, genRows_12,
    genRows_14, genRows_16, genRows_18, genRows_20, genRows_22]

theorem adSqOK_all {A : ℕ} (hA : A ∈ simpleIdx) (x : Fin 78) : adSqOK A x = true := by
  have h := genRows_all A hA
  simp only [genRows, List.all_eq_true, List.mem_range, Bool.and_eq_true] at h
  exact (h x x.2).1

theorem genOK_all {A : ℕ} (hA : A ∈ simpleIdx) (x y : Fin 78) : genOK A x y = true := by
  have h := genRows_all A hA
  simp only [genRows, List.all_eq_true, List.mem_range, Bool.and_eq_true] at h
  exact (h x x.2).2 y y.2

end CFSG.Monster.B.Classical.E6Adjoint
