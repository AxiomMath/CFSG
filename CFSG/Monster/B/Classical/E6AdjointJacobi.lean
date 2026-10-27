module

public import Certificates.Certificate1953

public section

namespace CFSG.Monster.B.Classical.E6Adjoint

theorem jacRows_0 : jacRows 0 13 = true :=
  Certificates.certificate1953.1

theorem jacRows_13 : jacRows 13 13 = true :=
  Certificates.certificate1953.2.1

theorem jacRows_26 : jacRows 26 13 = true :=
  Certificates.certificate1953.2.2.1

theorem jacRows_39 : jacRows 39 13 = true :=
  Certificates.certificate1953.2.2.2.1

theorem jacRows_52 : jacRows 52 13 = true :=
  Certificates.certificate1953.2.2.2.2.1

theorem jacRows_65 : jacRows 65 13 = true :=
  Certificates.certificate1953.2.2.2.2.2

theorem jacOK_of_rows {lo n : ℕ} (h : jacRows lo n = true) {a b c : ℕ} (ha : lo ≤ a)
    (ha' : a < lo + n) (hb : b < 78) (hc : c < 78) : jacOK a b c = true := by
  simp only [jacRows, List.all_eq_true, List.mem_range] at h
  have := h (a - lo) (by omega) b hb c hc
  rwa [Nat.add_sub_cancel' ha] at this

theorem jacOK_all (a b c : Fin 78) : jacOK a b c = true := by
  have ha := a.2
  have hb := b.2
  have hc := c.2
  by_cases h1 : (a : ℕ) < 13
  · exact jacOK_of_rows jacRows_0 (by omega) (by omega) hb hc
  by_cases h2 : (a : ℕ) < 26
  · exact jacOK_of_rows jacRows_13 (by omega) (by omega) hb hc
  by_cases h3 : (a : ℕ) < 39
  · exact jacOK_of_rows jacRows_26 (by omega) (by omega) hb hc
  by_cases h4 : (a : ℕ) < 52
  · exact jacOK_of_rows jacRows_39 (by omega) (by omega) hb hc
  by_cases h5 : (a : ℕ) < 65
  · exact jacOK_of_rows jacRows_52 (by omega) (by omega) hb hc
  · exact jacOK_of_rows jacRows_65 (by omega) (by omega) hb hc

end CFSG.Monster.B.Classical.E6Adjoint
