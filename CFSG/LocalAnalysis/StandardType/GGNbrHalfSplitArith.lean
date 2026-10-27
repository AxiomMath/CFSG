module

public import CFSG.LocalAnalysis.StandardType.GGNbrTableForms

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly

private theorem gnhs_lab_eq {lab : LargeEvenLabel} {t : LargeEvenLieTag} {r n : ℕ}
    (ht : lab.tag = t) (hr : lab.rank = r) (hn : lab.n = n) : lab = ⟨t, r, n⟩ := by
  obtain ⟨t', r', n'⟩ := lab
  simp_all

private theorem gnhs_dvd_sq_sub_one_of_dvd_sub {p a : ℕ} (h : p ∣ a - 1) : p ∣ a ^ 2 - 1 := by
  have ha : a ^ 2 - 1 = (a + 1) * (a - 1) := by
    rw [pow_two, mul_self_tsub_one]
  rw [ha]
  exact h.mul_left (a + 1)

private theorem gnhs_dvd_sq_sub_one_of_dvd_add {p a : ℕ} (h : p ∣ a + 1) : p ∣ a ^ 2 - 1 := by
  have ha : a ^ 2 - 1 = (a - 1) * (a + 1) := by
    rw [pow_two, mul_self_tsub_one, mul_comm]
  rw [ha]
  exact h.mul_left (a - 1)

theorem largeEvenHalfSplit_true {p : ℕ} {lab : LargeEvenLabel} {c : Prop}
    (h : LargeEvenHalfSplit p lab c) : LargeEvenHalfSplit p lab True := by
  rcases h with h | h | h | ⟨ht, hr, hn, -, hp⟩ | h | h
  · exact Or.inl h
  · exact Or.inr (Or.inl h)
  · exact Or.inr (Or.inr (Or.inl h))
  · exact Or.inr (Or.inr (Or.inr (Or.inl ⟨ht, hr, hn, trivial, hp⟩)))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))

theorem largeEvenHalfSplit_dvd {p : ℕ} {lab : LargeEvenLabel} {c : Prop}
    (hlab : LargeEvenInLambda2 lab) (h : LargeEvenHalfSplit p lab c) :
    p ∣ (2 ^ lab.n) ^ 2 - 1 ∨ (p = 7 ∧ (lab = ⟨.A, 8, 1⟩ ∨ lab = ⟨.E6, 0, 1⟩)) := by
  obtain ⟨t, r, n⟩ := lab
  rcases h with (h1 | h2 | h3 | h4) | h5 | h6 | h7 | h8 | h9
  · exact Or.inl (gnhs_dvd_sq_sub_one_of_dvd_sub h1.2)
  · exact Or.inl (gnhs_dvd_sq_sub_one_of_dvd_add h2.2.2)
  · exact Or.inl (gnhs_dvd_sq_sub_one_of_dvd_sub h3.2)
  · refine Or.inl ?_
    rw [h4.1, h4.2]
    norm_num
  · exact Or.inl (gnhs_dvd_sq_sub_one_of_dvd_add h5.2)
  · exact Or.inl (gnhs_dvd_sq_sub_one_of_dvd_sub h6.2)
  · refine Or.inl ?_
    rw [h7.2.2.1, h7.2.2.2.2]
    norm_num
  · refine Or.inr ⟨h8.2.2.2, Or.inl ?_⟩
    exact gnhs_lab_eq h8.1 h8.2.1 h8.2.2.1
  · obtain ⟨h9t, h9n, h9p⟩ := h9
    dsimp only at h9t
    subst h9t
    have hr : r = 0 := hlab.2
    exact Or.inr ⟨h9p, Or.inr (gnhs_lab_eq rfl hr h9n)⟩

theorem eq_of_ggLabelIso_of_exc {lab lab' : LargeEvenLabel}
    (hex : lab = ⟨.A, 8, 1⟩ ∨ lab = ⟨.E6, 0, 1⟩) (h : GGLabelIso lab' lab) : lab' = lab := by
  obtain ⟨t', r', n'⟩ := lab'
  rcases hex with rfl | rfl
  · unfold GGLabelIso at h
    rcases h with h | h | h | h | h | h | h | h <;> simp_all
  · unfold GGLabelIso at h
    rcases h with h | h | h | h | h | h | h | h <;> simp_all

end CFSG.StandardType

end
