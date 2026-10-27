module

public import CFSG.LocalAnalysis.StandardType.SpEightTransvections

public section

namespace CFSG.StandardType.SpEight

open Matrix CFSG.Open CFSG.Blueprint.EvenSource

theorem tvGL_swap_of_omega_eq_one {s s' : Vec} (hs : Q0 s = 0) (hs' : Q0 s' = 0)
    (h : omega s s' = 1) :
    Q0 (s + s') = 1 ∧
      ((tvGL (s + s') : GL Idx (ZMod 2)) : Matrix Idx Idx (ZMod 2)) *ᵥ s = s' := by
  have hQ : Q0 (s + s') = 1 := by
    rw [Q0_add, hs, hs', h]
    decide +kernel
  refine ⟨hQ, ?_⟩
  rw [tvGL_mulVec, omega_add_right s s s', omega_self s, zero_add, h, one_smul]
  funext i
  exact CharTwo.add_cancel_left (s i) (s' i)

theorem exists_singular_pairing_one {s s' : Vec} (hs : Q0 s = 0) (hs0 : s ≠ 0) (hs'0 : s' ≠ 0)
    (horth : omega s s' = 0) :
    ∃ s'' : Vec, Q0 s'' = 0 ∧ omega s s'' = 1 ∧ omega s' s'' = 1 := by
  have hz1 : ∀ c : ZMod 2, c ≠ 0 → c = 1 := by decide +kernel
  have hz0 : ∀ c : ZMod 2, c ≠ 1 → c = 0 := by decide +kernel
  have h1 : ∃ u, omega s u ≠ 0 := by
    by_contra hc
    push Not at hc
    exact hs0 (eq_zero_of_omega_eq_zero hc)
  obtain ⟨v₁, hv₁⟩ := h1
  have hv₁1 : omega s v₁ = 1 := hz1 _ hv₁
  have h2 : ∃ u, omega s' u ≠ 0 := by
    by_contra hc
    push Not at hc
    exact hs'0 (eq_zero_of_omega_eq_zero hc)
  obtain ⟨v₂, hv₂⟩ := h2
  have hv₂1 : omega s' v₂ = 1 := hz1 _ hv₂
  have hv : ∃ v : Vec, omega s v = 1 ∧ omega s' v = 1 := by
    by_cases hcase1 : omega s' v₁ = 1
    · exact ⟨v₁, hv₁1, hcase1⟩
    · by_cases hcase2 : omega s v₂ = 1
      · exact ⟨v₂, hcase2, hv₂1⟩
      · refine ⟨v₁ + v₂, ?_, ?_⟩
        · rw [omega_add_right, hv₁1, hz0 _ hcase2, add_zero]
        · rw [omega_add_right, hz0 _ hcase1, hv₂1, zero_add]
  obtain ⟨v, hsv, hs'v⟩ := hv
  by_cases hQv : Q0 v = 0
  · exact ⟨v, hQv, hsv, hs'v⟩
  · have hQv1 : Q0 v = 1 := hz1 _ hQv
    refine ⟨v + s, ?_, ?_, ?_⟩
    · rw [Q0_add, hQv1, hs, omega_comm v s, hsv]
      decide +kernel
    · rw [omega_add_right, hsv, omega_self, add_zero]
    · rw [omega_add_right, hs'v, omega_comm s' s, horth, add_zero]

theorem exists_mem_matrixOrthogonal_mulVec_eq {s s' : Vec} (hs : Q0 s = 0) (hs' : Q0 s' = 0)
    (hs0 : s ≠ 0) (hs'0 : s' ≠ 0) :
    ∃ o ∈ matrixOrthogonal Q0, ((o : GL Idx (ZMod 2)) : Matrix Idx Idx (ZMod 2)) *ᵥ s = s' := by
  by_cases hss : s = s'
  · exact ⟨1, one_mem _, by simp [hss]⟩
  by_cases h1 : omega s s' = 1
  · obtain ⟨hQ, hmul⟩ := tvGL_swap_of_omega_eq_one hs hs' h1
    exact ⟨tvGL (s + s'), tvGL_mem_matrixOrthogonal hQ, hmul⟩
  · have h0 : omega s s' = 0 := by
      generalize omega s s' = c at h1
      revert c
      decide
    obtain ⟨s'', hs'', h1'', h2''⟩ := exists_singular_pairing_one hs hs0 hs'0 h0
    obtain ⟨hQ1, hmul1⟩ := tvGL_swap_of_omega_eq_one hs hs'' h1''
    have h3 : omega s'' s' = 1 := by rw [omega_comm]; exact h2''
    obtain ⟨hQ2, hmul2⟩ := tvGL_swap_of_omega_eq_one hs'' hs' h3
    refine ⟨tvGL (s'' + s') * tvGL (s + s''), mul_mem (tvGL_mem_matrixOrthogonal hQ2)
      (tvGL_mem_matrixOrthogonal hQ1), ?_⟩
    rw [Units.val_mul, ← Matrix.mulVec_mulVec, hmul1, hmul2]

end CFSG.StandardType.SpEight
