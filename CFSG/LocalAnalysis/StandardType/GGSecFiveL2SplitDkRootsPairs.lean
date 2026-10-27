module

public import CFSG.LocalAnalysis.StandardType.GGSecFiveL2SplitDkRootsBasic

public section

namespace CFSG.StandardType

theorem ggDReflect_comm_dot {k : ℕ} {γ γ' : Fin k → ℤ} (hγ : ggDDot γ γ = 2)
    (hγ' : ggDDot γ' γ' = 2)
    (h : ggDReflect γ (ggDReflect γ' γ) = ggDReflect γ' (ggDReflect γ γ)) :
    ggDDot γ γ' = 0 ∨ γ' = γ ∨ γ' = -γ := by
  rw [ggDDot_eq_dotProduct] at hγ hγ' ⊢
  have hc : γ' ⬝ᵥ γ = γ ⬝ᵥ γ' := dotProduct_comm γ' γ
  simp only [ggDReflect, ggDDot_eq_dotProduct, sub_dotProduct, smul_dotProduct, smul_eq_mul,
    hγ, hc] at h
  generalize hcdef : γ ⬝ᵥ γ' = c at h ⊢
  have hx : ∀ x, c ^ 2 * γ x = 2 * c * γ' x := fun x => by
    have hx := congrFun h x
    simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul] at hx
    linear_combination hx
  have hv : c ^ 2 • γ = (2 * c) • γ' := funext fun x => by
    simp only [Pi.smul_apply, smul_eq_mul]
    exact hx x
  have hs := congrArg (· ⬝ᵥ γ') hv
  simp only [smul_dotProduct, smul_eq_mul, hγ', hcdef] at hs
  have hc3 : c * (c - 2) * (c + 2) = 0 := by linear_combination hs
  rcases mul_eq_zero.1 hc3 with hc2 | hc2
  · rcases mul_eq_zero.1 hc2 with hc0 | hc0
    · exact Or.inl hc0
    · refine Or.inr (Or.inl (funext fun x => ?_))
      have := hx x
      rw [show c = 2 by linarith] at this
      linarith
  · refine Or.inr (Or.inr (funext fun x => ?_))
    have := hx x
    rw [show c = -2 by linarith] at this
    simp only [Pi.neg_apply]
    linarith

private theorem pair_eq_pm {k : ℕ} (a b : Fin k) {s : ℤ} (hs : s = 1 ∨ s = -1) (s' : ℤ) :
    (Pi.single a s + Pi.single b s' : Fin k → ℤ) = Pi.single a 1 + Pi.single b (s * s') ∨
      (Pi.single a s + Pi.single b s' : Fin k → ℤ) = -(Pi.single a 1 + Pi.single b (s * s')) :=
    by
  rcases hs with rfl | rfl
  · left
    rw [one_mul]
  · right
    funext c
    simp only [Pi.add_apply, Pi.neg_apply, Pi.single_apply]
    split_ifs <;> ring

private theorem pair_eq_pm' {k : ℕ} (a b : Fin k) {u : ℤ} (hu : u = 1 ∨ u = -1) (S : ℤ) :
    (Pi.single a u + Pi.single b (-(S * u)) : Fin k → ℤ) = Pi.single a 1 - Pi.single b S ∨
      (Pi.single a u + Pi.single b (-(S * u)) : Fin k → ℤ) =
        -(Pi.single a 1 - Pi.single b S) := by
  rcases hu with rfl | rfl
  · left
    funext c
    simp only [Pi.add_apply, Pi.sub_apply, Pi.single_apply]
    split_ifs <;> ring
  · right
    funext c
    simp only [Pi.add_apply, Pi.sub_apply, Pi.neg_apply, Pi.single_apply]
    split_ifs <;> ring

private theorem orth_same {k : ℕ} {a b : Fin k} (hab : a ≠ b) {s s' u u' : ℤ}
    (hs : s = 1 ∨ s = -1) (hs' : s' = 1 ∨ s' = -1) (hu : u = 1 ∨ u = -1)
    (h : s * u + s' * u' = 0) :
    ∃ (a' b' : Fin k) (S : ℤ), a' ≠ b' ∧ (S = 1 ∨ S = -1) ∧
      ((Pi.single a s + Pi.single b s' : Fin k → ℤ) = Pi.single a' 1 + Pi.single b' S ∨
        (Pi.single a s + Pi.single b s' : Fin k → ℤ) = -(Pi.single a' 1 + Pi.single b' S)) ∧
      ((Pi.single a u + Pi.single b u' : Fin k → ℤ) = Pi.single a' 1 - Pi.single b' S ∨
        (Pi.single a u + Pi.single b u' : Fin k → ℤ) = -(Pi.single a' 1 - Pi.single b' S)) := by
  have hu' : u' = -((s * s') * u) := by
    rcases hs with rfl | rfl <;> rcases hs' with rfl | rfl <;> linarith
  refine ⟨a, b, s * s', hab, ?_, pair_eq_pm a b hs s', ?_⟩
  · rcases hs with rfl | rfl <;> rcases hs' with rfl | rfl <;> norm_num
  · rw [hu']
    exact pair_eq_pm' a b hu (s * s')

theorem ggDRootSet_orth {k : ℕ} {γ γ' : Fin k → ℤ} (hγ : γ ∈ ggDRootSet k)
    (hγ' : γ' ∈ ggDRootSet k) (h : ggDDot γ γ' = 0) :
    (∃ (a b : Fin k) (s : ℤ), a ≠ b ∧ (s = 1 ∨ s = -1) ∧
      (γ = Pi.single a 1 + Pi.single b s ∨ γ = -(Pi.single a 1 + Pi.single b s)) ∧
      (γ' = Pi.single a 1 - Pi.single b s ∨ γ' = -(Pi.single a 1 - Pi.single b s))) ∨
    ∃ (a b c d : Fin k) (s s' u u' : ℤ), a ≠ b ∧ c ≠ d ∧ a ≠ c ∧ a ≠ d ∧ b ≠ c ∧ b ≠ d ∧
      (s = 1 ∨ s = -1) ∧ (s' = 1 ∨ s' = -1) ∧ (u = 1 ∨ u = -1) ∧ (u' = 1 ∨ u' = -1) ∧
      γ = Pi.single a s + Pi.single b s' ∧ γ' = Pi.single c u + Pi.single d u' := by
  obtain ⟨a, b, s, s', hab, hs, hs', rfl⟩ := hγ
  obtain ⟨c, d, u, u', hcd, hu, hu', rfl⟩ := hγ'
  rw [ggDDot_single_add_single] at h
  by_cases hac : a = c
  · subst hac
    by_cases hbd : b = d
    · subst hbd
      rw [ggDPair_apply_left hab, ggDPair_apply_right hab] at h
      exact Or.inl (orth_same hab hs hs' hu h)
    · exfalso
      rw [ggDPair_apply_left hcd, ggDPair_apply_of_ne (Ne.symm hab) hbd] at h
      rcases hs with rfl | rfl <;> rcases hu with rfl | rfl <;> omega
  by_cases had : a = d
  · subst had
    by_cases hbc : b = c
    · subst hbc
      rw [ggDPair_apply_right hcd, ggDPair_apply_left hcd] at h
      obtain ⟨a', b', S, h1, h2, h3, h4⟩ := orth_same hab hs hs' hu' (by linarith)
      refine Or.inl ⟨a', b', S, h1, h2, h3, ?_⟩
      rwa [add_comm] at h4
    · exfalso
      rw [ggDPair_apply_right hcd, ggDPair_apply_of_ne hbc (Ne.symm hab)] at h
      rcases hs with rfl | rfl <;> rcases hu' with rfl | rfl <;> omega
  by_cases hbc : b = c
  · exfalso
    subst hbc
    rw [ggDPair_apply_of_ne hab had, ggDPair_apply_left hcd] at h
    rcases hs' with rfl | rfl <;> rcases hu with rfl | rfl <;> omega
  by_cases hbd : b = d
  · exfalso
    subst hbd
    rw [ggDPair_apply_of_ne hac had, ggDPair_apply_right hcd] at h
    rcases hs' with rfl | rfl <;> rcases hu' with rfl | rfl <;> omega
  exact Or.inr ⟨a, b, c, d, s, s', u, u', hab, hcd, hac, had, hbc, hbd, hs, hs', hu, hu', rfl,
    rfl⟩

theorem ggDRootSet_dot_eq_neg_one {k : ℕ} {γ δ : Fin k → ℤ} (hγ : γ ∈ ggDRootSet k)
    (hδ : δ ∈ ggDRootSet k) (h : ggDDot γ δ = -1) :
    ∃ x y z : Fin k, x ≠ y ∧ y ≠ z ∧ x ≠ z ∧ γ x ≠ 0 ∧ γ y ≠ 0 ∧ δ y ≠ 0 ∧ δ z ≠ 0 ∧
      γ z = 0 ∧ δ x = 0 := by
  obtain ⟨a, b, s, s', hab, hs, hs', rfl⟩ := hγ
  rw [ggDDot_single_add_single] at h
  have ha := ggDRootSet_apply hδ a
  have hb := ggDRootSet_apply hδ b
  have hγa : (Pi.single a s + Pi.single b s' : Fin k → ℤ) a ≠ 0 := by
    rw [ggDPair_apply_left hab]
    omega
  have hγb : (Pi.single a s + Pi.single b s' : Fin k → ℤ) b ≠ 0 := by
    rw [ggDPair_apply_right hab]
    omega
  by_cases hδa : δ a = 0
  · have hδb : δ b ≠ 0 := by
      intro h0
      rw [hδa, h0] at h
      omega
    obtain ⟨z, hzb, hz⟩ := ggDRootSet_exists_ne hδ hδb
    have hza : z ≠ a := fun e => hz (e ▸ hδa)
    exact ⟨a, b, z, hab, hzb.symm, hza.symm, hγa, hγb, hδb, hz,
      ggDPair_apply_of_ne hza hzb s s', hδa⟩
  · have hδb : δ b = 0 := by
      rcases hs with rfl | rfl <;> rcases hs' with rfl | rfl <;> omega
    obtain ⟨z, hza, hz⟩ := ggDRootSet_exists_ne hδ hδa
    have hzb : z ≠ b := fun e => hz (e ▸ hδb)
    exact ⟨b, a, z, hab.symm, hza.symm, hzb.symm, hγb, hγa, hδa, hz,
      ggDPair_apply_of_ne hza hzb s s', hδb⟩

end CFSG.StandardType

end
