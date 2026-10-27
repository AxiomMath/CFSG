module

public import CFSG.Quasithin.Recognition.GoldschmidtFan86Sec9P4Z2B

public section

namespace CFSG.Quasithin.Fan86

open SimpleGraph CFSG.Quasithin.F6.GoldAmL3T

variable {V G : Type*} [Group G] [MulAction G V] {Γ : SimpleGraph V}

theorem trio_excl_f {H : Type*} [Group H] {a b c : H} (hb : b * b = 1) (hc : c * c = 1)
    (hab : a * b = b * a) (hbc : b * c = c * b) (a1 : a ≠ 1) (b1 : b ≠ 1)
    (ab : a ≠ b) (ac' : a ≠ c) (bc' : b ≠ c) (abc : a * b * c ≠ 1) (e f : Fin 2) :
    a * b * c ^ (f : ℕ) ≠ a * c ^ (e : ℕ) ∧ a * b * c ^ (f : ℕ) ≠ b * c ^ (e : ℕ) ∧
      a * b * c ^ (f : ℕ) ≠ c := by
  have hcinv : c⁻¹ = c := inv_eq_of_mul_eq_one_right hc
  have hbinv : b⁻¹ = b := inv_eq_of_mul_eq_one_right hb
  have bc1 : b * c ≠ 1 := fun h => bc' (by rw [← hcinv]; exact eq_inv_of_mul_eq_one_left h)
  have ab1 : a * b ≠ 1 := fun h => ab (by rw [← hbinv]; exact eq_inv_of_mul_eq_one_left h)
  have ac1 : a * c ≠ 1 := fun h => ac' (by rw [← hcinv]; exact eq_inv_of_mul_eq_one_left h)
  fin_cases e <;> fin_cases f
  · simp only [pow_zero, mul_one]
    exact ⟨fun h => b1 (mul_eq_left.1 h), fun h => a1 (mul_eq_right.1 h),
      fun h => abc (by rw [h, hc])⟩
  · simp only [pow_zero, pow_one, mul_one]
    refine ⟨fun h => bc1 (mul_eq_left.1 ((mul_assoc a b c).symm.trans h)), fun h => ac1 ?_,
      fun h => ab1 (mul_eq_right.1 h)⟩
    have h2 : a * c * b = b := by rw [mul_assoc, ← hbc, ← mul_assoc]; exact h
    exact mul_eq_right.1 h2
  · simp only [pow_one, pow_zero, mul_one]
    exact ⟨fun h => bc' (mul_left_cancel h), fun h => ac' (mul_left_cancel (hab.symm.trans h)),
      fun h => abc (by rw [h, hc])⟩
  · simp only [pow_one]
    refine ⟨fun h => b1 (mul_eq_right.1 (mul_left_cancel ((mul_assoc a b c).symm.trans h))),
      fun h => a1 (mul_eq_right.1 (mul_right_cancel h)), fun h => ab1 (mul_eq_right.1 h)⟩

namespace D10Set

variable {L : ZLab Γ G} {α : V} (D : D10Set L α) (F : FanTree Γ G)

include F

theorem fixed_pair_of_shape_f (h71a : Fan71a F L) (h71c : Fan71c F L) (h83a : Fan83a F L)
    (h83b : Fan83b F L) (h87 : Fan87 F L) {δ' : V} (hY : D.IsYPair δ') {g : G}
    (h0 : g • D.alpha 0 = D.alpha 0) (h2 : g • D.alpha 2 = D.alpha 2) (hord : orderOf g = 4)
    (hsq : (∃ f : Fin 2, g * g = L.z (D.alpha 0) * L.z (D.alpha 2) * L.z α ^ (f : ℕ)) ∨
      g * g = L.z (D.alpha 0)) :
    g ∈ nbrStab Γ G α ∧
      (((∃ f : Fin 2, g * g = L.z (D.alpha 0) * L.z (D.alpha 2) * L.z α ^ (f : ℕ)) ∧
          g • D.alpha 1 = D.alpha 1 ∧ g • D.alpha 3 ≠ D.alpha 3 ∧ g • D.alpha 4 ≠ D.alpha 4) ∨
        (g * g = L.z (D.alpha 0) ∧ g • D.alpha 3 = D.alpha 3 ∧
          g • D.alpha 1 ≠ D.alpha 1 ∧ g • D.alpha 4 ≠ D.alpha 4)) := by
  have hpath : ∀ v ∈ pathSet Γ (D.alpha 0) (D.alpha 2), g • v = v := fun v hv =>
    fixes_pathSet F h0 h2 hv
  have hsqE : ∃ e₁ e₂ e₃ : Fin 2, g * g = L.z (D.alpha 0) ^ (e₁ : ℕ) * L.z (D.alpha 2) ^ (e₂ : ℕ) *
      L.z α ^ (e₃ : ℕ) := by
    rcases hsq with ⟨f, h⟩ | h
    · exact ⟨1, 1, f, by simpa using h⟩
    · exact ⟨1, 0, 0, by simpa using h⟩
  have k02 : kstar 0 2 = (4 : Fin 5) := by decide
  have k20 : kstar 2 0 = (3 : Fin 5) := by decide
  have m02 : midlab 0 2 = (1 : Fin 5) := by decide
  have hb : L.z (D.alpha 2) * L.z (D.alpha 2) = 1 := D.za_mul_self F 2
  have hc : L.z α * L.z α = 1 := L.z_mul_self D.val
  have hab : L.z (D.alpha 0) * L.z (D.alpha 2) = L.z (D.alpha 2) * L.z (D.alpha 0) :=
    D.za_comm F h71c 0 2
  have hbc : L.z (D.alpha 2) * L.z α = L.z α * L.z (D.alpha 2) := D.za_comm_start F h71c 2
  have a1 := D.zAlpha_ne_one F 0
  have b1 := D.zAlpha_ne_one F 2
  have ab := D.zAlpha_ne F h71c (show (0 : Fin 5) ≠ 2 by decide)
  have ac := D.zAlpha_ne_zStart F h71c 0
  have bc := D.zAlpha_ne_zStart F h71c 2
  have abc := D.zAlpha_prod_ne_one F h71c (show (0 : Fin 5) ≠ 2 by decide)
  have hy := D.y_mem_nbrStab F h83a hY
  have hyf := D.y_fix_alpha_iff F h71c h83b hY
  have hvf : ∀ {v : G}, v ∈ L.zGroup 2 α → ∀ m : Fin 5, v • D.alpha m = D.alpha m :=
    fun hv m => zGroup_smul_eq h71c hv (by rw [D.dist_start_alpha F m])
  have hcf : ∀ {c : G}, c ∈ D.calpha → ∀ m : Fin 5, c • D.alpha m = D.alpha m :=
    fun hc m => D.calpha_smul_alpha F h71a h71c hc m
  have hyy : ∀ (p q : Fin 5) (m : Fin 5),
      (D.y δ' p * D.y δ' q) • D.alpha m = D.alpha m ↔ ((p = m) ↔ (q = m)) := fun p q m => by
    rw [D.fix_mul_iff F (hy p) (hy q) m, hyf p m, hyf q m]
  rcases h87 α D δ' hY 0 2 (by decide) g hpath hord hsqE with
    ⟨v, hv, e, hg, hg2⟩ | ⟨v, hv, c, hc', hc4, e, hg, hg2⟩ | ⟨v, hv, c, hc', hc4, e, hg, hg2⟩ |
      ⟨v, hv, c, hc', hc4, hg, hg2⟩
  · rw [k02, k20] at hg
    have hvn := zGroup_mem_nbrStab F h71c hv
    have hgn : g ∈ nbrStab Γ G α := by
      rw [hg]
      exact mul_mem (mul_mem (hy 4) (hy 3)) hvn
    have key : ∀ m : Fin 5, g • D.alpha m = D.alpha m ↔ ((4 : Fin 5) = m ↔ (3 : Fin 5) = m) := by
      intro m
      rw [hg, D.fix_mul_iff F (mul_mem (hy 4) (hy 3)) hvn m, hyy 4 3 m]
      simp [hvf hv m]
    rcases hsq with hs | hs
    · refine ⟨hgn, Or.inl ⟨hs, (key 1).2 (by decide), fun h' => ?_, fun h' => ?_⟩⟩
      · have := (key 3).1 h'
        revert this; decide
      · have := (key 4).1 h'
        revert this; decide
    · exfalso
      rw [hg2] at hs
      have := (trio_excl hb hc hab hbc a1 b1 ab ac bc abc e).2.2.2.1
      exact this hs.symm
  · rw [k02, m02] at hg
    have hvn := zGroup_mem_nbrStab F h71c hv
    have hcn := D.calpha_mem_nbrStab hc'
    have hgn : g ∈ nbrStab Γ G α := by
      rw [hg]
      exact mul_mem (mul_mem (mul_mem (hy 4) (hy 1)) hvn) hcn
    have key : ∀ m : Fin 5, g • D.alpha m = D.alpha m ↔ ((4 : Fin 5) = m ↔ (1 : Fin 5) = m) := by
      intro m
      rw [hg, D.fix_mul_iff F (mul_mem (mul_mem (hy 4) (hy 1)) hvn) hcn m,
        D.fix_mul_iff F (mul_mem (hy 4) (hy 1)) hvn m, hyy 4 1 m]
      simp [hvf hv m, hcf hc' m]
    rcases hsq with ⟨f, hs⟩ | hs
    · exfalso
      rw [hg2] at hs
      exact (trio_excl_f hb hc hab hbc a1 b1 ab ac bc abc e f).1 hs.symm
    · refine ⟨hgn, Or.inr ⟨hs, (key 3).2 (by decide), fun h' => ?_, fun h' => ?_⟩⟩
      · have := (key 1).1 h'
        revert this; decide
      · have := (key 4).1 h'
        revert this; decide
  · exfalso
    rcases hsq with ⟨f, hs⟩ | hs
    · rw [hg2] at hs
      exact (trio_excl_f hb hc hab hbc a1 b1 ab ac bc abc e f).2.1 hs.symm
    · rw [hg2] at hs
      exact (trio_excl hb hc hab hbc a1 b1 ab ac bc abc e).2.2.2.2 hs.symm
  · exfalso
    rcases hsq with ⟨f, hs⟩ | hs
    · rw [hg2] at hs
      exact (trio_excl_f hb hc hab hbc a1 b1 ab ac bc abc 0 f).2.2 hs.symm
    · rw [hg2] at hs
      exact ac hs.symm

end D10Set

end CFSG.Quasithin.Fan86
