module

public import CFSG.Quasithin.EmptyFaithful.S146zNFinQ
public import CFSG.Quasithin.EmptyFaithful.S146zNFinK

public section

namespace CFSG.Quasithin.A6Fin

open Equiv Equiv.Perm CFSG.Quasithin CFSG.Quasithin.A6Mod

variable {W : Type} [CommGroup W] [Finite W] {ρ : A6 →* MulAut W}

theorem x0A6_sq : x0A6 * x0A6 = 1 := Subtype.ext rel_x0y0.1

theorem Setup.fc_x0A6 (h : Setup ρ) : fc ρ x0A6 = 4 := by
  classical
  have hF := F2_16 ρ h.nontrivial h.card
  have hsum := h.sum_fc
  set i := fc ρ x0A6 with hi
  set fa := fc ρ a with hfa
  set fb := fc ρ (a * a') with hfb
  have hab : fa + fb = 5 := by omega
  let lb : Fin 6 → ℕ := ![16, i, fa, fb, 2, 1]
  have hlb : ∀ g : A6, lb (cls g.1) ≤ fc ρ g := by
    intro g
    unfold cls
    by_cases h1 : g.1 = 1
    · have : g = 1 := Subtype.ext h1
      subst this
      simp only [h1, ite_true]
      show 16 ≤ fc ρ 1
      rw [fc_one, h.card]
    · simp only [h1, ite_false]
      by_cases h2 : g.1 * g.1 = 1
      · simp only [h2, ite_true]
        show i ≤ fc ρ g
        rw [fc_invol g (fun hg => h1 (by rw [hg]; rfl)) (Subtype.ext h2)]
      · simp only [h2, ite_false]
        by_cases h3 : g.1 * g.1 * g.1 = 1
        · simp only [h3, ite_true]
          have hg3 : g ^ 3 = 1 := Subtype.ext (by simpa [pow_succ, mul_assoc] using h3)
          have hg1 : g ≠ 1 := fun hg => h1 (by rw [hg]; rfl)
          by_cases h4 : ∃ j, g.1 j = j
          · simp only [h4, ite_true]
            show fa ≤ fc ρ g
            rw [fc_T g ⟨hg3, hg1, h4⟩]
          · simp only [h4, ite_false]
            show fb ≤ fc ρ g
            have : ∀ j, g.1 j ≠ j := fun j hj => h4 ⟨j, hj⟩
            rw [fc_U g ⟨hg3, hg1, this⟩]
        · simp only [h3, ite_false]
          by_cases h5 : g.1 * g.1 * g.1 * g.1 = 1
          · simp only [h5, ite_true]
            show 2 ≤ fc ρ g
            exact h.two_le_fc g (Subtype.ext h5)
          · simp only [h5, ite_false]
            show 1 ≤ fc ρ g
            exact Nat.card_pos
  have hsumlb : ∑ g : A6, lb (cls g.1) ≤ 720 := by
    rw [← hsum]
    exact Finset.sum_le_sum fun g _ => hlb g
  have hfib : ∑ g : A6, lb (cls g.1) =
      ∑ k : Fin 6, (Finset.univ.filter fun g : A6 => cls g.1 = k).card * lb k := by
    rw [← Finset.sum_fiberwise Finset.univ (fun g : A6 => cls g.1) (fun g => lb (cls g.1))]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [Finset.sum_congr rfl (fun g hg => by rw [(Finset.mem_filter.mp hg).2] : ∀ g ∈
      Finset.univ.filter (fun g : A6 => cls g.1 = k), lb (cls g.1) = lb k)]
    simp [Finset.sum_const]
  obtain ⟨c0, c1, c2, c3, c4, c5⟩ := cls_count
  rw [hfib, Fin.sum_univ_six, c0, c1, c2, c3, c4, c5] at hsumlb
  simp only [lb, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val] at hsumlb
  have hge : 16 ≤ i * i := by
    have := le_card_fixSub_sq h.sq (ρ x0A6) (by rw [← map_mul, x0A6_sq, map_one])
    rw [h.card] at this
    exact this
  have hle : i ≤ 4 := by omega
  interval_cases i <;> omega

end CFSG.Quasithin.A6Fin
