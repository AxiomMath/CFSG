module

public import CFSG.Quasithin.Recognition.GoldschmidtFan86TutteRedBound

public section

namespace CFSG.Quasithin.Fan86.Tutte.Red

open CFSG.Quasithin.F6.GoldAmL3T

variable {W : Type} {Γ : SimpleGraph W} {H : Type} [Group H] [MulAction H W]

theorem fixesExtensions_of_arcTrans (hcard : ∀ w, Nat.card (Γ.neighborSet w) = 3)
    (hadj : ∀ (h : H) (u v : W), Γ.Adj (h • u) (h • v) ↔ Γ.Adj u v) {s : ℕ} (hs : 1 ≤ s)
    (ht : ArcTrans H Γ s) (hn : ¬ ArcTrans H Γ (s + 1)) : FixesExtensions H s Γ := by
  intro q w hqw g hg
  by_contra hmove
  refine hn fun P' Q' => ?_
  obtain ⟨h₁, hh₁⟩ := ht (truncArc P') (truncArc Q')
  have hh : ∀ i, i ≤ s → h₁ • P'.vert i = Q'.vert i := hh₁
  have hs1 : s - 1 + 2 = s + 1 := by omega
  have hs2 : s - 1 + 1 = s := by omega
  have hxy : Γ.Adj (Q'.vert s) (Q'.vert (s - 1)) := by
    have := (Q'.adj (s - 1) (by omega)).symm
    rwa [hs2] at this
  have hb : Γ.Adj (Q'.vert s) (Q'.vert (s + 1)) := Q'.adj s (by omega)
  have hby : Q'.vert (s + 1) ≠ Q'.vert (s - 1) := by
    have := Q'.nb (s - 1) (by omega)
    rw [hs1] at this
    exact this.symm
  have ha : Γ.Adj (Q'.vert s) (h₁ • P'.vert (s + 1)) := by
    have := (hadj h₁ _ _).2 (P'.adj s (by omega))
    rwa [hh s le_rfl] at this
  have hay : h₁ • P'.vert (s + 1) ≠ Q'.vert (s - 1) := by
    intro e
    have h2 := P'.nb (s - 1) (by omega)
    rw [hs1] at h2
    exact h2 (MulAction.injective h₁ ((hh (s - 1) (by omega)).trans e.symm))
  by_cases hab : h₁ • P'.vert (s + 1) = Q'.vert (s + 1)
  · refine ⟨h₁, fun i hi => ?_⟩
    by_cases hi' : i ≤ s
    · exact hh i hi'
    · have : i = s + 1 := by omega
      subst this
      exact hab
  · obtain ⟨t, ht'⟩ := ht q (truncArc Q')
    have ht'' : ∀ i, i ≤ s → t • q.vert i = Q'.vert i := ht'
    have hgfix : ∀ i, i ≤ s → g • q.vert i = q.vert i := (Arc.mem_stab H).1 hg
    have hσfix : ∀ i, i ≤ s → (t * g * t⁻¹) • Q'.vert i = Q'.vert i := by
      intro i hi
      rw [← ht'' i hi, mul_smul, mul_smul, inv_smul_smul, hgfix i hi]
    have hc : Γ.Adj (Q'.vert s) (t • w) := by
      have := (hadj t _ _).2 hqw
      rwa [ht'' s le_rfl] at this
    have hcy : t • w ≠ Q'.vert (s - 1) := by
      intro e
      rw [← ht'' (s - 1) (by omega)] at e
      apply hmove
      rw [MulAction.injective t e]
      exact hgfix (s - 1) (by omega)
    have hσc : (t * g * t⁻¹) • (t • w) ≠ t • w := by
      intro e
      apply hmove
      rw [mul_smul, mul_smul, inv_smul_smul] at e
      exact MulAction.injective t e
    have hswap := Red.swap_of_moves (hcard _) hxy (fun v => (t * g * t⁻¹) • v)
      (MulAction.injective _) (hσfix s le_rfl) (hσfix (s - 1) (by omega))
      (fun u v huv => (hadj (t * g * t⁻¹) u v).2 huv) hc hcy hσc ha hay hb hby hab
    refine ⟨(t * g * t⁻¹) * h₁, fun i hi => ?_⟩
    rw [mul_smul]
    by_cases hi' : i ≤ s
    · rw [hh i hi']
      exact hσfix i hi'
    · have : i = s + 1 := by omega
      subst this
      exact hswap

end CFSG.Quasithin.Fan86.Tutte.Red
