module

public import CFSG.LocalAnalysis.StandardType.GGTwoPlaneThree
public import CFSG.LocalAnalysis.StandardType.GGSixSeventeenWitOmGlue
public import CFSG.LocalAnalysis.StandardType.GGSixSeventeenWitOmFix
public import CFSG.LocalAnalysis.StandardType.GGSixRootFusionWitOmBlkCore
public import CFSG.LocalAnalysis.StandardType.GGTableBOrthogonalDiag
public import CFSG.LocalAnalysis.StandardType.GGInterfaceSix
public import CFSG.LocalAnalysis.StandardType.GGOneFiveDefs

public section

namespace CFSG.StandardType

namespace OrthYFusion

open QuadraticMap Module

variable {K V : Type} [Field K] [CharP K 2] [AddCommGroup V] [Module K V] {Q : QuadraticForm K V}

private theorem polar_dual_four {a₁ a₂ a₃ a₄ : V}
    (h₁₂ : polar Q a₁ a₂ = 1) (h₃₄ : polar Q a₃ a₄ = 1)
    (h₁₃ : polar Q a₁ a₃ = 0) (h₁₄ : polar Q a₁ a₄ = 0)
    (h₂₃ : polar Q a₂ a₃ = 0) (h₂₄ : polar Q a₂ a₄ = 0) (i j : Fin 4) :
    polar Q (![a₁, a₂, a₃, a₄] i) (![a₂, a₁, a₄, a₃] j) = if i = j then 1 else 0 := by
  have h₂₁ : polar Q a₂ a₁ = 1 := by rw [QuadraticMap.polar_comm]; exact h₁₂
  have h₄₃ : polar Q a₄ a₃ = 1 := by rw [QuadraticMap.polar_comm]; exact h₃₄
  have h₃₁ : polar Q a₃ a₁ = 0 := by rw [QuadraticMap.polar_comm]; exact h₁₃
  have h₄₁ : polar Q a₄ a₁ = 0 := by rw [QuadraticMap.polar_comm]; exact h₁₄
  have h₃₂ : polar Q a₃ a₂ = 0 := by rw [QuadraticMap.polar_comm]; exact h₂₃
  have h₄₂ : polar Q a₄ a₂ = 0 := by rw [QuadraticMap.polar_comm]; exact h₂₄
  fin_cases i <;> fin_cases j <;>
    simp [-QuadraticMap.polar_self, h₁₂, h₂₁, h₃₄, h₄₃, h₁₃, h₃₁, h₁₄, h₄₁,
      h₂₃, h₃₂, h₂₄, h₄₂, CFSG.RankThree.OrthogonalInvolutions.polar_self_eq_zero]

private theorem linearIndependent_four {a₁ a₂ a₃ a₄ : V}
    (h₁₂ : polar Q a₁ a₂ = 1) (h₃₄ : polar Q a₃ a₄ = 1)
    (h₁₃ : polar Q a₁ a₃ = 0) (h₁₄ : polar Q a₁ a₄ = 0)
    (h₂₃ : polar Q a₂ a₃ = 0) (h₂₄ : polar Q a₂ a₄ = 0) :
    LinearIndependent K ![a₁, a₂, a₃, a₄] :=
  TableBOrth.linearIndependent_of_polar_dual (QF := Q) (d := ![a₂, a₁, a₄, a₃])
    (polar_dual_four h₁₂ h₃₄ h₁₃ h₁₄ h₂₃ h₂₄)

private theorem polar_four_apply {a₁ a₂ a₃ a₄ : V}
    (h₁₂ : polar Q a₁ a₂ = 1) (h₃₄ : polar Q a₃ a₄ = 1)
    (h₁₃ : polar Q a₁ a₃ = 0) (h₁₄ : polar Q a₁ a₄ = 0)
    (h₂₃ : polar Q a₂ a₃ = 0) (h₂₄ : polar Q a₂ a₄ = 0)
    (c₁ c₂ c₃ c₄ : K) (i : Fin 4) :
    polar Q (![a₁, a₂, a₃, a₄] i) (c₁ • a₁ + c₂ • a₂ + c₃ • a₃ + c₄ • a₄) =
      ![c₂, c₁, c₄, c₃] i := by
  have h₂₁ : polar Q a₂ a₁ = 1 := by rw [QuadraticMap.polar_comm]; exact h₁₂
  have h₄₃ : polar Q a₄ a₃ = 1 := by rw [QuadraticMap.polar_comm]; exact h₃₄
  have h₃₁ : polar Q a₃ a₁ = 0 := by rw [QuadraticMap.polar_comm]; exact h₁₃
  have h₄₁ : polar Q a₄ a₁ = 0 := by rw [QuadraticMap.polar_comm]; exact h₁₄
  have h₃₂ : polar Q a₃ a₂ = 0 := by rw [QuadraticMap.polar_comm]; exact h₂₃
  have h₄₂ : polar Q a₄ a₂ = 0 := by rw [QuadraticMap.polar_comm]; exact h₂₄
  fin_cases i <;>
    simp [-QuadraticMap.polar_self, h₁₂, h₂₁, h₃₄, h₄₃, h₁₃, h₃₁, h₁₄, h₄₁,
      h₂₃, h₃₂, h₂₄, h₄₂, CFSG.RankThree.OrthogonalInvolutions.polar_self_eq_zero,
        smul_eq_mul]

private theorem polar_four_val {a₁ a₂ a₃ a₄ : V}
    (h₁₂ : polar Q a₁ a₂ = 1) (h₃₄ : polar Q a₃ a₄ = 1)
    (h₁₃ : polar Q a₁ a₃ = 0) (h₁₄ : polar Q a₁ a₄ = 0)
    (h₂₃ : polar Q a₂ a₃ = 0) (h₂₄ : polar Q a₂ a₄ = 0) (i j : Fin 4) :
    polar Q (![a₁, a₂, a₃, a₄] i) (![a₁, a₂, a₃, a₄] j) =
      if (i = 0 ∧ j = 1) ∨ (i = 1 ∧ j = 0) ∨ (i = 2 ∧ j = 3) ∨ (i = 3 ∧ j = 2)
        then 1 else 0 := by
  have h₂₁ : polar Q a₂ a₁ = 1 := by rw [QuadraticMap.polar_comm]; exact h₁₂
  have h₄₃ : polar Q a₄ a₃ = 1 := by rw [QuadraticMap.polar_comm]; exact h₃₄
  have h₃₁ : polar Q a₃ a₁ = 0 := by rw [QuadraticMap.polar_comm]; exact h₁₃
  have h₄₁ : polar Q a₄ a₁ = 0 := by rw [QuadraticMap.polar_comm]; exact h₁₄
  have h₃₂ : polar Q a₃ a₂ = 0 := by rw [QuadraticMap.polar_comm]; exact h₂₃
  have h₄₂ : polar Q a₄ a₂ = 0 := by rw [QuadraticMap.polar_comm]; exact h₂₄
  fin_cases i <;> fin_cases j <;>
    simp [-QuadraticMap.polar_self, h₁₂, h₂₁, h₃₄, h₄₃, h₁₃, h₃₁, h₁₄, h₄₁,
      h₂₃, h₃₂, h₂₄, h₄₂, CFSG.RankThree.OrthogonalInvolutions.polar_self_eq_zero]

private theorem nondegOn_span_of_dual {ι : Type} [Fintype ι] [DecidableEq ι]
    {v d : ι → V} (hd : ∀ j, d j ∈ Submodule.span K (Set.range v))
    (h : ∀ i j, polar Q (v i) (d j) = if i = j then 1 else 0) :
    SUTB.NondegOn (polarBilin Q) (Submodule.span K (Set.range v)) := by
  intro x hx hx0
  obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun K).mp hx
  have hc0 : ∀ j, c j = 0 := by
    intro j
    have h1 : polar Q x (d j) = 0 := by
      rw [QuadraticMap.polar_comm]
      exact hx0 (d j) (hd j)
    rw [← hc] at h1
    rw [← QuadraticMap.polarBilin_apply_apply] at h1
    rw [map_sum, LinearMap.sum_apply] at h1
    simp only [map_smul, LinearMap.smul_apply, QuadraticMap.polarBilin_apply_apply, h,
      smul_eq_mul, mul_ite, mul_one, mul_zero] at h1
    rw [Finset.sum_ite_eq'] at h1
    simpa using h1
  rw [← hc]
  simp [hc0]

private theorem even_of_three_dvd_two_pow_sub_one {m : ℕ} (h : 3 ∣ 2 ^ m - 1) : Even m := by
  by_contra hm
  have hodd : Odd m := Nat.not_even_iff_odd.mp hm
  have hm1 : 1 ≤ 2 ^ m := Nat.one_le_two_pow
  have h0 : ((2 ^ m - 1 : ℕ) : ZMod 3) = 0 := (ZMod.natCast_eq_zero_iff _ 3).mpr h
  rw [Nat.cast_sub hm1, Nat.cast_pow, Nat.cast_ofNat, Nat.cast_one] at h0
  have h1 : ((2 : ZMod 3)) ^ m = 1 := sub_eq_zero.mp h0
  rw [show (2 : ZMod 3) = -1 by decide] at h1
  rw [hodd.neg_one_pow] at h1
  exact absurd h1 (by decide)

private theorem frame_finrank_four_le {K V : Type} [Field K] [AddCommGroup V] [Module K V]
    [FiniteDimensional K V]
    {Q : QuadraticForm K V} {p : ℕ} {A : Subgroup (V ≃ₗ[K] V)} {r : ℕ}
    (F : SevOm.Frame Q p A r) {a b c d : Fin r}
    (hab : a ≠ b) (hac : a ≠ c) (had : a ≠ d) (hbc : b ≠ c) (hbd : b ≠ d) (hcd : c ≠ d)
    {W : Submodule K V} (ha : F.U a ≤ W) (hb : F.U b ≤ W) (hc : F.U c ≤ W)
    (hd : F.U d ≤ W) :
    finrank K (F.U a) + finrank K (F.U b) + finrank K (F.U c) + finrank K (F.U d) ≤
      finrank K W := by
  have hdisj3 : (F.U a ⊔ F.U b) ⊓ F.U c = ⊥ := by
    refine (Submodule.eq_bot_iff _).mpr fun w hw => F.nondeg c w hw.2 fun v hv => ?_
    obtain ⟨x, hx, y, hy, rfl⟩ := Submodule.mem_sup.mp hw.1
    rw [QuadraticMap.polar_add_right, F.orth c a (Ne.symm hac) v hv x hx,
      F.orth c b (Ne.symm hbc) v hv y hy, add_zero]
  have hdisj4 : ((F.U a ⊔ F.U b) ⊔ F.U c) ⊓ F.U d = ⊥ := by
    refine (Submodule.eq_bot_iff _).mpr fun w hw => F.nondeg d w hw.2 fun v hv => ?_
    obtain ⟨x, hx, y, hy, rfl⟩ := Submodule.mem_sup.mp hw.1
    obtain ⟨x₁, hx₁, x₂, hx₂, rfl⟩ := Submodule.mem_sup.mp hx
    rw [QuadraticMap.polar_add_right, QuadraticMap.polar_add_right,
      F.orth d a (Ne.symm had) v hv x₁ hx₁,
      F.orth d b (Ne.symm hbd) v hv x₂ hx₂,
      F.orth d c (Ne.symm hcd) v hv y hy, add_zero, add_zero]
  have h1 := Submodule.finrank_sup_add_finrank_inf_eq (F.U a) (F.U b)
  rw [F.inf_eq_bot hab, finrank_bot, add_zero] at h1
  have h2 := Submodule.finrank_sup_add_finrank_inf_eq (F.U a ⊔ F.U b) (F.U c)
  rw [hdisj3, finrank_bot, add_zero, h1] at h2
  have h3 := Submodule.finrank_sup_add_finrank_inf_eq ((F.U a ⊔ F.U b) ⊔ F.U c) (F.U d)
  rw [hdisj4, finrank_bot, add_zero, h2] at h3
  rw [← h3]
  exact Submodule.finrank_mono (sup_le (sup_le (sup_le ha hb) hc) hd)

end OrthYFusion

namespace GGTwoPlaneThree

open QuadraticMap Module

theorem exists_orthDerived_conj {K V : Type} [Field K] [Finite K] [CharP K 2]
    [AddCommGroup V] [Module K V] [FiniteDimensional K V] {Q : QuadraticForm K V}
    (hQ : (QuadraticMap.polarBilin Q).Nondegenerate)
    (hT : ∃ T : Submodule K V, Module.finrank K T = 3 ∧ ∀ x ∈ T, Q x = 0)
    (hdim : 5 ≤ Module.finrank K V) {y b : V ≃ₗ[K] V}
    (hbO : b ∈ TauCeti.QuadraticMap.orthogonalGroup Q) {v₁ v₂ w₁ w₂ : V}
    (hy : GGTwoPlaneThree Q y v₁ v₂) (hb : GGTwoPlaneThree Q b w₁ w₂) :
    ∃ g ∈ CFSG.RankThree.Classical2.orthDerived Q, g * y = b * g := by
  classical
  set u : Fin 4 → V := ![v₁, y v₁, v₂, y v₂] with hu
  set u' : Fin 4 → V := ![w₁, b w₁, w₂, b w₂] with hu'
  have hu0 : u 0 = v₁ := by simp [hu]
  have hu1 : u 1 = y v₁ := by simp [hu]
  have hu2 : u 2 = v₂ := by simp [hu]
  have hu3 : u 3 = y v₂ := by simp [hu]
  have hu'0 : u' 0 = w₁ := by simp [hu']
  have hu'1 : u' 1 = b w₁ := by simp [hu']
  have hu'2 : u' 2 = w₂ := by simp [hu']
  have hu'3 : u' 3 = b w₂ := by simp [hu']
  have hu_li : LinearIndependent K u := by
    rw [hu]
    exact OrthYFusion.linearIndependent_four hy.polar_v₁_yv₁ hy.polar_v₂_yv₂ hy.polar_v₁_v₂
      hy.polar_v₁_yv₂ hy.polar_yv₁_v₂ hy.polar_yv₁_yv₂
  have hu'_li : LinearIndependent K u' := by
    rw [hu']
    exact OrthYFusion.linearIndependent_four hb.polar_v₁_yv₁ hb.polar_v₂_yv₂ hb.polar_v₁_v₂
      hb.polar_v₁_yv₂ hb.polar_yv₁_v₂ hb.polar_yv₁_yv₂
  have hQv : ∀ i, Q (u' i) = Q (u i) := by
    intro i
    fin_cases i <;>
      simp [hu0, hu1, hu2, hu3, hu'0, hu'1, hu'2, hu'3, hy.Q_v₁, hy.Q_yv₁, hy.Q_v₂,
        hy.Q_yv₂, hb.Q_v₁, hb.Q_yv₁, hb.Q_v₂, hb.Q_yv₂]
  have hpol : ∀ i j, polar Q (u' i) (u' j) = polar Q (u i) (u j) := by
    intro i j
    have h₁ := OrthYFusion.polar_four_val (a₁ := w₁) (a₂ := b w₁) (a₃ := w₂) (a₄ := b w₂)
      hb.polar_v₁_yv₁ hb.polar_v₂_yv₂ hb.polar_v₁_v₂ hb.polar_v₁_yv₂ hb.polar_yv₁_v₂
      hb.polar_yv₁_yv₂ i j
    have h₂ := OrthYFusion.polar_four_val (a₁ := v₁) (a₂ := y v₁) (a₃ := v₂) (a₄ := y v₂)
      hy.polar_v₁_yv₁ hy.polar_v₂_yv₂ hy.polar_v₁_v₂ hy.polar_v₁_yv₂ hy.polar_yv₁_v₂
      hy.polar_yv₁_yv₂ i j
    simpa only [hu0, hu1, hu2, hu3, hu'0, hu'1, hu'2, hu'3] using h₁.trans h₂.symm
  obtain ⟨g₀, hg₀O, hg₀u⟩ := TableBOrth.exists_orth_apply_eq hQ u u' hu_li hu'_li hQv hpol
  have hg₀0 : g₀ v₁ = w₁ := by simpa [hu0, hu'0] using hg₀u 0
  have hg₀1 : g₀ (y v₁) = b w₁ := by simpa [hu1, hu'1] using hg₀u 1
  have hg₀2 : g₀ v₂ = w₂ := by simpa [hu2, hu'2] using hg₀u 2
  have hg₀3 : g₀ (y v₂) = b w₂ := by simpa [hu3, hu'3] using hg₀u 3
  have hgy : g₀ * y = b * g₀ := by
    apply LinearEquiv.ext
    intro v
    rw [LinearEquiv.mul_apply, LinearEquiv.mul_apply]
    let s : V := polar Q v (y v₁) • v₁ + polar Q v v₁ • y v₁ + polar Q v (y v₂) • v₂ +
      polar Q v v₂ • y v₂
    have hs_eq : s = polar Q v (y v₁) • u 0 + polar Q v v₁ • u 1 + polar Q v (y v₂) • u 2 +
        polar Q v v₂ • u 3 := by
      simp [s, hu0, hu1, hu2, hu3]
    have hmem : s ∈ Submodule.span K (Set.range u) := by
      rw [hs_eq]
      refine Submodule.add_mem (Submodule.span K (Set.range u))
        (Submodule.add_mem (Submodule.span K (Set.range u))
          (Submodule.add_mem (Submodule.span K (Set.range u))
            (Submodule.smul_mem (Submodule.span K (Set.range u)) _
              (Submodule.subset_span (Set.mem_range_self (f := u) (0 : Fin 4))))
            (Submodule.smul_mem (Submodule.span K (Set.range u)) _
              (Submodule.subset_span (Set.mem_range_self (f := u) (1 : Fin 4)))))
          (Submodule.smul_mem (Submodule.span K (Set.range u)) _
            (Submodule.subset_span (Set.mem_range_self (f := u) (2 : Fin 4)))))
        (Submodule.smul_mem (Submodule.span K (Set.range u)) _
          (Submodule.subset_span (Set.mem_range_self (f := u) (3 : Fin 4))))
    have h₁ : polar Q v₁ s = polar Q v v₁ := by
      have h := OrthYFusion.polar_four_apply (a₁ := v₁) (a₂ := y v₁) (a₃ := v₂) (a₄ := y v₂)
        hy.polar_v₁_yv₁ hy.polar_v₂_yv₂ hy.polar_v₁_v₂ hy.polar_v₁_yv₂ hy.polar_yv₁_v₂
        hy.polar_yv₁_yv₂ (polar Q v (y v₁)) (polar Q v v₁) (polar Q v (y v₂)) (polar Q v v₂)
        0
      simpa [s] using h
    have h₂ : polar Q (y v₁) s = polar Q v (y v₁) := by
      have h := OrthYFusion.polar_four_apply (a₁ := v₁) (a₂ := y v₁) (a₃ := v₂) (a₄ := y v₂)
        hy.polar_v₁_yv₁ hy.polar_v₂_yv₂ hy.polar_v₁_v₂ hy.polar_v₁_yv₂ hy.polar_yv₁_v₂
        hy.polar_yv₁_yv₂ (polar Q v (y v₁)) (polar Q v v₁) (polar Q v (y v₂)) (polar Q v v₂)
        1
      simpa [s] using h
    have h₃ : polar Q v₂ s = polar Q v v₂ := by
      have h := OrthYFusion.polar_four_apply (a₁ := v₁) (a₂ := y v₁) (a₃ := v₂) (a₄ := y v₂)
        hy.polar_v₁_yv₁ hy.polar_v₂_yv₂ hy.polar_v₁_v₂ hy.polar_v₁_yv₂ hy.polar_yv₁_v₂
        hy.polar_yv₁_yv₂ (polar Q v (y v₁)) (polar Q v v₁) (polar Q v (y v₂)) (polar Q v v₂)
        2
      simpa [s] using h
    have h₄ : polar Q (y v₂) s = polar Q v (y v₂) := by
      have h := OrthYFusion.polar_four_apply (a₁ := v₁) (a₂ := y v₁) (a₃ := v₂) (a₄ := y v₂)
        hy.polar_v₁_yv₁ hy.polar_v₂_yv₂ hy.polar_v₁_v₂ hy.polar_v₁_yv₂ hy.polar_yv₁_v₂
        hy.polar_yv₁_yv₂ (polar Q v (y v₁)) (polar Q v v₁) (polar Q v (y v₂)) (polar Q v v₂)
        3
      simpa [s] using h
    have hw_orth : ∀ i, polar Q (u i) (v - s) = 0 := by
      intro i
      fin_cases i
      · change polar Q (u 0) (v - s) = 0
        rw [hu0, QuadraticMap.polar_sub_right Q, h₁, QuadraticMap.polar_comm]
        exact sub_self _
      · change polar Q (u 1) (v - s) = 0
        rw [hu1, QuadraticMap.polar_sub_right Q, h₂, QuadraticMap.polar_comm]
        exact sub_self _
      · change polar Q (u 2) (v - s) = 0
        rw [hu2, QuadraticMap.polar_sub_right Q, h₃, QuadraticMap.polar_comm]
        exact sub_self _
      · change polar Q (u 3) (v - s) = 0
        rw [hu3, QuadraticMap.polar_sub_right Q, h₄, QuadraticMap.polar_comm]
        exact sub_self _
    have hyw : y (v - s) = v - s := by
      refine hy.fix (v - s) ?_ ?_ ?_ ?_
      · simpa [hu0] using hw_orth 0
      · simpa [hu1] using hw_orth 1
      · simpa [hu2] using hw_orth 2
      · simpa [hu3] using hw_orth 3
    have hg₀w_orth : ∀ i, polar Q (u' i) (g₀ (v - s)) = 0 := by
      intro i
      rw [← hg₀u i, TauCeti.QuadraticMap.polar_apply_of_mem_orthogonalGroup hg₀O]
      exact hw_orth i
    have hbw : b (g₀ (v - s)) = g₀ (v - s) := by
      refine hb.fix (g₀ (v - s)) ?_ ?_ ?_ ?_
      · simpa [hu'0] using hg₀w_orth 0
      · simpa [hu'1] using hg₀w_orth 1
      · simpa [hu'2] using hg₀w_orth 2
      · simpa [hu'3] using hg₀w_orth 3
    have hspan : ∀ x ∈ Submodule.span K (Set.range u), b (g₀ x) = g₀ (y x) := by
      intro x hx
      induction hx using Submodule.span_induction with
      | mem x hx =>
        obtain ⟨i, rfl⟩ := hx
        fin_cases i
        · change b (g₀ (u 0)) = g₀ (y (u 0))
          rw [hu0, hg₀1, hg₀0]
        · change b (g₀ (u 1)) = g₀ (y (u 1))
          rw [hu1, hg₀1, hy.sq_v₁, map_add, hg₀1, hg₀0, hb.sq_v₁]
        · change b (g₀ (u 2)) = g₀ (y (u 2))
          rw [hu2, hg₀3, hg₀2]
        · change b (g₀ (u 3)) = g₀ (y (u 3))
          rw [hu3, hg₀3, hy.sq_v₂, map_add, hg₀3, hg₀2, hb.sq_v₂]
      | zero => simp
      | add x x' _ _ ih ih' => simp only [map_add, ih, ih']
      | smul a x _ ih => simp only [map_smul, ih]
    have hbs : b (g₀ s) = g₀ (y s) := hspan s hmem
    have hsv : s + (v - s) = v := by abel
    calc g₀ (y v) = g₀ (y (s + (v - s))) := by rw [hsv]
      _ = g₀ (y s + y (v - s)) := by rw [map_add]
      _ = g₀ (y s) + g₀ (y (v - s)) := by rw [map_add]
      _ = g₀ (y s) + g₀ (v - s) := by rw [hyw]
      _ = b (g₀ s) + b (g₀ (v - s)) := by rw [hbs, hbw]
      _ = b (g₀ s + g₀ (v - s)) := by simp only [map_add]
      _ = b (g₀ (s + (v - s))) := by simp only [map_add]
      _ = b (g₀ v) := by rw [hsv]
  have hXnd : SUTB.NondegOn (polarBilin Q) (Submodule.span K (Set.range u')) := by
    refine OrthYFusion.nondegOn_span_of_dual (d := ![b w₁, w₁, b w₂, w₂]) ?_ ?_
    · intro j
      fin_cases j
      · rw [← hu'1]
        exact Submodule.subset_span (Set.mem_range_self (f := u') 1)
      · rw [← hu'0]
        exact Submodule.subset_span (Set.mem_range_self (f := u') 0)
      · rw [← hu'3]
        exact Submodule.subset_span (Set.mem_range_self (f := u') 3)
      · rw [← hu'2]
        exact Submodule.subset_span (Set.mem_range_self (f := u') 2)
    · intro i j
      have h := OrthYFusion.polar_dual_four (a₁ := w₁) (a₂ := b w₁) (a₃ := w₂) (a₄ := b w₂)
        hb.polar_v₁_yv₁ hb.polar_v₂_yv₂ hb.polar_v₁_v₂ hb.polar_v₁_yv₂ hb.polar_yv₁_v₂
        hb.polar_yv₁_yv₂ i j
      simpa only [hu'0, hu'1, hu'2, hu'3] using h
  have hlt : finrank K (Submodule.span K (Set.range u')) < finrank K V := by
    rw [finrank_span_eq_card hu'_li]
    have h4 : Fintype.card (Fin 4) = 4 := Fintype.card_fin 4
    omega
  obtain ⟨w, hwperp, hwQ⟩ := WitOmBlk.exists_quad_ne_zero_orth hQ hXnd hlt
  have hw' : ∀ i, polar Q (u' i) w = 0 := fun i =>
    (QuadraticMap.polarBilin_apply_apply Q (u' i) w).symm.trans
      (Submodule.mem_orthogonalBilin.mp hwperp (u' i)
        (Submodule.subset_span (Set.mem_range_self i)))
  have hbw : b w = w := by
    refine hb.fix w ?_ ?_ ?_ ?_
    · simpa [hu'0] using hw' 0
    · simpa [hu'1] using hw' 1
    · simpa [hu'2] using hw' 2
    · simpa [hu'3] using hw' 3
  let _ : Invertible (Q w) := invertibleOfNonzero hwQ
  set r := TauCeti.QuadraticMap.reflection Q w with hr
  have hrO : r ∈ TauCeti.QuadraticMap.orthogonalGroup Q :=
    TauCeti.QuadraticMap.reflection_mem_orthogonalGroup Q w
  have hr1 : finrank K (CFSG.RankThree.OrthogonalInvolutions.commSpace r) = 1 :=
    CFSG.RankThree.OrthogonalInvolutions.finrank_commSpace_reflection hQ w
  have hcomm : r * b = b * r := by
    apply LinearEquiv.ext
    intro v
    rw [LinearEquiv.mul_apply, LinearEquiv.mul_apply, hr,
      TauCeti.QuadraticMap.reflection_apply_eq_sub_div,
      TauCeti.QuadraticMap.reflection_apply_eq_sub_div, map_sub, map_smul, hbw]
    have h : polar Q w (b v) = polar Q w v := by
      have h1 := TauCeti.QuadraticMap.polar_apply_of_mem_orthogonalGroup hbO w v
      rwa [hbw] at h1
    rw [h]
  have hdich : g₀ ∈ CFSG.RankThree.Classical2.orthDerived Q ∨
      r * g₀ ∈ CFSG.RankThree.Classical2.orthDerived Q := by
    have hΩ : CFSG.RankThree.OrthogonalInvolutions.omegaGroup Q hQ ≤
        CFSG.RankThree.Classical2.orthDerived Q :=
      CFSG.RankThree.PartOne.FieldFix.omegaGroup_le_orthDerived hQ hT
    by_cases hev : Even (finrank K (CFSG.RankThree.OrthogonalInvolutions.commSpace g₀))
    · exact Or.inl (hΩ (CFSG.RankThree.OrthogonalInvolutions.mem_omegaGroup.mpr ⟨hg₀O, hev⟩))
    · refine Or.inr (hΩ (CFSG.RankThree.OrthogonalInvolutions.mem_omegaGroup.mpr
        ⟨mul_mem hrO hg₀O, ?_⟩))
      obtain ⟨k, hk⟩ := Nat.not_even_iff_odd.mp hev
      rw [← ZMod.natCast_eq_zero_iff_even,
        CFSG.RankThree.OrthogonalInvolutions.natCast_finrank_commSpace_mul hQ hrO hg₀O, hr1,
        hk]
      push_cast
      rw [show (2 : ZMod 2) = 0 from rfl, zero_mul, zero_add]
      rfl
  rcases hdich with h | h
  · exact ⟨g₀, h, hgy⟩
  · refine ⟨r * g₀, h, ?_⟩
    rw [mul_assoc, hgy, ← mul_assoc, hcomm, mul_assoc]

end GGTwoPlaneThree

open CFSG.Assembly CFSG.ComponentClassification.CatalogueBOrthogonalSemilinear
  CFSG.RankThree.PartOne.KCOrthComm CFSG.RankThree.Classical2 NoOffOm SevOm
open CFSG.RankThree.PartOne.KCOrthogonal
open QuadraticMap Module Multiplicative

theorem ggSix_centralizer_le_of_twoPlaneThree {G : Type} [Group G] [Finite G] {p : ℕ}
    {B Bs : Subgroup G} {x : G} {L D J : Subgroup G} {d : ℕ}
    {Q : QuadraticForm (GaloisField 2 1) (Fin d → GaloisField 2 1)}
    (hnd : Q.polarBilin.Nondegenerate)
    (hT : ∃ T : Submodule (GaloisField 2 1) (Fin d → GaloisField 2 1),
      Module.finrank (GaloisField 2 1) T = 3 ∧ ∀ x ∈ T, Q x = 0)
    (hd : d = 10 ∨ d = 12)
    (φ : CFSG.ComponentClassification.CatalogueBOrthogonalSemilinear.matrixDerived Q →* G)
    (hφ : Function.Injective φ) (hrange : φ.range = ggG0 p B x L D J)
    (hp : p = 3) (hBs : GGBstar p B Bs) (hBφ : Bs ≤ φ.range) (hcard : p ^ 4 ≤ Nat.card Bs)
    (s2 : GGSixStepTwo p B Bs x L D J)
    {y : CFSG.ComponentClassification.CatalogueBOrthogonalSemilinear.matrixDerived Q}
    {v₁ v₂ : Fin d → GaloisField 2 1}
    (hy : GGTwoPlaneThree Q
      (CFSG.ComponentClassification.CatalogueBOrthogonalSemilinear.matrixLinearIso
        (y : GL (Fin d) (GaloisField 2 1))) v₁ v₂) :
    Subgroup.centralizer ({φ y} : Set G) ≤ ggM p B x L D J := by
  subst hp
  haveI : Fact (Nat.Prime 3) := ⟨by norm_num⟩
  haveI : Fintype (GaloisField 2 1) := Fintype.ofFinite _
  haveI : DecidableEq (GaloisField 2 1) := Classical.decEq _
  have hfield01 : ∀ a : GaloisField 2 1, a = 0 ∨ a = 1 := by
    have hcardK : Fintype.card (GaloisField 2 1) = 2 := by
      rw [← Nat.card_eq_fintype_card, GaloisField.card 2 1 (by norm_num), pow_one]
    intro a
    have h : ({0, 1} : Finset (GaloisField 2 1)) = Finset.univ := by
      apply Finset.eq_univ_of_card
      rw [Finset.card_insert_of_notMem (by simp), Finset.card_singleton, hcardK]
    have ha : a ∈ ({0, 1} : Finset (GaloisField 2 1)) := by
      rw [h]; exact Finset.mem_univ a
    simpa using ha
  have hA := genMax_of_orth hnd hT (by norm_num) (by norm_num) hBs.2.1 hBs.2.2.2 φ hφ hBφ
  obtain ⟨r, ⟨F⟩⟩ := exists_frame_of_genMax hA
  set A := ((Bs.comap φ).map (matrixDerived Q).subtype).map
    (matrixLinearIso (d := d) (K := GaloisField 2 1)).toMonoidHom with hAdef
  set Ω := orthDerived Q with hΩ
  set φV : ↥Ω →* G := φ.comp (matrixDerivedEquiv Q).symm.toMonoidHom with hφVdef
  have hφV : Function.Injective φV := hφ.comp (matrixDerivedEquiv Q).symm.injective
  have hφVr : φV.range = φ.range := by
    ext g
    constructor
    · rintro ⟨y, rfl⟩
      exact ⟨_, rfl⟩
    · rintro ⟨X, rfl⟩
      exact ⟨matrixDerivedEquiv Q X, by simp [hφVdef]⟩
  have : Finite ((Fin d → GaloisField 2 1) ≃ₗ[GaloisField 2 1]
      (Fin d → GaloisField 2 1)) := finite_linearEquiv
  have hAB : ∀ g : ↥Ω, ((g : ↥Ω) : (Fin d → GaloisField 2 1) ≃ₗ[GaloisField 2 1]
      (Fin d → GaloisField 2 1)) ∈ A ↔ φV g ∈ Bs := by
    intro g
    constructor
    · rintro ⟨_, ⟨Y, hY, rfl⟩, hYg⟩
      have hYg' : (matrixDerivedEquiv Q).symm g = Y := by
        apply (matrixDerivedEquiv Q).injective
        rw [MulEquiv.apply_symm_apply]
        exact Subtype.ext hYg.symm
      show φ ((matrixDerivedEquiv Q).symm g) ∈ Bs
      rw [hYg']
      exact hY
    · intro hg
      exact ⟨((matrixDerivedEquiv Q).symm g).1, ⟨(matrixDerivedEquiv Q).symm g, hg, rfl⟩, by
        have h1 := coe_matrixDerivedEquiv Q ((matrixDerivedEquiv Q).symm g)
        rw [MulEquiv.apply_symm_apply] at h1
        exact h1.symm⟩
  have hAΩ : A ≤ Ω := by
    rintro _ ⟨_, ⟨Y, -, rfl⟩, rfl⟩
    have h1 := (matrixDerivedEquiv Q Y).2
    rwa [coe_matrixDerivedEquiv] at h1
  have hBφV : Bs ≤ φV.range := hφVr ▸ hBφ
  have hmax : ∀ g ∈ Ω, g ^ 3 = 1 → (∀ c ∈ A, g * c = c * g) → g ∈ A := by
    intro g hg hgp hgc
    refine (hAB ⟨g, hg⟩).mpr (hBs.2.2.2 _ (Subgroup.mem_centralizer_iff.mpr fun y hy => ?_) ?_)
    · obtain ⟨c, rfl⟩ := hBφV hy
      have h1 := hgc c ((hAB c).mpr hy)
      rw [← map_mul, ← map_mul]
      exact congrArg φV (Subtype.ext h1.symm)
    · rw [← map_pow]
      have h1 : (⟨g, hg⟩ : ↥Ω) ^ 3 = 1 := Subtype.ext (by simpa using hgp)
      rw [h1, map_one]
  have hr : 4 ≤ r := by
    have hcA : Nat.card A = 3 ^ r := by
      rw [← F.range, Nat.card_congr (MonoidHom.ofInjective F.inj).toEquiv.symm,
        Nat.card_congr Multiplicative.toAdd, Nat.card_fun, Nat.card_zmod, Nat.card_eq_fintype_card,
        Fintype.card_fin]
    have hle : Nat.card Bs ≤ Nat.card A := by
      have hex : ∀ y : Bs, ∃ g : ↥Ω, φV g = y := fun y => hBφV y.2
      choose σ hσ using hex
      refine Nat.card_le_card_of_injective (fun y => ⟨σ y, (hAB _).mpr (by rw [hσ]; exact y.2)⟩)
        fun y y' hyy => ?_
      have h0 := congrArg (fun z : A => (z : (Fin d → GaloisField 2 1) ≃ₗ[GaloisField 2 1]
        (Fin d → GaloisField 2 1))) hyy
      have h1 : σ y = σ y' := Subtype.ext h0
      exact Subtype.ext (by rw [← hσ y, ← hσ y', h1])
    exact (Nat.pow_le_pow_iff_right (by norm_num : 1 < 3)).mp (hcard.trans (hle.trans hcA.le))
  have hcardU : ∀ k : Fin r, Nat.card (F.U k) = 2 ^ finrank (GaloisField 2 1) (F.U k) := by
    intro k
    rw [Module.natCard_eq_pow_finrank (K := GaloisField 2 1) (V := F.U k),
      GaloisField.card 2 1 (by norm_num), pow_one]
  have hEven : ∀ k : Fin r, Even (finrank (GaloisField 2 1) (F.U k)) := by
    intro k
    exact OrthYFusion.even_of_three_dvd_two_pow_sub_one
      (by rw [← hcardU k]; exact F.dvd_card_sub_one k)
  have hcases : ∀ k : Fin r, finrank (GaloisField 2 1) (F.U k) = 2 ∨
      4 ≤ finrank (GaloisField 2 1) (F.U k) := by
    intro k
    have h2 := F.two_le_finrank k
    obtain ⟨m, hm⟩ := hEven k
    omega
  have hdle : d ≤ 12 := by rcases hd with rfl | rfl <;> norm_num
  have hdimV : finrank (GaloisField 2 1) (Fin d → GaloisField 2 1) = d :=
    Module.finrank_fin_fun (R := GaloisField 2 1) (n := d)
  let i0 : Fin r := ⟨0, by omega⟩
  let i1 : Fin r := ⟨1, by omega⟩
  let i2 : Fin r := ⟨2, by omega⟩
  let i3 : Fin r := ⟨3, by omega⟩
  have h01 : i0 ≠ i1 := by
    intro h
    have hv : (i0 : Fin r).val = (i1 : Fin r).val := Fin.ext_iff.mp h
    simp only [i0, i1] at hv
    omega
  have h02 : i0 ≠ i2 := by
    intro h
    have hv : (i0 : Fin r).val = (i2 : Fin r).val := Fin.ext_iff.mp h
    simp only [i0, i2] at hv
    omega
  have h03 : i0 ≠ i3 := by
    intro h
    have hv : (i0 : Fin r).val = (i3 : Fin r).val := Fin.ext_iff.mp h
    simp only [i0, i3] at hv
    omega
  have h12 : i1 ≠ i2 := by
    intro h
    have hv : (i1 : Fin r).val = (i2 : Fin r).val := Fin.ext_iff.mp h
    simp only [i1, i2] at hv
    omega
  have h13 : i1 ≠ i3 := by
    intro h
    have hv : (i1 : Fin r).val = (i3 : Fin r).val := Fin.ext_iff.mp h
    simp only [i1, i3] at hv
    omega
  have h23 : i2 ≠ i3 := by
    intro h
    have hv : (i2 : Fin r).val = (i3 : Fin r).val := Fin.ext_iff.mp h
    simp only [i2, i3] at hv
    omega
  have htwo : ∃ j j' : Fin r, j ≠ j' ∧ finrank (GaloisField 2 1) (F.U j) = 2 ∧
      finrank (GaloisField 2 1) (F.U j') = 2 := by
    by_contra hcon
    push Not at hcon
    rcases hcases i0 with h0 | h0 <;> rcases hcases i1 with h1 | h1 <;>
      rcases hcases i2 with h2 | h2 <;> rcases hcases i3 with h3 | h3
    · exact hcon i0 i1 h01 h0 h1
    · exact hcon i0 i1 h01 h0 h1
    · exact hcon i0 i1 h01 h0 h1
    · exact hcon i0 i1 h01 h0 h1
    · exact hcon i0 i2 h02 h0 h2
    · exact hcon i0 i2 h02 h0 h2
    · exact hcon i0 i3 h03 h0 h3
    · exfalso
      have h4 := OrthYFusion.frame_finrank_four_le F h01 h02 h03 h12 h13 h23
        (le_top : F.U i0 ≤ ⊤) (le_top : F.U i1 ≤ ⊤) (le_top : F.U i2 ≤ ⊤)
        (le_top : F.U i3 ≤ ⊤)
      have htop : finrank (GaloisField 2 1) (⊤ : Submodule (GaloisField 2 1)
          (Fin d → GaloisField 2 1)) = d := by rw [finrank_top, hdimV]
      have h2a := F.two_le_finrank i0
      have h2b := F.two_le_finrank i1
      have h2c := F.two_le_finrank i2
      have h2d := F.two_le_finrank i3
      omega
    · exact hcon i1 i2 h12 h1 h2
    · exact hcon i1 i2 h12 h1 h2
    · exact hcon i1 i3 h13 h1 h3
    · exfalso
      have h4 := OrthYFusion.frame_finrank_four_le F h01 h02 h03 h12 h13 h23
        (le_top : F.U i0 ≤ ⊤) (le_top : F.U i1 ≤ ⊤) (le_top : F.U i2 ≤ ⊤)
        (le_top : F.U i3 ≤ ⊤)
      have htop : finrank (GaloisField 2 1) (⊤ : Submodule (GaloisField 2 1)
          (Fin d → GaloisField 2 1)) = d := by rw [finrank_top, hdimV]
      have h2a := F.two_le_finrank i0
      have h2b := F.two_le_finrank i1
      have h2c := F.two_le_finrank i2
      have h2d := F.two_le_finrank i3
      omega
    · exact hcon i2 i3 h23 h2 h3
    · exfalso
      have h4 := OrthYFusion.frame_finrank_four_le F h01 h02 h03 h12 h13 h23
        (le_top : F.U i0 ≤ ⊤) (le_top : F.U i1 ≤ ⊤) (le_top : F.U i2 ≤ ⊤)
        (le_top : F.U i3 ≤ ⊤)
      have htop : finrank (GaloisField 2 1) (⊤ : Submodule (GaloisField 2 1)
          (Fin d → GaloisField 2 1)) = d := by rw [finrank_top, hdimV]
      have h2a := F.two_le_finrank i0
      have h2b := F.two_le_finrank i1
      have h2c := F.two_le_finrank i2
      have h2d := F.two_le_finrank i3
      omega
    · exfalso
      have h4 := OrthYFusion.frame_finrank_four_le F h01 h02 h03 h12 h13 h23
        (le_top : F.U i0 ≤ ⊤) (le_top : F.U i1 ≤ ⊤) (le_top : F.U i2 ≤ ⊤)
        (le_top : F.U i3 ≤ ⊤)
      have htop : finrank (GaloisField 2 1) (⊤ : Submodule (GaloisField 2 1)
          (Fin d → GaloisField 2 1)) = d := by rw [finrank_top, hdimV]
      have h2a := F.two_le_finrank i0
      have h2b := F.two_le_finrank i1
      have h2c := F.two_le_finrank i2
      have h2d := F.two_le_finrank i3
      omega
    · exfalso
      have h4 := OrthYFusion.frame_finrank_four_le F h01 h02 h03 h12 h13 h23
        (le_top : F.U i0 ≤ ⊤) (le_top : F.U i1 ≤ ⊤) (le_top : F.U i2 ≤ ⊤)
        (le_top : F.U i3 ≤ ⊤)
      have htop : finrank (GaloisField 2 1) (⊤ : Submodule (GaloisField 2 1)
          (Fin d → GaloisField 2 1)) = d := by rw [finrank_top, hdimV]
      have h2a := F.two_le_finrank i0
      have h2b := F.two_le_finrank i1
      have h2c := F.two_le_finrank i2
      have h2d := F.two_le_finrank i3
      omega

  obtain ⟨j, j', hjj, hj2, hj'2⟩ := htwo
  let s : Multiplicative (Fin r → ZMod 3) := ofAdd (Pi.single j 1 + Pi.single j' 1)
  have hsj : toAdd s j = 1 := by simp [s, Pi.add_apply, hjj]
  have hsj' : toAdd s j' = 1 := by simp [s, Pi.add_apply, Ne.symm hjj]
  have hsi : ∀ i, i ≠ j → i ≠ j' → toAdd s i = 0 := by
    intro i hij hij'
    simp [s, Pi.add_apply, hij, hij']
  have hsupp : ∀ i, toAdd s i ≠ 0 → i = j ∨ i = j' := by
    intro i hi
    by_contra hcon
    push Not at hcon
    exact hi (hsi i hcon.1 hcon.2)
  let bV : (Fin d → GaloisField 2 1) ≃ₗ[GaloisField 2 1] (Fin d → GaloisField 2 1) :=
    F.ι s
  have hbVA : bV ∈ A := F.mem s
  have hbVΩ : bV ∈ Ω := hAΩ hbVA
  have hbVO : bV ∈ TauCeti.QuadraticMap.orthogonalGroup Q := orthDerived_le_orthogonalGroup hbVΩ
  have pair_span_orth_right : ∀ (w v : Fin d → GaloisField 2 1), polar Q w v = 0 →
      polar Q (bV w) v = 0 →
      ∀ x ∈ Submodule.span (GaloisField 2 1) ({w, bV w} : Set (Fin d → GaloisField 2 1)),
        polar Q x v = 0 := by
    intro w v h1 h2 x hx
    induction hx using Submodule.span_induction with
    | mem x hx =>
      rcases hx with rfl | rfl
      · exact h1
      · exact h2
    | zero => simp
    | add x y _ _ hx hy => rw [QuadraticMap.polar_add_left, hx, hy, add_zero]
    | smul a x _ hx => rw [QuadraticMap.polar_smul_left, hx, smul_zero]
  have plane : ∀ (k : Fin r) (w : Fin d → GaloisField 2 1),
      finrank (GaloisField 2 1) (F.U k) = 2 → w ∈ F.U k → w ≠ 0 → toAdd s k ≠ 0 →
      Q w = 1 ∧ polar Q w (bV w) = 1 ∧ bV (bV w) = bV w + w ∧ bV w ≠ w ∧
        Submodule.span (GaloisField 2 1) ({w, bV w} : Set (Fin d → GaloisField 2 1)) = F.U k := by
    intro k w hk2 hw hw0 hsk
    have hbVw_mem : bV w ∈ F.U k := F.mapsTo s k w hw
    have hbVw_ne : bV w ≠ w := fun h => hw0 (F.fpf s k hsk w hw h)
    have hpow3 : bV (bV (bV w)) = w := by
      have h := congrArg (fun e : (Fin d → GaloisField 2 1) ≃ₗ[GaloisField 2 1]
          (Fin d → GaloisField 2 1) => e w)
        (F.pow_p s)
      have h3 : bV ^ 3 = bV * bV * bV := by rw [pow_succ, pow_succ, pow_one]
      rw [h3, LinearEquiv.mul_apply, LinearEquiv.mul_apply] at h
      simpa using h
    have hz_mem : bV (bV w) + bV w + w ∈ F.U k :=
      (F.U k).add_mem ((F.U k).add_mem (F.mapsTo s k _ hbVw_mem) hbVw_mem) hw
    have hz_fix : bV (bV (bV w) + bV w + w) = bV (bV w) + bV w + w := by
      simp only [map_add]
      rw [hpow3]
      abel
    have hz0 : bV (bV w) + bV w + w = 0 := F.fpf s k hsk _ hz_mem hz_fix
    have hz0' : bV (bV w) + (bV w + w) = 0 := by
      rw [add_assoc] at hz0
      exact hz0
    have hbV2 : bV (bV w) = bV w + w := by
      have hneg : -(bV w + w) = bV (bV w) := neg_eq_of_add_eq_zero_left hz0'
      have hneg' : -(bV w + w) = bV w + w := by
        funext i
        exact CharTwo.neg_eq ((bV w + w) i)
      calc bV (bV w) = -(bV w + w) := hneg.symm
        _ = bV w + w := hneg'
    have hQbV : Q (bV w) = Q w := TauCeti.QuadraticMap.map_app_of_mem_orthogonalGroup hbVO w
    have hQ2 : Q (bV (bV w)) = Q w := by
      rw [TauCeti.QuadraticMap.map_app_of_mem_orthogonalGroup hbVO (bV w), hQbV]
    have hQsum : Q (bV w + w) = Q (bV w) + Q w + polar Q (bV w) w :=
      QuadraticMap.map_add (Q : (Fin d → GaloisField 2 1) → GaloisField 2 1) (bV w) w
    rw [hbV2, hQsum, hQbV] at hQ2
    have hcancel : Q w + Q w = 0 := CharTwo.add_self_eq_zero (Q w)
    rw [hcancel, zero_add] at hQ2
    have hB : polar Q (bV w) w = Q w := hQ2
    have hli : LinearIndependent (GaloisField 2 1) ![w, bV w] := by
      rw [LinearIndependent.pair_iff]
      intro a c h
      rcases hfield01 a with rfl | rfl <;> rcases hfield01 c with rfl | rfl <;> simp at h ⊢
      · have h2 : bV w = 0 := by simpa using h
        exact hw0 (bV.injective (by rw [h2]; simp))
      · exact hw0 h
      · exfalso
        apply hbVw_ne
        have h2 : w + bV w = 0 := by simpa using h
        have h3 : -(bV w) = w := neg_eq_of_add_eq_zero_left h2
        calc bV w = -(bV w) := by
              funext i
              exact (CharTwo.neg_eq (bV w i)).symm
          _ = w := h3
    have hspan : Submodule.span (GaloisField 2 1) ({w, bV w} : Set (Fin d → GaloisField 2 1)) =
        F.U k := by
      have hle : Submodule.span (GaloisField 2 1) ({w, bV w} : Set (Fin d → GaloisField 2 1)) ≤
          F.U k := by
        refine Submodule.span_le.mpr ?_
        intro x hx
        rcases hx with rfl | rfl
        · exact hw
        · exact hbVw_mem
      have hfin : finrank (GaloisField 2 1)
          (Submodule.span (GaloisField 2 1) ({w, bV w} : Set (Fin d → GaloisField 2 1))) = 2 := by
        have hrange : Set.range ![w, bV w] = ({w, bV w} : Set (Fin d → GaloisField 2 1)) := by
          ext z
          constructor
          · rintro ⟨i, rfl⟩
            fin_cases i <;> simp
          · intro hz
            rcases hz with rfl | rfl
            · exact ⟨0, rfl⟩
            · exact ⟨1, rfl⟩
        have h : finrank (GaloisField 2 1)
            (Submodule.span (GaloisField 2 1) (Set.range ![w, bV w])) = 2 := by
          rw [finrank_span_eq_card hli]
          simp
        rwa [hrange] at h
      exact Submodule.eq_of_le_of_finrank_eq hle (hfin.trans hk2.symm)
    have hQw0 : Q w ≠ 0 := by
      intro hQw
      have hB0 : polar Q (bV w) w = 0 := by rw [hB, hQw]
      apply hw0
      refine F.nondeg k w hw fun v hv => ?_
      exact pair_span_orth_right w w
        (CFSG.RankThree.OrthogonalInvolutions.polar_self_eq_zero Q w) hB0 v
        (by rwa [← hspan] at hv)
    have hQw1 : Q w = 1 := by
      rcases hfield01 (Q w) with h | h
      · exact absurd h hQw0
      · exact h
    refine ⟨hQw1, ?_, hbV2, hbVw_ne, hspan⟩
    rw [QuadraticMap.polar_comm, hB, hQw1]
  obtain ⟨w₁, hw₁U, hw₁0⟩ := (Submodule.ne_bot_iff (F.U j)).mp (F.ne_bot j)
  obtain ⟨w₂, hw₂U, hw₂0⟩ := (Submodule.ne_bot_iff (F.U j')).mp (F.ne_bot j')
  obtain ⟨hQw₁, hpol₁, hsq₁, hne₁, hspan₁⟩ :=
    plane j w₁ hj2 hw₁U hw₁0 (by rw [hsj]; norm_num)
  obtain ⟨hQw₂, hpol₂, hsq₂, hne₂, hspan₂⟩ :=
    plane j' w₂ hj'2 hw₂U hw₂0 (by rw [hsj']; norm_num)
  have hQbVw₁ : Q (bV w₁) = 1 := by
    rw [TauCeti.QuadraticMap.map_app_of_mem_orthogonalGroup hbVO w₁, hQw₁]
  have hQbVw₂ : Q (bV w₂) = 1 := by
    rw [TauCeti.QuadraticMap.map_app_of_mem_orthogonalGroup hbVO w₂, hQw₂]
  have hbVw₁mem : bV w₁ ∈ F.U j := F.mapsTo s j w₁ hw₁U
  have hbVw₂mem : bV w₂ ∈ F.U j' := F.mapsTo s j' w₂ hw₂U
  have hcross₁ : polar Q w₁ w₂ = 0 := F.orth j j' hjj w₁ hw₁U w₂ hw₂U
  have hcross₂ : polar Q w₁ (bV w₂) = 0 := F.orth j j' hjj w₁ hw₁U (bV w₂) hbVw₂mem
  have hcross₃ : polar Q (bV w₁) w₂ = 0 := by
    rw [QuadraticMap.polar_comm]
    exact F.orth j' j (Ne.symm hjj) w₂ hw₂U (bV w₁) hbVw₁mem
  have hcross₄ : polar Q (bV w₁) (bV w₂) = 0 :=
    F.orth j j' hjj (bV w₁) hbVw₁mem (bV w₂) hbVw₂mem
  have hfix : ∀ v, polar Q w₁ v = 0 → polar Q (bV w₁) v = 0 → polar Q w₂ v = 0 →
      polar Q (bV w₂) v = 0 → bV v = v := by
    intro v h1 h2 h3 h4
    refine (F.fix s v).mpr fun k hk u hu => ?_
    rcases hsupp k hk with rfl | rfl
    · exact pair_span_orth_right w₁ v h1 h2 u (by rwa [← hspan₁] at hu)
    · exact pair_span_orth_right w₂ v h3 h4 u (by rwa [← hspan₂] at hu)
  have htwoPlane : GGTwoPlaneThree Q bV w₁ w₂ :=
    ⟨hQw₁, hQbVw₁, hQw₂, hQbVw₂, hpol₁, hpol₂, hcross₁, hcross₂, hcross₃, hcross₄,
      hsq₁, hsq₂, hfix⟩

  have hfixspace : fixedSpace bV = (F.U j ⊔ F.U j').orthogonalBilin (polarBilin Q) := by
    ext v
    rw [mem_fixedSpace, F.fix s v]
    constructor
    · intro h
      rw [Submodule.mem_orthogonalBilin]
      intro u hu
      rw [Submodule.mem_sup] at hu
      obtain ⟨x, hx, y, hy, rfl⟩ := hu
      rw [map_add, LinearMap.add_apply,
        show (polarBilin Q x) v = 0 by
          rw [QuadraticMap.polarBilin_apply_apply]; exact h j (by rw [hsj]; norm_num) x hx,
        show (polarBilin Q y) v = 0 by
          rw [QuadraticMap.polarBilin_apply_apply]; exact h j' (by rw [hsj']; norm_num) y hy,
        add_zero]
    · intro h k hk u hu
      rw [Submodule.mem_orthogonalBilin] at h
      rcases hsupp k hk with rfl | rfl
      · exact h u (Submodule.mem_sup_left hu)
      · exact h u (Submodule.mem_sup_right hu)
  have hfinrank_sup : finrank (GaloisField 2 1) ↥(F.U j ⊔ F.U j') = 4 := by
    have h := Submodule.finrank_sup_add_finrank_inf_eq (F.U j) (F.U j')
    rw [F.inf_eq_bot hjj, finrank_bot, add_zero, hj2, hj'2] at h
    omega
  have hdim_fix : finrank (GaloisField 2 1) (fixedSpace bV) = d - 4 := by
    rw [hfixspace]
    change finrank (GaloisField 2 1) ↥(LinearMap.BilinForm.orthogonal (polarBilin Q)
      (F.U j ⊔ F.U j')) = d - 4
    rw [LinearMap.BilinForm.finrank_orthogonal hnd, hdimV, hfinrank_sup]
  have h3fix : 3 ≤ finrank (GaloisField 2 1) (fixedSpace bV) := by
    rw [hdim_fix]
    rcases hd with rfl | rfl <;> norm_num
  have hns : ¬ CFSG.StandardType.OmNonsplit.SplitFour (Q.comp (fixedSpace bV).subtype) := by
    intro hsp
    have h4 : finrank (GaloisField 2 1) (fixedSpace bV) = 4 := hsp.1
    rw [hdim_fix] at h4
    rcases hd with rfl | rfl <;> norm_num at h4
  obtain ⟨L₂, hL₂, hcard₂⟩ := direct_of_supp hnd (by norm_num : Nat.Prime 3) (by norm_num)
    hAΩ F (s := s) (j := j) (j' := j') hsupp h3fix hns
  change IsComponentOf L₂ (orthDerived Q ⊓ Subgroup.centralizer {bV}) at hL₂
  have hbV1 : bV ≠ 1 := fun h => hne₁ (by rw [h]; rfl)
  let b : G := φV ⟨bV, hbVΩ⟩
  have hbB : b ∈ Bs := (hAB ⟨bV, hbVΩ⟩).mp hbVA
  have hb1 : b ≠ 1 := by
    intro h
    have h1 : (⟨bV, hbVΩ⟩ : ↥Ω) = 1 := hφV (h.trans (map_one φV).symm)
    exact hbV1 (congrArg Subtype.val h1)
  have hL₂' : IsComponentOf L₂ (Ω ⊓ Subgroup.centralizer {bV}) := by
    rwa [hΩ]
  obtain ⟨hL₁, hmapL⟩ := isComponentOf_transport' hφV ⟨bV, hbVΩ⟩ hL₂'
  have hφVrange : φV.range = ggG0 3 B x L D J := hφVr.trans hrange
  rw [hφVrange] at hL₁
  change IsComponentOf ((L₂.comap Ω.subtype).map φV) (ggG0 3 B x L D J ⊓
    Subgroup.centralizer {b}) at hL₁
  have hcard₁ : Nat.card (Bs ⊓ Subgroup.centralizer
      ((((L₂.comap Ω.subtype).map φV : Subgroup G)) : Set G) : Subgroup G) ≤ 3 ^ 2 := by
    have h1 := card_inf_centralizer_le (L₂ := L₂) hφV hBφV hAB
      (by rw [hΩ]; exact hL₂.1.trans inf_le_left)
    exact h1.trans hcard₂
  have hfus : GGControlsStrongFusion (ggM 3 B x L D J) (Subgroup.zpowers b) :=
    (s2 b hbB hb1 ((L₂.comap Ω.subtype).map φV) hL₁ hcard₁).2
  have hCb : Subgroup.centralizer ({b} : Set G) ≤ ggM 3 B x L D J :=
    hfus.centralizer_le (Subgroup.mem_zpowers b) hb1
  have hdim : 5 ≤ finrank (GaloisField 2 1) (Fin d → GaloisField 2 1) := by
    rw [hdimV]
    rcases hd with rfl | rfl <;> norm_num
  obtain ⟨g, hgΩ, hgy⟩ :=
    GGTwoPlaneThree.exists_orthDerived_conj (Q := Q) hnd hT hdim hbVO hy htwoPlane
  let h₀ : CFSG.ComponentClassification.CatalogueBOrthogonalSemilinear.matrixDerived Q :=
    (matrixDerivedEquiv Q).symm ⟨g, hgΩ⟩
  have hlin₀ : matrixLinearIso (h₀ : GL (Fin d) (GaloisField 2 1)) = g := by
    have h := coe_matrixDerivedEquiv Q h₀
    change ((matrixDerivedEquiv Q h₀ : ↥Ω) : (Fin d → GaloisField 2 1) ≃ₗ[GaloisField 2 1]
      (Fin d → GaloisField 2 1)) = matrixLinearIso (h₀ : GL (Fin d) (GaloisField 2 1)) at h
    rw [MulEquiv.apply_symm_apply] at h
    exact h.symm
  have hmodel : matrixLinearIso ((h₀ * y * h₀⁻¹ :
      CFSG.ComponentClassification.CatalogueBOrthogonalSemilinear.matrixDerived Q) :
      GL (Fin d) (GaloisField 2 1)) = bV := by
    change matrixLinearIso ((h₀ : GL (Fin d) (GaloisField 2 1)) *
      (y : GL (Fin d) (GaloisField 2 1)) * ((h₀ : GL (Fin d) (GaloisField 2 1)))⁻¹) = bV
    rw [map_mul, map_mul, map_inv, hlin₀, hgy, mul_assoc, mul_inv_cancel, mul_one]
  have hRHS : matrixLinearIso (((matrixDerivedEquiv Q).symm ⟨bV, hbVΩ⟩ :
      CFSG.ComponentClassification.CatalogueBOrthogonalSemilinear.matrixDerived Q) :
      GL (Fin d) (GaloisField 2 1)) = bV := by
    have h := coe_matrixDerivedEquiv Q ((matrixDerivedEquiv Q).symm ⟨bV, hbVΩ⟩)
    change ((matrixDerivedEquiv Q ((matrixDerivedEquiv Q).symm ⟨bV, hbVΩ⟩) : ↥Ω) :
      (Fin d → GaloisField 2 1) ≃ₗ[GaloisField 2 1] (Fin d → GaloisField 2 1)) =
      matrixLinearIso (((matrixDerivedEquiv Q).symm ⟨bV, hbVΩ⟩ :
        CFSG.ComponentClassification.CatalogueBOrthogonalSemilinear.matrixDerived Q) :
        GL (Fin d) (GaloisField 2 1)) at h
    rw [MulEquiv.apply_symm_apply] at h
    exact h.symm
  have heq : (h₀ * y * h₀⁻¹ :
      CFSG.ComponentClassification.CatalogueBOrthogonalSemilinear.matrixDerived Q) =
      (matrixDerivedEquiv Q).symm ⟨bV, hbVΩ⟩ := by
    apply Subtype.ext
    exact matrixLinearIso.injective (by rw [hmodel, hRHS])
  have hφeq : φ (h₀ * y * h₀⁻¹) = b := by
    change φ (h₀ * y * h₀⁻¹) = φV ⟨bV, hbVΩ⟩
    rw [heq]
    rfl
  have hh₀M : φ h₀ ∈ ggM 3 B x L D J := by
    have h : φ h₀ ∈ φ.range := ⟨h₀, rfl⟩
    rw [hrange] at h
    exact Subgroup.le_normalizer h
  have hfinal := centralizer_conj_le hCb (Subgroup.inv_mem _ hh₀M)
  have heqel : (φ h₀)⁻¹ * b * (φ h₀) = φ y := by
    rw [← hφeq, ← map_inv, ← map_mul, ← map_mul]
    congr 1
    group
  rw [show ((φ h₀)⁻¹)⁻¹ = φ h₀ from inv_inv _] at hfinal
  rwa [heqel] at hfinal

end CFSG.StandardType
