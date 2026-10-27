module

public import CFSG.LocalAnalysis.StandardType.FS81.N6AllMat

public section

namespace CFSG.StandardType.FrameRoute.FS81

open CFSG.Open CFSG.Assembly
open scoped Matrix

theorem not_evenAll0_six_of_std : ∀ (G : Type) [Group G] [Finite G] (b₀ : G) (K E : Subgroup G),
    StdAssumptions b₀ K E Row.D6 → ∀ B : Basis3 G (Row.D6.n + 1), Adapted B b₀ K E →
      LocalOrthII B b₀ → Fus42 B b₀ → OddCoreTrivial E →
        B.realized (Subgroup.normalizer (Subgroup.zpowers b₀ : Set G)) = evenAll0 Row.D6.n →
          False := by
  intro G _ _ b₀ K E hstd B hB _ hfus hodd hN0
  classical
  obtain ⟨hspan, hb0, -⟩ := hB
  subst hspan
  obtain ⟨-, ⟨-, -, -, -, -, hcard⟩, -⟩ := hstd
  obtain ⟨Xg, hXg⟩ : ∃ Xg : Subgroup (GL (Fin (Row.D6.n + 1)) (ZMod 3)),
      Xg = (ggAutomizer ⊤ B.span).map B.glHom := ⟨_, rfl⟩
  have h1 : ∀ A ∈ Xg, (∀ i : Fin (Row.D6.n + 1), i ≠ 0 →
      (A : Matrix (Fin (Row.D6.n + 1)) (Fin (Row.D6.n + 1)) (ZMod 3)) i 0 = 0) →
      (A : Matrix (Fin (Row.D6.n + 1)) (Fin (Row.D6.n + 1)) (ZMod 3)) ∈ evenAll0 Row.D6.n := by
    intro A hA hcol
    rw [hXg] at hA
    obtain ⟨φ, g, hgN, hg, rfl⟩ := B.exists_of_mem_xg hA
    have hc : B.matOf φ *ᵥ Pi.single 0 1 = B.matOf φ 0 0 • Pi.single 0 1 := by
      funext i
      rw [Matrix.mulVec_single_one, Matrix.col_apply, Pi.smul_apply, smul_eq_mul]
      by_cases hi : i = 0
      · subst hi
        simp
      · rw [show B.matOf φ i 0 = 0 from hcol i hi, Pi.single_eq_of_ne hi, mul_zero]
    have himg := B.conj_b_of_mulVec_single hg hc
    rw [hb0] at himg
    have hgb : g ∈ Subgroup.normalizer (Subgroup.zpowers b₀ : Set G) := by
      refine Basis3.mem_normalizer_zpowers_of_conj ?_
      rw [himg]
      exact Subgroup.pow_mem _ (Subgroup.mem_zpowers b₀) _
    rw [← hN0]
    exact (B.mem_realized_iff _ _).mpr ⟨φ, ⟨g, hgb, hgN, hg⟩, rfl⟩
  have h2 : ∀ M ∈ evenAll0 Row.D6.n, ∃ A ∈ Xg,
      (A : Matrix (Fin (Row.D6.n + 1)) (Fin (Row.D6.n + 1)) (ZMod 3)) = M := by
    intro M hM
    rw [hXg]
    rw [← hN0] at hM
    exact B.exists_xg_of_realized _ hM
  have h3 : ∀ N : Subgroup ↥Xg, N.Normal → Odd (Nat.card N) → N = ⊥ := by
    subst hXg
    intro N hNn hNodd
    set e := (ggAutomizer ⊤ B.span).equivMapOfInjective B.glHom B.glHom_injective with he
    have hinj : Function.Injective e.symm.toMonoidHom := e.symm.injective
    have h := hodd (N.map e.symm.toMonoidHom) (hNn.map _ e.symm.surjective)
      (by rwa [Subgroup.card_map_of_injective hinj])
    exact (Subgroup.map_eq_bot_iff_of_injective _ hinj).mp h
  have h4 : ∃ A ∈ Xg, ∃ i : Fin (Row.D6.n + 1), i ≠ 0 ∧
      (A : Matrix (Fin (Row.D6.n + 1)) (Fin (Row.D6.n + 1)) (ZMod 3)) i 0 ≠ 0 := by
    obtain ⟨x, hx, i, hi, hxi⟩ := B.exists_xg_moves_e0 hb0 hfus
    refine ⟨x, hXg ▸ hx, i, hi, ?_⟩
    rwa [Matrix.mulVec_single_one, Matrix.col_apply] at hxi
  have h5 : 2 ^ 7 * Nat.factorial 7 < Nat.card ↥Xg := by
    rw [hXg, Subgroup.card_map_of_injective B.glHom_injective]
    exact hcard
  exact false_of_evenAll0_six Xg h1 h2 h3 h4 h5

end CFSG.StandardType.FrameRoute.FS81

end
