module

public import CFSG.LocalAnalysis.StandardType.FS81.TwD5Split
public import CFSG.LocalAnalysis.StandardType.FS81.EvenN0Mat
public import CFSG.LocalAnalysis.StandardType.FS81.OddCoreTransvOrth

public section

namespace CFSG.StandardType.FrameRoute.FS81

open CFSG.Open CFSG.Assembly
open scoped Matrix

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

structure StabMatHyp (n : ℕ) (H : Set (Matrix (Fin (n + 1)) (Fin (n + 1)) (ZMod 3)))
    (Xg : Subgroup (GL (Fin (n + 1)) (ZMod 3))) : Prop where
  norm : ∀ A ∈ Xg, (∀ i : Fin (n + 1), i ≠ 0 →
    (A : Matrix (Fin (n + 1)) (Fin (n + 1)) (ZMod 3)) i 0 = 0) →
    (A : Matrix (Fin (n + 1)) (Fin (n + 1)) (ZMod 3)) ∈ H
  sub : ∀ M ∈ H, ∃ A ∈ Xg, (A : Matrix (Fin (n + 1)) (Fin (n + 1)) (ZMod 3)) = M
  odd : ∀ N : Subgroup ↥Xg, N.Normal → Odd (Nat.card N) → N = ⊥
  moves : ∃ A ∈ Xg, ∃ i : Fin (n + 1), i ≠ 0 ∧
    (A : Matrix (Fin (n + 1)) (Fin (n + 1)) (ZMod 3)) i 0 ≠ 0

theorem Basis3.stabMatHyp_xg {G : Type} [Group G] [Finite G] {n : ℕ} (B : Basis3 G (n + 1))
    {b₀ : G} (hb0 : B.b 0 = b₀) {H : Set (Matrix (Fin (n + 1)) (Fin (n + 1)) (ZMod 3))}
    (hN : B.realized (Subgroup.normalizer (Subgroup.zpowers b₀ : Set G)) = H)
    (hodd : OddCoreTrivial B.span) (hfus : Fus42 B b₀) :
    StabMatHyp n H ((ggAutomizer ⊤ B.span).map B.glHom) where
  norm A hA hcol := by
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
      refine mem_normalizer_zpowers_of_conj ?_
      rw [himg]
      exact Subgroup.pow_mem _ (Subgroup.mem_zpowers b₀) _
    rw [← hN]
    exact (B.mem_realized_iff _ _).mpr ⟨φ, ⟨g, hgb, hgN, hg⟩, rfl⟩
  sub M hM := B.exists_xg_of_realized _ (by rw [hN]; exact hM)
  odd N hNn hNodd := by
    set e := (ggAutomizer ⊤ B.span).equivMapOfInjective B.glHom B.glHom_injective with he
    have hinj : Function.Injective e.symm.toMonoidHom := e.symm.injective
    have h := hodd (N.map e.symm.toMonoidHom) (hNn.map _ e.symm.surjective)
      (by rwa [Subgroup.card_map_of_injective hinj])
    exact (Subgroup.map_eq_bot_iff_of_injective _ hinj).mp h
  moves := by
    obtain ⟨x, hx, i, hi, hxi⟩ := B.exists_xg_moves_e0 hb0 hfus
    refine ⟨x, hx, i, hi, ?_⟩
    rwa [Matrix.mulVec_single_one, Matrix.col_apply] at hxi

@[expose] def rE6 (ε : ZMod 3) : Matrix (Fin 6) (Fin 6) (ZMod 3) :=
  1 + Matrix.vecMulVec ![0, 1, 1, 1, 1, ε] ![1, -1, -1, -1, -1, -ε]

@[expose] def wE6 (ε : ZMod 3) : Subgroup (GL (Fin 6) (ZMod 3)) :=
  Subgroup.closure {A | (A : Matrix (Fin 6) (Fin 6) (ZMod 3)) ∈ evenFix0 5 ∨
    (A : Matrix (Fin 6) (Fin 6) (ZMod 3)) = rE6 ε}

@[expose] def oE6 (ε : ZMod 3) : Subgroup (GL (Fin 6) (ZMod 3)) :=
  Subgroup.closure {A | (A : Matrix (Fin 6) (Fin 6) (ZMod 3)) ∈ evenAll0 5 ∨
    (A : Matrix (Fin 6) (Fin 6) (ZMod 3)) = rE6 ε}

@[expose] def T5MatFix : Prop :=
  ∀ Xg : Subgroup (GL (Fin 6) (ZMod 3)), StabMatHyp 5 (evenFix0 5) Xg →
    ∃ ε : ZMod 3, (ε = 1 ∨ ε = -1) ∧ Xg = wE6 ε

@[expose] def T5MatMain : Prop :=
  ∀ Xg : Subgroup (GL (Fin 6) (ZMod 3)), StabMatHyp 5 (evenAll0 5) Xg →
    2 ^ 6 * Nat.factorial 6 < Nat.card Xg → ∃ ε : ZMod 3, (ε = 1 ∨ ε = -1) ∧ Xg = oE6 ε

@[expose] def OE6RecOut : Prop :=
  ∀ ε : ZMod 3, (ε = 1 ∨ ε = -1) →
    (∀ A ∈ oE6 ε, ∀ j : Fin 6, j ≠ 0 → (A : Matrix (Fin 6) (Fin 6) (ZMod 3)) 0 j = 0) ∧
      (∀ A ∈ oE6 ε, ∀ v : Fin 6 → ZMod 3, v 0 = 0 →
        ∑ i, ((A : Matrix (Fin 6) (Fin 6) (ZMod 3)) *ᵥ v) i ^ 2 = ∑ i, v i ^ 2) ∧
      ∀ e : Fin 6 → ZMod 3, e ≠ 0 →
        ((IsOrbitE0 5 (oE6 ε) e ∨ IsOrbitE0 5 (oE6 ε) (-e)) ↔
          ((wt e ≤ 2 ∧ e 0 ≠ 0) ∨ (wt e = 6 ∧ ∏ i, e i = ε)))

@[expose] def T5FixTransfer : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (b₀ : G) (K E : Subgroup G), StdTwD5 b₀ K E →
    ∀ B : Basis3 G (5 + 1), Adapted B b₀ K E → ∀ ε : ZMod 3, (ε = 1 ∨ ε = -1) →
      (ggAutomizer ⊤ B.span).map B.glHom = wE6 ε → False

theorem t5Fix_of_mat (hM : T5MatFix) (hG : T5FixTransfer) : T5Fix := by
  intro G _ _ b₀ K E hstd B hB _ hfus hodd hF
  obtain ⟨ε, hε, hX⟩ := hM _ (B.stabMatHyp_xg hB.2.1 hF (hB.1.symm ▸ hodd) hfus)
  exact hG G b₀ K E hstd B hB ε hε hX

end CFSG.StandardType.FrameRoute.FS81

end
