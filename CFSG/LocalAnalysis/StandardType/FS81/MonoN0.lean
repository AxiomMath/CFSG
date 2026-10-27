module

public import CFSG.LocalAnalysis.StandardType.FS81.MonoN0Hyper
public import CFSG.LocalAnalysis.StandardType.FS81.MonoN0Swap
public import CFSG.LocalAnalysis.StandardType.FS81.MonoN0Count
public import CFSG.LocalAnalysis.StandardType.FS81.N6Fix

public section

namespace CFSG.StandardType.FrameRoute.FS81

open CFSG.Open CFSG.Assembly
open scoped Matrix

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

variable {n : ℕ}

theorem false_of_monoN0Hyp (hn : 4 ≤ n) {Xg : Subgroup (GL (Fin (n + 1)) (ZMod 3))}
    (h : MonoN0Hyp Xg) (hcard : 2 ^ (n + 1) * (n + 1).factorial < Nat.card ↥Xg) : False := by
  by_cases h1 : ∃ p : Fin (n + 1), p ≠ 0 ∧ OrbN Xg (Pi.single p 1)
  · obtain ⟨p, hp, hp1⟩ := h1
    have hFK : ∀ (σ : Equiv.Perm (Fin (n + 1))) (s : Fin (n + 1) → ZMod 3), IsSign s →
        ∃ A ∈ Xg, (A : Matrix (Fin (n + 1)) (Fin (n + 1)) (ZMod 3)) = spMat σ s :=
      fun _ _ hs => h.fk_sub hp (h.exists_swap_mem hn hp hp1) hs
    by_cases h2 : ∃ u, OrbN Xg u ∧ wt u = 2
    · obtain ⟨u, hu, hu2⟩ := h2
      exact h.false_of_orbN_wt_two hn hFK hu hu2
    · have h2' : ∀ v, OrbN Xg v → wt v ≠ 2 := fun v hv hv2 => h2 ⟨v, hv, hv2⟩
      by_cases h3 : ∃ u, OrbN Xg u ∧ wt u = n + 1
      · obtain ⟨u, hu, hu3⟩ := h3
        exact h.false_of_orbN_wt_full hn hFK h2' hu hu3
      · have hwt1 : ∀ v, OrbN Xg v → wt v = 1 := by
          intro v hv
          rcases h.wt_orbN hFK hv with hv1 | hv2 | hv3
          · exact hv1
          · exact absurd hv2 (h2' v hv)
          · exact absurd ⟨v, hv, hv3⟩ h3
        exact absurd hcard (not_lt.mpr (card_le_of_orbN_wt_one hFK hwt1))
  · exact h.false_of_not_orbN_single hn fun p hp hp1 => h1 ⟨p, hp, hp1⟩

namespace Basis3

variable {G : Type} [Group G]

theorem monoN0Hyp_xg [Finite G] (B : Basis3 G (n + 1)) {b₀ : G} (hb0 : B.b 0 = b₀)
    (hN0 : B.realized (Subgroup.normalizer (Subgroup.zpowers b₀ : Set G)) = monoN0 n)
    (hodd : OddCoreTrivial B.span) (hfus : Fus42 B b₀) :
    MonoN0Hyp ((ggAutomizer ⊤ B.span).map B.glHom) where
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
    rw [← hN0]
    exact (B.mem_realized_iff _ _).mpr ⟨φ, ⟨g, hgb, hgN, hg⟩, rfl⟩
  sub M hM := B.exists_xg_of_realized _ (by rw [hN0]; exact hM)
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

end Basis3

theorem false_of_normalizer_mono {G : Type} [Group G] [Finite G] (hn : 4 ≤ n)
    (B : Basis3 G (n + 1)) {b₀ : G} (hb0 : B.b 0 = b₀) (hfus : Fus42 B b₀)
    (hodd : OddCoreTrivial B.span)
    (hcard : 2 ^ (n + 1) * (n + 1).factorial < Nat.card ↥(ggAutomizer ⊤ B.span))
    (hN : B.realized (Subgroup.normalizer (Subgroup.zpowers b₀ : Set G)) = monoFix0 n ∨
      B.realized (Subgroup.normalizer (Subgroup.zpowers b₀ : Set G)) = monoN0 n) : False := by
  rcases hN with hN | hN
  · refine false_of_normalizer_le_monoFix0 (by omega) B hb0 hfus hodd hN.le ?_
    rw [hN]
    exact diagonal_tauSign_mem_monoFix0 n
  · refine false_of_monoN0Hyp hn (B.monoN0Hyp_xg hb0 hN hodd hfus) ?_
    rwa [Subgroup.card_map_of_injective B.glHom_injective]

end CFSG.StandardType.FrameRoute.FS81
