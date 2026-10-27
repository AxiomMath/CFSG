module

public import CFSG.LocalAnalysis.StandardType.FS81.N6MainMat
public import CFSG.LocalAnalysis.StandardType.FS81.N6Split
public import CFSG.LocalAnalysis.StandardType.FS81.N7MainRecOut
public import CFSG.LocalAnalysis.StandardType.FS81.N6All

public section

namespace CFSG.StandardType.FrameRoute.FS81

open CFSG.Open CFSG.Assembly
open scoped Matrix

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

theorem prod_succ_neg_six (v : Fin 7 → ZMod 3) : ∏ i : Fin 6, (-v) i.succ = ∏ i : Fin 6, v i.succ := by
  simp only [Pi.neg_apply, Fin.prod_univ_six]
  ring

namespace Basis3

variable {G : Type} [Group G]

theorem isConjLineIn_iff_O6 (B : Basis3 G 7) {e : Coords 7} (he : e ≠ 0) :
    IsConjLineIn B.span (B.vec (Pi.single 0 1)) (B.line e) ↔
      O6 ((ggAutomizer ⊤ B.span).map B.glHom) e ∨ O6 ((ggAutomizer ⊤ B.span).map B.glHom) (-e) := by
  constructor
  · rintro ⟨g, hgN, hg⟩
    obtain ⟨x, hx, hxv⟩ := B.exists_xg_of_mem_normalizer hgN
    rw [hxv] at hg
    have hmem : B.vec e ∈ Subgroup.zpowers
        (B.vec ((x : Matrix (Fin 7) (Fin 7) (ZMod 3)) *ᵥ Pi.single 0 1)) := by
      rw [hg]
      exact Subgroup.mem_zpowers _
    rcases B.eq_or_eq_neg_of_vec_mem_zpowers he hmem with h | h
    · exact Or.inl ⟨x, hx, h.symm⟩
    · exact Or.inr ⟨x, hx, by rw [h, neg_neg]⟩
  · rintro (⟨x, hx, h⟩ | ⟨x, hx, h⟩)
    · obtain ⟨g, hgN, hgv⟩ := B.exists_conj_of_mem_xg hx
      refine ⟨g, hgN, ?_⟩
      show Subgroup.zpowers _ = Subgroup.zpowers (B.vec e)
      rw [hgv, h]
    · obtain ⟨g, hgN, hgv⟩ := B.exists_conj_of_mem_xg hx
      refine ⟨g, hgN, ?_⟩
      show Subgroup.zpowers _ = Subgroup.zpowers (B.vec e)
      rw [hgv, h, B.vec_neg_eq_inv, Subgroup.zpowers_inv]

theorem n6MatHyp_xg [Finite G] (B : Basis3 G 7) {b₀ : G} (hb0 : B.b 0 = b₀)
    (hN0 : B.realized (Subgroup.normalizer (Subgroup.zpowers b₀ : Set G)) = evenN0 6)
    (hodd : OddCoreTrivial B.span) (hfus : Fus42 B b₀) :
    N6MatHyp ((ggAutomizer ⊤ B.span).map B.glHom) where
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

@[expose] def sgn6 : Fin 7 → ZMod 3 := fun i => if i = 6 then -1 else 1

theorem isSign_sgn6 : IsSign sgn6 := by
  unfold IsSign sgn6
  decide

theorem recOutD6_of_evenN0 {G : Type} [Group G] [Finite G] {b₀ : G} {K E : Subgroup G}
    {B : Basis3 G 7} (hB : Adapted B b₀ K E) (hfus : Fus42 B b₀) (hodd : OddCoreTrivial E)
    (hN0 : B.realized (Subgroup.normalizer (Subgroup.zpowers b₀ : Set G)) = evenN0 6) :
    ∃ B' : Basis3 G 7, Adapted B' b₀ K E ∧ RecOutD6 B' b₀ := by
  classical
  obtain ⟨hspan, hb0, hBK⟩ := hB
  subst hspan
  have hM := B.n6MatHyp_xg hb0 hN0 hodd hfus
  obtain ⟨hX, δ, hδ, hO⟩ := orbit_evenN0_six _ hM
  have h1 : Nat.card ↥(ggAutomizer ⊤ B.span) = 2903040 := by
    rw [← hX, Subgroup.card_map_of_injective B.glHom_injective]
  have h2 : ∀ e : Coords 7, e ≠ 0 → (IsConjLine b₀ (B.line e) ↔
      ((wt e = 1 ∧ e 0 ≠ 0) ∨ (wt e = 2 ∧ e 0 = 0) ∨ (wt e = 7 ∧ ∏ i : Fin 6, e i.succ = δ))) := by
    intro e he
    rw [B.isConjLine_iff_isConjLineIn hfus, ← hb0, ← B.vec_single, B.isConjLineIn_iff_O6 he,
      hO e, hO (-e), wt_neg, prod_succ_neg_six, Pi.neg_apply, neg_ne_zero, neg_eq_zero, or_self]
  rcases hδ with hδ1 | hδm
  · exact ⟨B, ⟨rfl, hb0, hBK⟩, h1, fun e he => by rw [h2 e he, hδ1]⟩
  · refine ⟨B.signed sgn6 isSign_sgn6, ⟨B.span_signed isSign_sgn6, ?_, ?_⟩, ?_, ?_⟩
    · show B.b 0 ^ (sgn6 0).val = b₀
      rw [show (sgn6 0).val = 1 by decide, pow_one, hb0]
    · intro i hi
      exact K.pow_mem (hBK i hi) _
    · rw [B.span_signed isSign_sgn6]
      exact h1
    · intro e he
      have hp : ∏ i : Fin 6, sgn6 i.succ * e i.succ = -∏ i : Fin 6, e i.succ := by
        rw [Finset.prod_mul_distrib, show ∏ i : Fin 6, sgn6 i.succ = -1 by decide, neg_one_mul]
      have h0 : sgn6 0 * e 0 = e 0 := by rw [show sgn6 0 = 1 by decide, one_mul]
      rw [B.line_signed isSign_sgn6, h2 _ (sign_mul_ne_zero_vec isSign_sgn6 he),
        wt_sign_mul isSign_sgn6]
      simp only [h0, hp, hδm, neg_eq_iff_eq_neg, neg_neg]

theorem l1N6Main_holds : L1N6Main := fun _ _ _ _ _ _ _ _ hB _ hfus hodd hN0 =>
  recOutD6_of_evenN0 hB hfus hodd hN0

theorem l1N6_holds : L1N6 := by
  intro G _ _ b₀ K E hstd B hB hII hfus hodd
  rcases hII.2 with h | h | h
  · exact (l1N6Fix_holds G b₀ K E hstd B hB hII hfus hodd h).elim
  · exact l1N6Main_holds G b₀ K E hstd B hB hII hfus hodd h
  · exact (not_evenAll0_six_of_std G b₀ K E hstd B hB hII hfus hodd h).elim

end CFSG.StandardType.FrameRoute.FS81

end
