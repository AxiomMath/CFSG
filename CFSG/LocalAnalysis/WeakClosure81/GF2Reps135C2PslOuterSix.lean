module

public import CFSG.LocalAnalysis.WeakClosure81.GF2Reps135C2PslOuterSixGraph
import CFSG.LocalAnalysis.WeakClosure81.GF2Reps135C2Gen
public import CFSG.LocalAnalysis.WeakClosure81.GF2Reps135C2Defs
public import CFSG.LocalAnalysis.WeakClosure81.GF2Reps135C2FinLinearModel
public import CFSG.LocalAnalysis.WeakClosure81.GF2Reps135C2FinLinearNormalizer
public import CFSG.LocalAnalysis.WeakClosure81.GF2Reps135C2FinLinearRank

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.Quasithin
open CFSG.LieType.SpecialLinear
open CFSG.HardMathSupport.Meierfrankenfeld.PSUScalar
open CFSG.LieType.SpecialLinear.ExteriorModel

theorem finRowStmt_psl_six_twenty :
    FinRowStmt .PSL 6 1 20 := by
  intro W _ _ hW Y L g hctx hgY hg2 hlie hcard
  obtain ⟨K, _, _, hK, ⟨σ⟩⟩ := exists_mulEquiv_specialLinear_of_lieModel hctx (by norm_num) hlie
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : CharP K 2 := charP_of_card_eq_prime hK
  have hW2 : ∀ a : Additive W, (2 : ℕ) • a = 0 := fun a => by
    apply Additive.toMul.injective
    show (Additive.toMul a) ^ 2 = 1
    exact hW _
  letI : Module (ZMod 2) (Additive W) := AddCommGroup.zmodModule hW2
  have hLY : L ≤ Y := hctx.2.2.1
  have hirr : (specialLinearRep σ).IsIrreducible := isIrreducible_specialLinearRep hctx σ
  have hne : ∃ x, specialLinearRep σ x ≠ 1 := specialLinearRep_ne_one hctx σ
  have hcardA : Nat.card (Additive W) = 2 ^ 20 := by
    rw [← hcard]
    exact Nat.card_congr Additive.toMul
  have hG : Subgroup.center (Matrix.SpecialLinearGroup (Fin 6) K) = ⊥ :=
    center_specialLinear_eq_bot_of_card_two hK
  have hπ := slToY_injective hLY σ
  have hg2' : g * g = 1 := by
    have h : g ^ 2 = 1 := by rw [← hg2]; exact pow_orderOf_eq_one g
    simpa [pow_two] using h
  have hgY2 : (⟨g, hgY⟩ : ↥Y) * ⟨g, hgY⟩ = 1 := Subtype.ext hg2'
  obtain ⟨x, hx⟩ := exists_conj_mem_range_or_borelStd_one hK (by norm_num) (slToY hLY σ) hπ
    (fun c hc => by rw [eq_one_of_mem_centralizer_slToY hctx σ hG hc]; simp)
    (slToY_mem_normalizer hctx σ hgY) hgY2
  set g' : ↥Y := (slToY hLY σ x)⁻¹ * ⟨g, hgY⟩ * slToY hLY σ x with hg'
  have hg'2 : g' * g' = 1 := by
    calc g' * g' = (slToY hLY σ x)⁻¹ * ((⟨g, hgY⟩ : ↥Y) * ⟨g, hgY⟩) * slToY hLY σ x := by
          rw [hg']; group
      _ = 1 := by rw [hgY2]; group
  have hconj : E3.mQuot ⊤ (fixV (Subgroup.zpowers (g' : MulAut W))) =
      E3.mQuot ⊤ (fixV (Subgroup.zpowers g)) := by
    have h := w135c2_mQuot_conj (((slToY hLY σ x : ↥Y) : MulAut W)⁻¹) g
    simpa [hg'] using h
  rcases hx with ⟨y, hy⟩ | ⟨B, hB, τ, hgraph⟩
  · have hy2 : y * y = 1 := by
      apply hπ
      rw [map_mul, hy, hg'2, map_one]
    have hy1 : y ≠ 1 := by
      rintro rfl
      have h1 : g' = 1 := by rw [← hy, map_one]
      have h2 : (⟨g, hgY⟩ : ↥Y) = 1 := by
        calc (⟨g, hgY⟩ : ↥Y) = slToY hLY σ x * g' * (slToY hLY σ x)⁻¹ := by rw [hg']; group
          _ = 1 := by rw [h1]; group
      have h3 : g = 1 := congrArg Subtype.val h2
      rw [h3, orderOf_one] at hg2
      omega
    have hnat : Nat.card (Additive W) ≠ 2 ^ 6 := by
      rw [hcardA]
      norm_num
    have hrank := sub_two_le_finrank_range_sub_one hK (show 6 ≤ 6 by norm_num)
      (specialLinearRep σ) hirr hne hnat hy2 hy1
    have hmul : mulAutLinear (g' : MulAut W) = specialLinearRep σ y := by
      rw [← hy, specialLinearRep_apply, coe_slToY]
    rw [← hconj, mQuot_fixV_zpowers_eq_finrank_range_sub_one, hmul]
    omega
  · have hintertwine : ∀ (y : Matrix.SpecialLinearGroup (Fin 6) K) (w : Additive W),
        (mulAutLinearEquiv (g' : MulAut W)) (specialLinearRep σ y w) =
          specialLinearRep σ (borelStd 6 K B τ 1 y) ((mulAutLinearEquiv (g' : MulAut W)) w) := by
      intro y w
      have h := congrArg (fun z : ↥Y => (z : MulAut W) (Additive.toMul w)) (hgraph y)
      exact congrArg Additive.ofMul h
    have h4 := w135c2_graph_six_twenty hK (specialLinearRep σ) hirr hne hcardA hB hintertwine
    rw [← hconj, mQuot_fixV_zpowers_eq_finrank_range_sub_one]
    exact h4

end CFSG.LocalAnalysis.WeakClosure81
