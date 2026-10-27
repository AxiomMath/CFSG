module

public import CFSG.LocalAnalysis.WeakClosure81.GF2Reps135C2FinLinearModel
public import CFSG.LocalAnalysis.WeakClosure81.GF2Reps135C2FinLinearNormalizer
public import CFSG.LocalAnalysis.WeakClosure81.GF2Reps135C2FinLinearRank
public import CFSG.LocalAnalysis.WeakClosure81.GF2Reps135C2FinLinearGraph
import CFSG.LocalAnalysis.WeakClosure81.GF2Reps135C2Gen
public import CFSG.LocalAnalysis.WeakClosure81.GF2Reps135C2Defs

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.Quasithin CFSG.Open CFSG.LocalAnalysis.UniquenessCase.UC22
open CFSG.Quasithin.F6
open CFSG.LocalAnalysis.UniquenessCase.PartTwo
open CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719
open CFSG.HardMathSupport.Meierfrankenfeld.PSUScalar

theorem finRowStmt_psl_of_orbit_bound
    (n D : ℕ) (hn : 6 ≤ n) (hDn : D ≠ n)
    (horb : ∀ S : Finset (Fin n), (⟨0, by omega⟩ : Fin n) ∉ S → S ≠ ∅ →
      (∀ (j : Fin n) (hj : 1 ≤ j.val), (j ∈ S ↔ (⟨n - j.val, by omega⟩ : Fin n) ∈ S)) →
        D < orbitSize S) :
    FinRowStmt .PSL n 1 D := by
  intro W _ _ hW Y L g hctx hgY hg2 hlie hcard
  obtain ⟨K, _, _, hK, ⟨σ⟩⟩ := exists_mulEquiv_specialLinear_of_lieModel hctx (by omega) hlie
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
  have hcardA : Nat.card (Additive W) = 2 ^ D := by
    rw [← hcard]
    exact Nat.card_congr Additive.toMul
  have hG : Subgroup.center (Matrix.SpecialLinearGroup (Fin n) K) = ⊥ :=
    center_specialLinear_eq_bot_of_card_two hK
  have hπ := slToY_injective hLY σ
  have hg2' : g * g = 1 := by
    have h : g ^ 2 = 1 := by rw [← hg2]; exact pow_orderOf_eq_one g
    simpa [pow_two] using h
  have hgY2 : (⟨g, hgY⟩ : ↥Y) * ⟨g, hgY⟩ = 1 := Subtype.ext hg2'
  obtain ⟨x, hx⟩ := exists_conj_mem_range_or_borelStd_one hK (by omega) (slToY hLY σ) hπ
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
    have hnat : Nat.card (Additive W) ≠ 2 ^ n := by
      rw [hcardA]
      exact fun h => hDn (Nat.pow_right_injective le_rfl h)
    have hrank := sub_two_le_finrank_range_sub_one hK hn (specialLinearRep σ) hirr hne hnat hy2 hy1
    have hmul : mulAutLinear (g' : MulAut W) = specialLinearRep σ y := by
      rw [← hy, specialLinearRep_apply, coe_slToY]
    rw [← hconj, mQuot_fixV_zpowers_eq_finrank_range_sub_one, hmul]
    omega
  · exfalso
    have hgg : (g' : MulAut W) * (g' : MulAut W) = 1 := congrArg Subtype.val hg'2
    refine false_of_borelStd_one_intertwiner hK hn (specialLinearRep σ) hirr hne hcardA horb
      (d := mulAutLinearEquiv (g' : MulAut W)) hB (τ := τ) ?_ ?_
    · refine LinearEquiv.ext fun w => ?_
      show mulAutLinear (g' : MulAut W) (mulAutLinear (g' : MulAut W) w) = w
      rw [← Module.End.mul_apply, ← mulAutLinear_mul, hgg, mulAutLinear_one]
      rfl
    · intro y w
      have h := congrArg (fun z : ↥Y => (z : MulAut W) (Additive.toMul w)) (hgraph y)
      exact congrArg Additive.ofMul h

end CFSG.LocalAnalysis.WeakClosure81
