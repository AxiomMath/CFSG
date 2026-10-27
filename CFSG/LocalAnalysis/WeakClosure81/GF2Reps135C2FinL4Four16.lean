module

public import CFSG.LocalAnalysis.WeakClosure81.GF2Reps135C2FinL4Four16Model
public import CFSG.LocalAnalysis.WeakClosure81.GF2Reps135C2FinL4Four16Normalizer
public import CFSG.LocalAnalysis.WeakClosure81.GF2Reps135C2FinL4Four16Rank
public import CFSG.LocalAnalysis.WeakClosure81.GF2Reps135C2FinL4Four16Graph
public import CFSG.LocalAnalysis.WeakClosure81.GF2Reps135C2FinL4Four16Flip
import CFSG.LocalAnalysis.WeakClosure81.GF2Reps135C2Gen
public import CFSG.LocalAnalysis.WeakClosure81.GF2Reps135C2Defs
public import CFSG.LocalAnalysis.WeakClosure81.GF2Reps135C2FinL4Four16Pair
public import CFSG.LocalAnalysis.WeakClosure81.GF2Reps135C2FinLinearModel

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.Quasithin CFSG.Open CFSG.LocalAnalysis.UniquenessCase.UC22
open CFSG.Quasithin.F6
open CFSG.LocalAnalysis.UniquenessCase.PartTwo
open CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719
open CFSG.LieType.SpecialLinear

theorem finL4Four16_holds :
    FinL4Four16 := by
  intro W _ _ hW Y L g hctx hgY hg2 hlie hcard
  obtain ⟨K, _, _, _, hK, ⟨σ⟩⟩ := exists_mulEquiv_specialLinear_four_of_lieModel hctx hlie
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hW2 : ∀ a : Additive W, (2 : ℕ) • a = 0 := fun a => by
    apply Additive.toMul.injective
    show (Additive.toMul a) ^ 2 = 1
    exact hW _
  letI : Module (ZMod 2) (Additive W) := AddCommGroup.zmodModule hW2
  have hLY : L ≤ Y := hctx.2.2.1
  have hirr : (specialLinearRep σ).IsIrreducible := isIrreducible_specialLinearRep hctx σ
  have hne : ∃ x, specialLinearRep σ x ≠ 1 := specialLinearRep_ne_one hctx σ
  haveI : (specialLinearRep σ).IsIrreducible := hirr
  have hcardA : Nat.card (Additive W) = 2 ^ 16 := by
    rw [← hcard]
    exact Nat.card_congr Additive.toMul
  have hG : Subgroup.center (Matrix.SpecialLinearGroup (Fin 4) K) = ⊥ :=
    center_specialLinear_eq_bot_of_card_four hK
  have hπ := slToY_injective hLY σ
  have hg2' : g * g = 1 := by
    have h : g ^ 2 = 1 := by rw [← hg2]; exact pow_orderOf_eq_one g
    simpa [pow_two] using h
  have hgY2 : (⟨g, hgY⟩ : ↥Y) * ⟨g, hgY⟩ = 1 := Subtype.ext hg2'
  obtain ⟨x, hx⟩ := exists_conj_mem_range_or_borelStd_or_fieldAut hK (slToY hLY σ) hπ
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
  obtain ⟨ε, j, hε, hE, hj, h0, h1⟩ := exists_pair_label hK (specialLinearRep σ) hne hcardA
  have hgg : (g' : MulAut W) * (g' : MulAut W) = 1 := congrArg Subtype.val hg'2
  have hdd : mulAutLinearEquiv (g' : MulAut W) * mulAutLinearEquiv (g' : MulAut W) = 1 := by
    refine LinearEquiv.ext fun w => ?_
    show mulAutLinear (g' : MulAut W) (mulAutLinear (g' : MulAut W) w) = w
    rw [← Module.End.mul_apply, ← mulAutLinear_mul, hgg, mulAutLinear_one]
    rfl
  rw [← hconj, mQuot_fixV_zpowers_eq_finrank_range_sub_one]
  rcases hx with ⟨y, hy⟩ | ⟨B, hB, τ, hgraph⟩ | ⟨τ, hτ1, hfield⟩
  · have hy2 : y * y = 1 := by
      apply hπ
      rw [map_mul, hy, hg'2, map_one]
    have hy1 : y ≠ 1 := by
      rintro rfl
      have h1' : g' = 1 := by rw [← hy, map_one]
      have h2 : (⟨g, hgY⟩ : ↥Y) = 1 := by
        calc (⟨g, hgY⟩ : ↥Y) = slToY hLY σ x * g' * (slToY hLY σ x)⁻¹ := by rw [hg']; group
          _ = 1 := by rw [h1']; group
      have h3 : g = 1 := congrArg Subtype.val h2
      rw [h3, orderOf_one] at hg2
      omega
    have hrank := six_le_finrank_range_sub_one_of_pair hK (specialLinearRep σ) hε hE hj h0 h1
      hy2 hy1
    have hmul : mulAutLinear (g' : MulAut W) = specialLinearRep σ y := by
      rw [← hy, specialLinearRep_apply, coe_slToY]
    rw [hmul]
    omega
  · exfalso
    refine false_of_borelStd_one_intertwiner_pair hK (specialLinearRep σ) hε hE hj h0 h1
      (d := mulAutLinearEquiv (g' : MulAut W)) hB (τ := τ) hdd ?_
    intro y w
    have h := congrArg (fun z : ↥Y => (z : MulAut W) (Additive.toMul w)) (hgraph y)
    exact congrArg Additive.ofMul h
  · have hrank := six_le_finrank_range_sub_one_of_fieldAut hK (specialLinearRep σ) hε hE hj h0 h1
      hτ1 (d := mulAutLinearEquiv (g' : MulAut W)) hdd (fun y w => by
        have h := congrArg (fun z : ↥Y => (z : MulAut W) (Additive.toMul w)) (hfield y)
        exact congrArg Additive.ofMul h)
    have hcoe : (mulAutLinearEquiv (g' : MulAut W)).toLinearMap = mulAutLinear (g' : MulAut W) :=
      rfl
    rw [hcoe] at hrank
    omega

end CFSG.LocalAnalysis.WeakClosure81
