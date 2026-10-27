module

public import CFSG.RankThree.PartTwo.KFacts.L34Aut
import CFSG.RankThree.PartTwo.Census.Criteria

public section

namespace CFSG.RankThree.PartTwo.KFacts.L34

open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.LinearFlag
open CFSG.LocalAnalysis.ComponentInitial.LinearThreeFourFixedNine
open scoped commutatorElement

variable {k : Type*} [Field k]

section SL

theorem card_specialLinearGroup (hk : Nat.card k = 4) :
    Nat.card (Matrix.SpecialLinearGroup (Fin 3) k) = 60480 := by
  rw [Subgroup.card_eq_card_quotient_mul_card_subgroup (scalars 3 k)]
  change Nat.card (projectiveSL 3 k) * _ = _
  rw [card_projectiveSL hk, card_scalars hk]

theorem card_center_specialLinearGroup (hk : Nat.card k = 4) :
    Nat.card (Subgroup.center (Matrix.SpecialLinearGroup (Fin 3) k)) = 3 := by
  rw [← scalars_eq_center, card_scalars hk]

theorem pRank_three_specialLinearGroup (hk : Nat.card k = 4) :
    CFSG.pRank 3 (Matrix.SpecialLinearGroup (Fin 3) k) = 2 := by
  have : Finite (Matrix.SpecialLinearGroup (Fin 3) k) :=
    Nat.finite_of_card_ne_zero (by rw [card_specialLinearGroup hk]; norm_num)
  obtain ⟨u, hu⟩ := exists_units_ne_one hk
  have h3 := LinearThreeFourOuter.units_pow_three hk u
  have hx3 : hSL u ^ 3 = 1 := by
    rw [hSL, ← map_pow]
    have : ((u, 1) : kˣ × kˣ) ^ 3 = 1 := Prod.ext h3 (one_pow 3)
    rw [this, map_one]
  have hy3 : (rSL : Matrix.SpecialLinearGroup (Fin 3) k) ^ 3 = 1 := rSL_pow_three
  have hz : ⁅hSL u, (rSL : Matrix.SpecialLinearGroup (Fin 3) k)⁆ = (zSL u)⁻¹ := by
    rw [commutatorElement_def]
    exact hSL_commutator hk
  have hzc : (zSL u)⁻¹ ∈ Subgroup.center (Matrix.SpecialLinearGroup (Fin 3) k) :=
    inv_mem (scalars_le_center 3 k (zSL_mem_scalars hk))
  have hzx : Commute ⁅hSL u, (rSL : Matrix.SpecialLinearGroup (Fin 3) k)⁆ (hSL u) := by
    rw [hz]
    exact ((Subgroup.mem_center_iff.mp hzc) (hSL u)).symm
  have hzy : Commute ⁅hSL u, (rSL : Matrix.SpecialLinearGroup (Fin 3) k)⁆
      (rSL : Matrix.SpecialLinearGroup (Fin 3) k) := by
    rw [hz]
    exact ((Subgroup.mem_center_iff.mp hzc) rSL).symm
  have hz1 : ⁅hSL u, (rSL : Matrix.SpecialLinearGroup (Fin 3) k)⁆ ≠ 1 := by
    rw [hz, Ne, inv_eq_one]
    intro h
    have h0 := congrFun (congrFun (congrArg (fun g : Matrix.SpecialLinearGroup (Fin 3) k =>
      (g : Matrix (Fin 3) (Fin 3) k)) h) 0) 0
    simp only [zSL, coe_dHom, Matrix.SpecialLinearGroup.coe_one] at h0
    simp at h0
    exact hu h0
  have hL : (Nat.card (Matrix.SpecialLinearGroup (Fin 3) k)).factorization 3 = 3 := by
    rw [card_specialLinearGroup hk]
    exact CFSG.RankThree.Asc83Table.factorization_eq_of_eq Nat.prime_three
      (show 60480 = 3 ^ 3 * 2240 by norm_num) (by norm_num)
  exact CFSG.RankThree.Asc83Table.ex27_pRank hx3 hy3 hzx hzy hz1 hL

theorem dHom_conj_wMat (p : kˣ × kˣ) (c : k) :
    dHom p * LinearFieldFour.wMat c * (dHom p)⁻¹ =
      LinearFieldFour.wMat ((p.1 : k) * p.1 * p.2 * c) := by
  rw [mul_inv_eq_iff_eq_mul]
  apply Subtype.ext
  rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul, coe_dHom,
    LinearFieldFour.coe_wMat, LinearFieldFour.coe_wMat]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [LinearFieldFour.wM, Matrix.mul_apply, Matrix.diagonal]
  field_simp

theorem localRank_three_specialLinearGroup {k : Type} [Field k] [Finite k]
    (hk : Nat.card k = 4) :
    CFSG.Assembly.RankThreeEven.localRank 3 (Matrix.SpecialLinearGroup (Fin 3) k) = 2 := by
  have := LinearFieldFour.charP_two_of_card_eq_four hk
  obtain ⟨u, hu⟩ := exists_units_ne_one hk
  apply le_antisymm
  ·
    refine CFSG.RankThree.PartTwo.Census.localRank_le_of_pRank_le Nat.prime_three ?_
    refine CFSG.RankThree.PartTwo.Census.pRank_le_two_of_nonabelian Nat.prime_three
      (by rw [card_specialLinearGroup hk]; norm_num) (S := qSub) (by rw [card_qSub hk]; norm_num) ?_
    refine ⟨hSL u, hSL_mem_qSub, rSL, rSL_mem_qSub, fun h => ?_⟩
    have hc : hSL u * rSL * (hSL u)⁻¹ * rSL⁻¹ = 1 := by rw [h]; group
    rw [hSL_commutator hk, inv_eq_one] at hc
    have h0 := congrFun (congrFun (congrArg (fun g : Matrix.SpecialLinearGroup (Fin 3) k =>
      (g : Matrix (Fin 3) (Fin 3) k)) hc) 0) 0
    simp only [zSL, coe_dHom, Matrix.SpecialLinearGroup.coe_one] at h0
    simp at h0
    exact hu h0
  ·
    let wHom : Multiplicative k →* Matrix.SpecialLinearGroup (Fin 3) k :=
      { toFun := fun c => LinearFieldFour.wMat (Multiplicative.toAdd c)
        map_one' := by
          apply Subtype.ext
          rw [LinearFieldFour.coe_wMat]
          ext i j
          fin_cases i <;> fin_cases j <;> simp [LinearFieldFour.wM]
        map_mul' := fun c d => LinearFieldFour.wMat_add _ _ }
    set W := wHom.range
    have hW : W ≠ ⊥ := by
      intro h
      have hmem : LinearFieldFour.wMat (1 : k) ∈ W := ⟨Multiplicative.ofAdd 1, rfl⟩
      rw [h, Subgroup.mem_bot] at hmem
      have h02 := congrFun (congrFun (congrArg (fun g : Matrix.SpecialLinearGroup (Fin 3) k =>
        (g : Matrix (Fin 3) (Fin 3) k)) hmem) 0) 2
      simp [LinearFieldFour.coe_wMat, LinearFieldFour.wM] at h02
    have hW2 : IsPGroup 2 W := by
      rintro ⟨_, c, rfl⟩
      refine ⟨1, Subtype.ext ?_⟩
      change wHom c ^ 2 = 1
      rw [sq, ← map_mul, show c * c = 1 from ?_, map_one]
      change Multiplicative.ofAdd (Multiplicative.toAdd c + Multiplicative.toAdd c) = 1
      rw [CharTwo.add_self_eq_zero]
      rfl
    set E := (dHom : kˣ × kˣ →* Matrix.SpecialLinearGroup (Fin 3) k).range
    have hinj : Function.Injective (dHom : kˣ × kˣ →* Matrix.SpecialLinearGroup (Fin 3) k) := by
      intro p q hpq
      have e := congrArg (fun g : Matrix.SpecialLinearGroup (Fin 3) k =>
        (g : Matrix (Fin 3) (Fin 3) k)) hpq
      have e0 := congrFun (congrFun e 0) 0
      have e1 := congrFun (congrFun e 1) 1
      simp [coe_dHom, Matrix.diagonal] at e0 e1
      exact Prod.ext (Units.ext e0) (Units.ext e1)
    have hEc : Nat.card E = 3 ^ 2 := by
      rw [← Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv, Nat.card_prod,
        LinearThreeFourOuter.card_units_eq_three hk]
      norm_num
    have hE : CFSG.Assembly.IsElemAbelian 3 E := by
      refine ⟨⟨⟨fun a b => Subtype.ext ?_⟩⟩, ?_⟩
      · obtain ⟨p, hp⟩ := a.2
        obtain ⟨q, hq⟩ := b.2
        change (a : Matrix.SpecialLinearGroup (Fin 3) k) * b = b * a
        rw [← hp, ← hq, ← map_mul, ← map_mul, mul_comm]
      · rintro _ ⟨p, rfl⟩
        rw [← map_pow]
        have : p ^ 3 = 1 := Prod.ext (LinearThreeFourOuter.units_pow_three hk _)
          (LinearThreeFourOuter.units_pow_three hk _)
        rw [this, map_one]
    have hconjW : ∀ p : kˣ × kˣ, ∀ w ∈ W, dHom p * w * (dHom p)⁻¹ ∈ W := by
      rintro p _ ⟨c, rfl⟩
      refine ⟨Multiplicative.ofAdd ((p.1 : k) * p.1 * p.2 * Multiplicative.toAdd c), ?_⟩
      exact (dHom_conj_wMat p _).symm
    have hEW : E ≤ Subgroup.normalizer (W : Set (Matrix.SpecialLinearGroup (Fin 3) k)) := by
      rintro _ ⟨p, rfl⟩
      refine Subgroup.mem_normalizer_iff.mpr fun w => ⟨hconjW p w, fun hw => ?_⟩
      have := hconjW p⁻¹ _ hw
      rwa [map_inv, inv_inv, ← mul_assoc, ← mul_assoc, inv_mul_cancel, one_mul, mul_assoc,
        inv_mul_cancel, mul_one] at this
    exact CFSG.RankThree.PartTwo.Census.le_localRank_of_le_normalizer Nat.prime_three hW hW2 hE
      hEc hEW

end SL


end CFSG.RankThree.PartTwo.KFacts.L34
