module

public import CFSG.RankThree.PartOne.CTP.Su4Std
public import CFSG.RankThree.PartOne.CTP.SpinMinusEven
public import CFSG.RankThree.PartOne.CTP.LinearCore
public import CFSG.RankThree.PartOne.CTP.SU4EvenSU

public section

namespace CFSG.RankThree.PartOne.CTP.SU4Even

open CFSG.LieType.Universal CFSG.LieType.Universal.Spin CFSG.LieType.Universal.Spin.Twisted
  CFSG.LieType.Universal.Unitary CFSG.LieType.BorelTits
  CFSG.ClassicalInvolution.Models.TwistedPairs CFSG.Timmesfeld
open CFSG.ClassicalInvolution.WeakCT.SU4 (sl2_mem_of_tv sulong coe_sulong suroot coe_suroot)
open scoped Matrix MatrixGroups

section Standard

variable {K : Type} [Field K] {σ : K ≃+* K}

theorem sulong_mem_range_lbEmb {i : Fin 4} (hi : i ≠ Fin.rev i) (hi12 : i = 1 ∨ i = 2) (x : K)
    (hx : σ x = -x) : sulong σ i hi x hx ∈ (lbEmb σ).range := by
  refine mem_range_lbEmb_of_fix _ ?_ ?_
  · rw [mem_stabVec]
    ext r
    rcases hi12 with rfl | rfl <;> fin_cases r <;>
      simp [matS, coe_sulong, longRootMatrix, Matrix.mulVec, dotProduct,
        Matrix.single_apply, Fin.rev, Pi.single_apply]
  · rw [mem_stabVec]
    ext r
    rcases hi12 with rfl | rfl <;> fin_cases r <;>
      simp [matS, coe_sulong, longRootMatrix, Matrix.mulVec, dotProduct,
        Matrix.single_apply, Fin.rev, Pi.single_apply]

theorem suroot_zero_one_mem_range_sbEmb (hσ : ∀ c, σ (σ c) = c) (z : K) :
    suroot σ hσ 0 1 (by decide) (by decide) (by decide) z ∈ (sbEmb σ hσ).range := by
  refine mem_range_sbEmb_of_blk σ hσ _ ?_ ?_
  · intro i j hij
    fin_cases i <;> fin_cases j <;>
      simp [matS, coe_suroot, rootMatrix, Fin.rev] at hij ⊢
  · simp [ulBlock, matS, coe_suroot, rootMatrix, Matrix.det_fin_two, Fin.rev]

theorem suroot_one_zero_mem_range_sbEmb (hσ : ∀ c, σ (σ c) = c) (z : K) :
    suroot σ hσ 1 0 (by decide) (by decide) (by decide) z ∈ (sbEmb σ hσ).range := by
  refine mem_range_sbEmb_of_blk σ hσ _ ?_ ?_
  · intro i j hij
    fin_cases i <;> fin_cases j <;>
      simp [matS, coe_suroot, rootMatrix, Fin.rev] at hij ⊢
  · simp [ulBlock, matS, coe_suroot, rootMatrix, Matrix.det_fin_two, Fin.rev]

end Standard

section Blocks

variable {F K : Type} [Field F] [Field K] [Algebra F K] [Finite F] [CharP F 2] {f : ℕ}
  [CharP K 2] [Finite K] {b c : F} (D : KleinDataEven F K (unitaryInvolution K 2 f) b c)
  (hF : Nat.card F = 2 ^ f) (hK : Nat.card K = (2 ^ f) ^ 2)
  (hirr : ∀ s : F, s ^ 2 + b * s + c ≠ 0)

omit [Finite F] [CharP F 2] in
theorem minusLongBlock_injective : Function.Injective (minusLongBlock b c) :=
  CFSG.LieType.Steinberg.SpinFrame.longSL2_injective _ _ _ _

include hF hK hirr in
theorem map_minusLongBlock_eq_lbEmb :
    (minusLongBlock b c).range.map (D.PhiSUEven hirr) =
      (lbEmb (unitaryInvolution K 2 f)).range := by
  have hle : (minusLongBlock b c).range.map (D.PhiSUEven hirr) ≤
      (lbEmb (unitaryInvolution K 2 f)).range := by
    rw [← MonoidHom.range_comp]
    rintro _ ⟨A, rfl⟩
    refine sl2_mem_of_tv ((D.PhiSUEven hirr).comp (minusLongBlock b c)) (fun x => ?_)
      (fun x => ?_) A
    · rw [MonoidHom.comp_apply, D.PhiSUEven_minusLongBlock_tv01 hirr]
      exact sulong_mem_range_lbEmb _ (Or.inl rfl) _ _
    · rw [MonoidHom.comp_apply, D.PhiSUEven_minusLongBlock_tv10 hirr]
      exact sulong_mem_range_lbEmb _ (Or.inr rfl) _ _
  refine Subgroup.eq_of_le_of_card_ge hle ?_
  rw [Subgroup.card_map_of_injective (D.PhiSUEven_injective hirr),
    (Nat.card_congr (MonoidHom.ofInjective
      (minusLongBlock_injective (b := b) (c := c))).toEquiv).symm,
    natCard_range_lbEmb, CFSG.LieType.Steinberg.card_SU_two hK,
    CFSG.LieType.Steinberg.card_specialLinearGroup_fin_two F, hF]

variable [Fact (∀ r : F, r ^ 2 ≠ -c + b * r)]

omit [Algebra F K] [Finite K] [Finite F] [CharP F 2] [Fact (∀ r : F, r ^ 2 ≠ -c + b * r)] in
theorem natCard_shortField : Nat.card (ShortField b c) = Nat.card F * Nat.card F := by
  rw [Nat.card_congr (QuadraticAlgebra.equivProd (-c) b), Nat.card_prod]

include hF hK hirr in
theorem map_shortBlock_eq_sbEmb :
    (shortBlock hirr 3 finOne).range.map (D.PhiSUEven hirr) =
      (sbEmb (unitaryInvolution K 2 f) (unitaryInvolution_involutive hK)).range := by
  have := finite_shortField (b := b) (c := c)
  have hle : (shortBlock hirr 3 finOne).range.map (D.PhiSUEven hirr) ≤
      (sbEmb (unitaryInvolution K 2 f) (unitaryInvolution_involutive hK)).range := by
    rw [← MonoidHom.range_comp]
    rintro _ ⟨A, rfl⟩
    refine sl2_mem_of_tv ((D.PhiSUEven hirr).comp (shortBlock hirr 3 finOne)) (fun x => ?_)
      (fun x => ?_) A
    · rw [MonoidHom.comp_apply, D.PhiSUEven_shortBlock_tv01 hirr]
      exact suroot_zero_one_mem_range_sbEmb _ _
    · rw [MonoidHom.comp_apply, D.PhiSUEven_shortBlock_tv10 hirr]
      exact suroot_one_zero_mem_range_sbEmb _ _
  refine Subgroup.eq_of_le_of_card_ge hle ?_
  have hE : Nat.card (ShortField b c) = Nat.card K := by
    rw [natCard_shortField, hF, hK, sq]
  rw [Subgroup.card_map_of_injective (D.PhiSUEven_injective hirr),
    (Nat.card_congr (MonoidHom.ofInjective
      (shortBlock_injective_even hirr 3 finOne)).toEquiv).symm,
    natCard_range_sbEmb _]
  exact (card_sl2_eq hE.symm).le

end Blocks

end CFSG.RankThree.PartOne.CTP.SU4Even
