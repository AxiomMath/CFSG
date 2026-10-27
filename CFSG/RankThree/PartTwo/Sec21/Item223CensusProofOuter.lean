module

public import CFSG.RankThree.PartTwo.Sec21.Item223CensusProof
public import CFSG.RankThree.PartTwo.KFacts.K72FieldKind
public import CFSG.RankThree.PartTwo.KFacts.AutPSpOrderThree
import CFSG.LocalAnalysis.ComponentInitial.SymplecticPerfectCoverOuterPrime

public section

namespace CFSG.RankThree.PartTwo.Sec21

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open CFSG.RankThree.PartTwo.KFacts
open CFSG.ClassicalGroups.UnitaryFlag CFSG.LocalAnalysis.ComponentInitial

namespace Item223CensusProof

variable {G : Type} [Group G] [Finite G] {L : Subgroup G} {x : G}

theorem not_inducesKindPSL2_diagonal {K : Type} [Field K] [Finite K] (hx3 : x ^ 3 = 1)
    (h : InducesKindPSL2 K L x .diagonal) : False := by
  obtain ⟨e, hx, hτ, hni⟩ := h
  exact hni (isInnerAut_of_mem_inndiag_of_pow_three hτ (inducedAutHom_pow_eq_one L e hx hx3))

open CFSG.LocalAnalysis.ComponentInitial.SymplecticHigher in
theorem isInnerAut_conjAut_of_pow_three {r : ℕ} {K : Type} [Field K] [Finite K] (hr : 1 ≤ r)
    (A : gsp r K) (hA3 : conjAut r K A ^ 3 = 1) : IsInnerAut (conjAut r K A) := by
  have : NeZero r := ⟨by omega⟩
  obtain ⟨c, hc⟩ := exists_scalar_of_conjAut_eq_one hr (A := A ^ 3) (by rw [map_pow, hA3])
  have hμ : multiplier r K (A ^ 3) = c * c := by
    refine multiplier_eq _ ?_
    have h : ((((A ^ 3 : gsp r K) : GL (Fin r ⊕ Fin r) K)) : Matrix (Fin r ⊕ Fin r)
        (Fin r ⊕ Fin r) K) = (c : K) • (1 : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K) := by
      rw [hc, Matrix.GeneralLinearGroup.coe_scalar, Matrix.smul_one_eq_diagonal]
      rfl
    rw [h, Matrix.transpose_smul, Matrix.transpose_one, Matrix.smul_mul, Matrix.one_mul,
      Matrix.mul_smul, Matrix.mul_one, smul_smul, Units.val_mul]
  rw [map_pow] at hμ
  have hsq : (c * (multiplier r K A)⁻¹) ^ 2 = multiplier r K A := by
    rw [mul_pow, inv_pow, sq c, ← hμ]
    group
  exact conjAut_mem_inner_of_isSquare ⟨((c * (multiplier r K A)⁻¹ : Kˣ) : K), by
    rw [← Units.val_mul, ← sq, hsq]⟩

theorem not_inducesKindPSp_diagonal {r : ℕ} {K : Type} [Field K] [Finite K] (hr : 1 ≤ r)
    (hx3 : x ^ 3 = 1) (h : InducesKindPSp r K L x .diagonal) : False := by
  obtain ⟨e, hx, ⟨A, hA⟩, hni⟩ := h
  have h3 := inducedAutHom_pow_eq_one L e hx hx3
  rw [← hA] at h3 hni
  exact hni (isInnerAut_conjAut_of_pow_three hr A h3)

theorem not_inducesKindPSp4Even_diagonal {F : Type} [Field F] [Finite F] [CharP F 2]
    (h : InducesKindPSp4Even F L x .diagonal) : False := by
  obtain ⟨e, hx, ⟨A, hA⟩, hni⟩ := h
  rw [← hA] at hni
  exact hni (conjAut_mem_inner_of_charTwo A)

end Item223CensusProof

open Item223CensusProof


@[expose] def Outer223Linear : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (X A : Subgroup G),
    Sec4.IsList46 (X ⧸ aschbacherSolvableCore 3 X) →
    CFSG.Assembly.IsElemAbelian 3 A → Nat.card A = 3 ^ 4 →
    A ≤ Subgroup.normalizer (X : Set G) →
    Nat.card (A ⊓ Sec4.thetaQuotCentralizer X : Subgroup G) = 3 →
    (∀ x ∈ A, Sec4.InducesOuterTheta x X → KFacts.InducesStdKind X x .diagonal) →
    ∀ x ∈ A, Sec4.InducesOuterTheta x X →
      (∀ (n : ℕ) (K : Type) [Field K] [Finite K], 3 ≤ n →
        ¬ InducesKindPSL n K X x .diagonal ∧ ¬ InducesKindSL n K X x .diagonal) ∧
      ∀ (p f : ℕ) (K : Type) [Field K] (hK : UnitaryFieldData p f K) (hq : 2 < p ^ f),
        ¬ InducesKindPSU3 hK X x .diagonal ∧ ¬ InducesKindSU3 hK X hq x .diagonal

theorem inspection223ListOuter_of (hLin : Outer223Linear) : Inspection223ListOuter := by
  intro G _ _ X A hL hAe hA81 hAN hAC hdiag x hxA hout
  have hx3 : x ^ 3 = 1 := hAe.2 x hxA
  have hLx := hLin G X A hL hAe hA81 hAN hAC hdiag x hxA hout
  cases hdiag x hxA hout with
  | psl2 K h => exact not_inducesKindPSL2_diagonal hx3 h
  | psl n K hn h => exact (hLx.1 n K hn).1 h
  | sl n K hn h => exact (hLx.1 n K hn).2 h
  | psu3 hK hq h => exact (hLx.2 _ _ _ hK hq).1 h
  | su3 hK hq h => exact (hLx.2 _ _ _ hK hq).2 h
  | psp r K hr h =>
    exact not_inducesKindPSp_diagonal (by rcases hr with hr | ⟨rfl, -⟩ <;> omega) hx3 h
  | psp4even F h => exact not_inducesKindPSp4Even_diagonal h
  | g2 K hK3 hK4 h =>
    obtain ⟨e, hx, hτ, hni⟩ := h
    exact hni hτ
  | sz a K ha hK h =>
    obtain ⟨e, hx, hτ, hni⟩ := h
    exact hni hτ
  | triality f hf K hK σ hσ h =>
    obtain ⟨e, hx, h⟩ := h
    exact h
  | largeRee a ha K hK h =>
    obtain ⟨e, hx, hτ, hni⟩ := h
    exact hni hτ

end CFSG.RankThree.PartTwo.Sec21
