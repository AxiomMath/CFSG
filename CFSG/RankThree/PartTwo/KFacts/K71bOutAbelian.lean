module

public import CFSG.RankThree.PartTwo.Sec11.Omega
public import CFSG.RankThree.PartTwo.KFacts.K72OutL3
import CFSG.LocalAnalysis.ComponentInitial.QTNQRLinearUnitaryOuterDerivedLinear

public section

namespace CFSG.RankThree.PartTwo.KFacts

open CFSG.RankThree.PartTwo CFSG.GorensteinWalter
open CFSG.ComponentClassification.OuterAutomorphisms (Outer inner)

theorem isInnerAut_commutator_psl2_all {K : Type} [Field K] [Finite K]
    (σ τ : MulAut (PSL2 K)) : IsInnerAut (σ * τ * σ⁻¹ * τ⁻¹) := by
  have h := CFSG.LocalAnalysis.ComponentInitial.OuterDerived.outer_psl2_mul_comm K
    (σ : Outer (PSL2 K)) τ
  have h1 : ((σ * τ * σ⁻¹ * τ⁻¹ : MulAut (PSL2 K)) : Outer (PSL2 K)) = 1 := by
    rw [QuotientGroup.mk_mul, QuotientGroup.mk_mul, QuotientGroup.mk_mul, QuotientGroup.mk_inv,
      QuotientGroup.mk_inv, h]
    group
  have h2 : σ * τ * σ⁻¹ * τ⁻¹ ∈ inner (PSL2 K) := (QuotientGroup.eq_one_iff _).mp h1
  exact h2

theorem isInnerAut_commutator_of_mulEquiv_psl2_all {X : Type*} [Group X] {K : Type} [Field K]
    [Finite K] (e : X ≃* PSL2 K) (σ τ : MulAut X) : IsInnerAut (σ * τ * σ⁻¹ * τ⁻¹) := by
  rw [← isInnerAut_congr e, map_mul, map_mul, map_mul, map_inv, map_inv]
  exact isInnerAut_commutator_psl2_all _ _

theorem isInnerAut_commutator_of_isList1016_all {X : Type} [Group X] [Finite X]
    (hX : Sec9.IsList1016 X) (σ τ : MulAut X) : IsInnerAut (σ * τ * σ⁻¹ * τ⁻¹) := by
  by_cases hL3 : ∃ n : ℕ, 1 ≤ n ∧ Sec8.IsoLThreeMinusPi X 2 (3 * n)
  · obtain ⟨n, hn, hL⟩ := hL3
    exact isInnerAut_commutator_of_isoLThreeMinusPi hn hL σ τ
  · obtain ⟨K, _, _, -, -, ⟨e⟩⟩ := Sec11.exists_mulEquiv_psl2_of_isList1016 hX hL3
    exact isInnerAut_commutator_of_mulEquiv_psl2_all e σ τ

end CFSG.RankThree.PartTwo.KFacts
