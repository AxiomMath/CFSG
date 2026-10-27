module

public import CFSG.LocalAnalysis.StandardType.GGKD2ConnectedPieces1615
public import CFSG.ClassicalInvolution.SmallCases.NobqL2
public import CFSG.LocalAnalysis.GLTheoremA.CatA.T1428InnDerived

public section

namespace CFSG.StandardType.KD2Pieces1615

open CFSG CFSG.Assembly CFSG.StandardType S2MathAs3_1615

theorem a1EightInnAutDerived_holds : A1EightInnAutDerived := by
  intro Q _ hlab β hβ
  unfold GGHasLabel at hlab
  dsimp only [LargeEvenRawDatum, LargeEvenRecipeLinear] at hlab
  obtain ⟨K, hKfield, hKfinite, hKcard, ⟨e₀⟩⟩ := hlab
  letI : Field K := hKfield
  letI : Finite K := hKfinite
  haveI : CharP K 2 :=
    CFSG.LocalAnalysis.ComponentInitial.finite_field_prime_power_characteristic
      Nat.prime_two (by omega) hKcard
  let e₁ := TypeA.recipeEquiv 2 K
  let e₂ := QuotientGroup.quotientMulEquivOfEq
    (CFSG.LocalAnalysis.ComponentInitial.LinearFlag.scalars_eq_center 2 K).symm
  let e : Q ≃* CFSG.GorensteinWalter.PSL2 K := e₀.trans (e₁.trans e₂.symm)
  haveI : IsCyclic (CFSG.ComponentClassification.OuterAutomorphisms.Outer
      (CFSG.GorensteinWalter.PSL2 K)) :=
    CFSG.ClassicalInvolution.Nobq.isCyclic_outer_psl2_of_charTwo K
  haveI : IsMulCommutative (CFSG.ComponentClassification.OuterAutomorphisms.Outer
      (CFSG.GorensteinWalter.PSL2 K)) := IsCyclic.isMulCommutative
  have hcommK : ∀ a b : CFSG.ComponentClassification.OuterAutomorphisms.Outer
      (CFSG.GorensteinWalter.PSL2 K), a * b = b * a :=
    fun a b => mul_comm' a b
  have hcomm : ∀ a b : CFSG.ComponentClassification.OuterAutomorphisms.Outer Q, a * b = b * a := by
    intro a b
    apply (CFSG.ComponentClassification.OuterAutomorphisms.equivalence e).injective
    rw [map_mul, map_mul]
    exact hcommK _ _
  have hder : CFSG.ComponentClassification.OuterAutomorphisms.innAutDerived Q =
      CFSG.ComponentClassification.OuterAutomorphisms.inner Q :=
    CFSG.LocalAnalysis.GLTheoremA.innAutDerived_eq_inner_of_commutative_outer hcomm
  rw [hder] at hβ
  unfold CFSG.ComponentClassification.OuterAutomorphisms.inner at hβ
  rw [MonoidHom.mem_range] at hβ
  obtain ⟨y, hy⟩ := hβ
  refine ⟨y, fun q => ?_⟩
  rw [← hy]
  simp [MulAut.conj_apply]

end CFSG.StandardType.KD2Pieces1615

end
