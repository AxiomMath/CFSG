module

public import CFSG.RankThree.GF2n.Stroth80.Conclusion
public import CFSG.LocalAnalysis.ComponentClassification.OuterAutomorphisms
import CFSG.RankThree.GF2n.Stroth80.ClassicalQuasisimple
import CFSG.RankThree.PartOne.KC.OrthogonalEvenMinusFourExtract
import CFSG.RankThree.PartOne.KC.OrthogonalEvenMinusFour
import CFSG.LocalAnalysis.ComponentClassification.RankTwoClassicalAS76aProofOMinusFacts
import CFSG.LocalAnalysis.ComponentClassification.CatalogueSchreierLinearTwoAllFields
import CFSG.Adapters.ProjectiveSpecialLinear
import CFSG.Open.StatedAPI
import CFSG.GroupTheory.ABGLocalTools.PStabilityQSL2
import CFSG.LocalAnalysis.ComponentClassification.CatalogueBDerivedNormalSectionBound
import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalFourSplitQuotient
import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalPointActionModels
import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalPointPlusBorelModel
import CFSG.LocalAnalysis.ComponentClassification.RankTwoClassicalAS76aProofOAut
import CFSG.LocalAnalysis.ComponentClassification.RankTwoClassicalAS76aProofOEightSwap
import CFSG.LocalAnalysis.ComponentClassification.RankTwoClassicalAS76aProofOKlein
import CFSG.LocalAnalysis.ComponentClassification.RankTwoClassicalAS76aProofOPlusLevi
import CFSG.LocalAnalysis.ComponentInitial.UnitaryHigherEvenOrthogonalModel
import CFSG.LocalAnalysis.SectionRank.EvenCover.Catalog
import CFSG.LocalAnalysis.SectionRank.LargeRee.SuzukiData
import CFSG.LocalAnalysis.SectionRank.OddCover.CatalogOdd
import CFSG.LocalAnalysis.SectionRank.SectionAssemblyBase
import CFSG.LocalAnalysis.SectionRank.Sporadic.J4LocalBase
import CFSG.LocalAnalysis.SectionRank.Sporadic.MathieuLocalBase
import CFSG.LocalAnalysis.SectionRank.TitsCover
import CFSG.Quasithin.Background.A3Components
import CFSG.Quasithin.Background.A3ComponentsAmbient
import CFSG.Quasithin.Background.G11Stmts
import CFSG.RankThree.GF2n.Stroth80.FrobClause
import CFSG.RankThree.GF2n.Stroth80.GlobalModel
import CFSG.RankThree.GF2n.Stroth80.Sec310Stmt
import CFSG.RankThree.GF2n.Stroth80.Sec39Rt
import CFSG.RankThree.GF2n.Stroth80.Sec4Stmt
import CFSG.RankThree.GF2n.Stroth80.Sec5Stmt
import CFSG.RankThree.GF2n.SupIndepDecomp
import CFSG.RankThree.GF2n.Tim79CentC
import CFSG.RankThree.GF2n.Tim79CentL
import CFSG.RankThree.GF2n.Tim79Mod
import CFSG.RankThree.PartOne.KC.OrthogonalAutSemilinearBridge
import CFSG.SignalizerFunctorTheorem.McBride.Prelim.Basic
import CFSG.SignalizerFunctorTheorem.Nonsolvable.SolComponent
import CFSG.Sporadic.J4.Simple
import CFSG.Sporadic.J4Base
import CFSG.Sporadic.Mathieu.M12
import CFSG.Sporadic.Mathieu.M24

public section

namespace CFSG.RankThree.GF2n.Stroth80

open CFSG.ComponentClassification.OuterAutomorphisms (Outer)

private noncomputable def sl2EquivPSL (F : Type) [Field F] [CharP F 2] :
    Matrix.SpecialLinearGroup (Fin 2) F ≃* Matrix.ProjectiveSpecialLinearGroup (Fin 2) F :=
  QuotientGroup.quotientBot.symm.trans
    (QuotientGroup.quotientMulEquivOfEq
      CFSG.RankThree.PartOne.KCOrthogonal.sl2_center_eq_bot.symm)

private theorem exists_ne_comm_of_equiv {G H : Type} [Group G] [Group H] (e : G ≃* H)
    (h : ¬ ∀ x y : H, x * y = y * x) : ∃ x y : G, x * y ≠ y * x := by
  by_contra hc
  push Not at hc
  apply h
  intro x y
  have h1 := congrArg e (hc (e.symm x) (e.symm y))
  simpa only [map_mul, MulEquiv.apply_symm_apply] using h1

private theorem charTwo_of_card_two_pow (K : Type) [Field K] [Finite K] {a : ℕ} (ha2 : 2 ≤ a)
    (hKa : Nat.card K = 2 ^ a) : CharP K 2 ∧ 4 ≤ Nat.card K := by
  refine ⟨CFSG.ABGLocalTools.SL2Facts.charP_of_card_eq_prime_pow Nat.prime_two hKa, ?_⟩
  rw [hKa]
  calc (4 : ℕ) = 2 ^ 2 := by norm_num
    _ ≤ 2 ^ a := Nat.pow_le_pow_right (by norm_num) ha2

private theorem sl2_not_commutative {F : Type} [Field F] [CharP F 2] (h4 : 4 ≤ Nat.card F) :
    ¬ ∀ x y : Matrix.SpecialLinearGroup (Fin 2) F, x * y = y * x := by
  intro hc
  haveI : IsSimpleGroup (Matrix.SpecialLinearGroup (Fin 2) F) :=
    CFSG.RankThree.PartOne.KCOrthogonal.sl2_isSimpleGroup h4
  haveI : Group.IsPerfect (Matrix.SpecialLinearGroup (Fin 2) F) :=
    CFSG.RankThree.PartOne.KCOrthogonal.sl2_isPerfect h4
  haveI : IsMulCommutative (Matrix.SpecialLinearGroup (Fin 2) F) := ⟨⟨fun a b => hc a b⟩⟩
  exact Group.IsPerfect.not_isMulCommutative (Matrix.SpecialLinearGroup (Fin 2) F) inferInstance

theorem isSLModel_two_facts {q : ℕ} {X : Type} [Group X] (hq : ∃ a : ℕ, 2 ≤ a ∧ q = 2 ^ a)
    (h : IsSLModel 2 q X) :
    IsSimpleGroup X ∧ (∃ x y : X, x * y ≠ y * x) ∧ Group.IsSolvable (Outer X) ∧
      Nat.card X = q * (q ^ 2 - 1) := by
  obtain ⟨K, _, _, hKq, ⟨eX⟩⟩ := h
  obtain ⟨a, ha2, ha⟩ := hq
  obtain ⟨hchar, h4⟩ := charTwo_of_card_two_pow K ha2 (hKq.trans ha)
  haveI := hchar
  let eSL : X ≃* Matrix.SpecialLinearGroup (Fin 2) K :=
    eX.trans (CFSG.Assembly.LowTwoRank.specialLinearGroupEquivStatedSL 2 K).symm
  haveI : IsSimpleGroup (Matrix.SpecialLinearGroup (Fin 2) K) :=
    CFSG.RankThree.PartOne.KCOrthogonal.sl2_isSimpleGroup h4
  refine ⟨eSL.isSimpleGroup, exists_ne_comm_of_equiv eSL (sl2_not_commutative h4), ?_, ?_⟩
  · exact CFSG.ComponentClassification.CatalogueSchreierLinearTwo.outer_solvable_of_equiv K
      (eSL.trans (sl2EquivPSL K))
  · rw [Nat.card_congr eX.toEquiv, CFSG.Open.StatedAPI.card_statedSL_two, hKq]

theorem isOmegaMinus_two_facts {q : ℕ} {X : Type} [Group X] (hq : ∃ a : ℕ, 2 ≤ a ∧ q = 2 ^ a)
    (h : IsOmegaMinus 2 q X) :
    IsSimpleGroup X ∧ (∃ x y : X, x * y ≠ y * x) ∧ Group.IsSolvable (Outer X) ∧
      Nat.card X = q ^ 2 * (q ^ 4 - 1) := by
  obtain ⟨K, _, _, hKq, b, c, hirr, ⟨eX⟩⟩ := h
  obtain ⟨a, ha2, ha⟩ := hq
  obtain ⟨hchar, -⟩ := charTwo_of_card_two_pow K ha2 (hKq.trans ha)
  haveI := hchar
  obtain ⟨hsimp, -, hna⟩ :=
    CFSG.ComponentClassification.RankTwoClassical.isSimpleGroup_statedOmega_quadMinus_small
      (n := 2) (Or.inl rfl) hirr
  haveI := hsimp
  obtain ⟨E, _, _, D, _, ρ, -, -, hinj, -, hrange, -, -, -, hcard, -, -, -⟩ :=
    CFSG.RankThree.PartOne.even_minus_four_actual_derived_extraction
      (CFSG.LieType.Universal.Spin.quadMinus 2 K b c)
      (CFSG.LieType.Universal.Spin.nondegenerate_polarBilin_quadMinus_of_finite 2 K hirr)
      (by rw [Module.finrank_fintype_fun_eq_card]; simp)
      (fun U hU =>
        CFSG.ComponentClassification.RankTwoClassical.exists_ne_zero_of_finrank_eq_quadMinus
          (n := 2) (by norm_num) hirr U (by rw [hU, Module.finrank_fintype_fun_eq_card]; simp))
  haveI : Finite E := D.finite_E
  haveI : CharP E 2 := CFSG.RankThree.PartOne.KCOrthogonal.charP_two_of_algebra (K := K)
  let eρ : X ≃* ↥ρ.range := eX.trans
    ((CFSG.ComponentClassification.RankTwoClassical.statedOmegaEquivCommutator
      (CFSG.LieType.Universal.Spin.quadMinus 2 K b c)
      (CFSG.LieType.Universal.Spin.coe_quadMinus 2 K b c)).trans
      (MulEquiv.subgroupCongr hrange))
  let eSL : X ≃* Matrix.SpecialLinearGroup (Fin 2) E :=
    eρ.trans (MonoidHom.ofInjective hinj).symm
  refine ⟨eX.isSimpleGroup, exists_ne_comm_of_equiv eX hna, ?_, ?_⟩
  · exact CFSG.ComponentClassification.CatalogueSchreierLinearTwo.outer_solvable_of_equiv E
      (eSL.trans (sl2EquivPSL E))
  · rw [Nat.card_congr eρ.toEquiv, hcard, hKq]

theorem isOmegaPlus_two_split {q : ℕ} {X : Type} [Group X] (hq : ∃ a : ℕ, 2 ≤ a ∧ q = 2 ^ a)
    (h : IsOmegaPlus 2 q X) :
    ∃ (A B : Type) (_ : Group A) (_ : Group B), IsSLModel 2 q A ∧ IsSLModel 2 q B ∧
      Nonempty (X ≃* A × B) := by
  obtain ⟨K, _, _, hKq, ⟨eX⟩⟩ := h
  obtain ⟨a, ha2, ha⟩ := hq
  obtain ⟨hchar, h4⟩ := charTwo_of_card_two_pow K ha2 (hKq.trans ha)
  haveI := hchar
  obtain ⟨eP⟩ := statedOmega_plus_four_nonempty_equiv K h4
  exact ⟨↥(CFSG.Open.StatedSL 2 K), ↥(CFSG.Open.StatedSL 2 K), inferInstance, inferInstance,
    ⟨K, inferInstance, inferInstance, hKq, ⟨MulEquiv.refl _⟩⟩,
    ⟨K, inferInstance, inferInstance, hKq, ⟨MulEquiv.refl _⟩⟩, ⟨eX.trans eP⟩⟩

end CFSG.RankThree.GF2n.Stroth80
