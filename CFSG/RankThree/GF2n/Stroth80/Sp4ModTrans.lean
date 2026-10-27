module

public import CFSG.RankThree.GF2n.Stroth80.IrrSectionCard
public import CFSG.Quasithin.Vol2.Ch3E215MSp4A
public import CFSG.RankThree.GF2n.Stroth80.ClassicalQuasisimple
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCatalogSpExterior
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.X7Basic
public import CFSG.Quasithin.Background.G11Defs
public import CFSG.Open.StatedDefs
public import Mathlib.Algebra.Group.End
public import Mathlib.Algebra.Module.ZMod
public import Mathlib.FieldTheory.Finite.Basic
public import Mathlib.FieldTheory.Finiteness
public import Mathlib.GroupTheory.IsPerfect
public import Mathlib.SetTheory.Cardinal.Finite
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBDerivedNormalSectionBound
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBHeldSmallCorePrimeCore
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalDescentEndpoint
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalFiveStructure
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalFixedTransfer
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalPointActionModels
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalPointPlusBorelModel
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalScalarSquareField
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalScalarSquareStructure
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalSixComponentsCover
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalSixModelGeometry
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalTraceZeroCoordinates
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBProjectiveInvolutionStructure
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBSymplecticBField
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBSymplecticBLinear
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBSymplecticRepresentationOdd
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueKProperGroups
public import CFSG.LocalAnalysis.ComponentClassification.RankTwoClassicalAS76aProofOAut
public import CFSG.LocalAnalysis.ComponentClassification.RankTwoClassicalAS76aProofOEightSwap
public import CFSG.LocalAnalysis.ComponentClassification.RankTwoClassicalAS76aProofOKlein
public import CFSG.LocalAnalysis.ComponentClassification.RankTwoClassicalAS76aProofOPlusLevi
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCatalogSpExclusion
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCatalogSpWedge
public import CFSG.LocalAnalysis.ComponentInitial.UnitaryHigherEvenOrthogonalModel
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.Vol2NativeBasic
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.L238BridgeAlt57SL
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.L238BridgeAlt57Sp4
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.LayerFinal
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.LiftSaturate
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.SL2ModulesAlt5Split
public import CFSG.Quasithin.Background.A1cModuleCoprime
public import CFSG.Quasithin.Background.A3Structure312Facts
public import CFSG.Quasithin.Background.G11Stmts
public import CFSG.Quasithin.Vol2.Ch1Local
public import CFSG.RankThree.Asc83Table.PermTables
public import CFSG.RankThree.GF2n.Stroth80.FrobClause
public import CFSG.RankThree.GF2n.Stroth80.GlobalModel
public import CFSG.RankThree.GF2n.Stroth80.Sec310Stmt
public import CFSG.RankThree.GF2n.Stroth80.Sec39Rt
public import CFSG.RankThree.GF2n.Stroth80.Sec4Stmt
public import CFSG.RankThree.GF2n.Stroth80.Sec5Stmt
public import CFSG.RankThree.GF2n.SupIndepDecomp
public import CFSG.RankThree.GF2n.Tim79CentC
public import CFSG.RankThree.GF2n.Tim79CentL
public import CFSG.RankThree.GF2n.Tim79Mod
public import CFSG.RankThree.PartOne.KC.OrthogonalAutSemilinearBridge
public import CFSG.SignalizerFunctorTheorem.McBride.Prelim.Basic
public import CFSG.SignalizerFunctorTheorem.Nonsolvable.SolComponent
public import CFSG.Sporadic.Schreier.M11
public import CFSG.Sporadic.Schreier.M22
public import Certificates.Certificate8026Base
public import TauCeti.LinearAlgebra.Dimension.IsQuadraticExtension

public section

namespace CFSG.RankThree.GF2n.Stroth80

open CFSG.Open
open CFSG.ComponentClassification.UnbalancedCatalog.SpChain

@[expose] def sp4AddAutLin (Y : Type) [AddCommGroup Y] [Module (ZMod 2) Y] :
    Multiplicative (AddAut Y) →* (Y ≃ₗ[ZMod 2] Y) where
  toFun e :=
    { toFun := fun y => e.toAdd y
      invFun := fun y => (AddEquiv.symm e.toAdd) y
      map_add' := fun a b => map_add e.toAdd a b
      map_smul' := fun c x => ZMod.map_smul e.toAdd c x
      left_inv := fun y => AddEquiv.symm_apply_apply e.toAdd y
      right_inv := fun y => AddEquiv.apply_symm_apply e.toAdd y }
  map_one' := LinearEquiv.ext fun _ => rfl
  map_mul' _ _ := LinearEquiv.ext fun _ => rfl

theorem sp4AddAutLin_injective (Y : Type) [AddCommGroup Y] [Module (ZMod 2) Y] :
    Function.Injective (sp4AddAutLin Y) := by
  intro a b h
  apply Multiplicative.toAdd.injective
  apply AddEquiv.ext
  intro y
  exact congrArg (fun L : Y ≃ₗ[ZMod 2] Y => L y) h

theorem sp4_card_pow (K : Type) [Field K] [Finite K] [CharP K 2] :
    ∃ f : ℕ, 1 ≤ f ∧ Nat.card K = 2 ^ f := by
  letI : Fintype K := Fintype.ofFinite K
  obtain ⟨n, -, hK⟩ := FiniteField.card K 2
  exact ⟨(n : ℕ), n.pos, by rw [Nat.card_eq_fintype_card, hK]⟩

theorem sp4_repOf_isIrreducible {K : Type} [Field K] [CharP K 2] [Fintype K] {M : Type}
    [AddCommGroup M] [Module (ZMod 2) M] [Finite M] (σ : antiSp K →* (M ≃ₗ[ZMod 2] M))
    (hσ : CFSG.Quasithin.G11.IsIrr σ.range ⊤) :
    (CFSG.Quasithin.B42Sp4.repOf σ).IsIrreducible := by
  obtain ⟨-, hsec⟩ := hσ
  obtain ⟨hlt, hJ⟩ := hsec
  have hnt : Nontrivial M := by
    by_contra hM
    rw [not_nontrivial_iff_subsingleton] at hM
    have htop : (⊤ : Submodule (ZMod 2) M) = ⊥ := by
      rw [eq_bot_iff]
      intro x _
      rw [Submodule.mem_bot]
      exact Subsingleton.elim x 0
    exact hlt.ne' htop
  refine (CFSG.QuasithinUnique.Setup.X7.isIrreducible_iff _).mpr ⟨hnt, fun U hU => ?_⟩
  have hUinv : CFSG.Quasithin.G11.Invariant σ.range U := by
    intro k hk u hu
    obtain ⟨g, rfl⟩ := MonoidHom.mem_range.mp hk
    exact hU g u hu
  exact hJ U hUinv bot_le le_top

theorem sp4_exists_repOf_ne_one {K : Type} [Field K] [CharP K 2] [Fintype K] {M : Type}
    [AddCommGroup M] [Module (ZMod 2) M] [Finite M] (σ : antiSp K →* (M ≃ₗ[ZMod 2] M))
    (h : ∃ g, σ g ≠ 1) : ∃ g, CFSG.Quasithin.B42Sp4.repOf σ g ≠ 1 := by
  obtain ⟨g, hg⟩ := h
  refine ⟨g, fun h1 => hg ?_⟩
  have h2 : σ g = σ 1 :=
    LinearEquiv.toLinearMap_injective (h1.trans (map_one (CFSG.Quasithin.B42Sp4.repOf σ)).symm)
  exact h2.trans (map_one σ)

theorem sp4ModTransStatement_holds :
    ∀ (K : Type) [Field K] [Finite K] [CharP K 2], 4 ≤ Nat.card K →
    ∀ (Y : Type) [AddCommGroup Y] [Finite Y], (∀ y : Y, y + y = 0) →
      Nat.card Y = Nat.card K ^ 4 → ∀ π : ↥(StatedSp 2 K) →* Multiplicative (AddAut Y), π ≠ 1 →
      ∀ y y' : Y, y ≠ 0 → y' ≠ 0 → ∃ g, π g y = y' := by
  intro K _ _ _ h4 Y _ _ hY2 hYcard π hπ y y' hy hy'
  obtain ⟨f, hf, hKc⟩ := sp4_card_pow K
  letI : Fintype K := Fintype.ofFinite K
  have hF : Fintype.card K = 2 ^ f := by rw [← Nat.card_eq_fintype_card]; exact hKc
  have hP : Group.IsPerfect ↥(StatedSp 2 K) :=
    (statedSp_quasisimple_of_card 2 K (by norm_num) h4).1
  have hG : Group.IsPerfect ↥(antiSp K) := by
    haveI := hP
    exact Group.IsPerfect.ofSurjective (f := (antiSpEquiv K).symm.toMonoidHom)
      (antiSpEquiv K).symm.surjective
  have h2Y : ∀ y : Y, (2 : ℕ) • y = 0 := fun y => by rw [two_nsmul]; exact hY2 y
  letI : Module (ZMod 2) Y := AddCommGroup.zmodModule h2Y
  haveI : Module.Finite (ZMod 2) Y := Module.Finite.of_finite
  have hYcard2 : Nat.card Y = 2 ^ (4 * f) := by
    rw [hYcard, hKc, ← pow_mul, Nat.mul_comm]
  have hYfin : Module.finrank (ZMod 2) Y = 4 * f := by
    have h := Module.natCard_eq_pow_finrank (K := ZMod 2) (V := Y)
    rw [Nat.card_zmod, hYcard2] at h
    exact (Nat.pow_right_injective (le_refl 2) h).symm
  let ρ : ↥(antiSp K) →* (Y ≃ₗ[ZMod 2] Y) :=
    (sp4AddAutLin Y).comp (π.comp (antiSpEquiv K).toMonoidHom)
  have hρnt : ∃ g, ρ g ≠ 1 := by
    by_contra hall
    push Not at hall
    apply hπ
    refine MonoidHom.ext fun h => ?_
    obtain ⟨g, rfl⟩ := (antiSpEquiv K).surjective h
    have h1 : sp4AddAutLin Y (π (antiSpEquiv K g)) = 1 := hall g
    rw [MonoidHom.one_apply]
    exact sp4AddAutLin_injective Y (h1.trans (map_one (sp4AddAutLin Y)).symm)
  obtain ⟨Y', _, _, _, σ, hle, hσnt, hσirr, hfull⟩ :=
    exists_irr_section_card hG (4 * f) Y ρ hYfin hρnt
  haveI : Module.Finite (ZMod 2) Y' := Module.Finite.of_finite
  have hY'card : Nat.card Y' ≤ 2 ^ (4 * f) := by
    have h := Module.natCard_eq_pow_finrank (K := ZMod 2) (V := Y')
    rw [Nat.card_zmod] at h
    rw [h]
    exact Nat.pow_le_pow_right (by norm_num) hle
  have hY'fin : Module.finrank (ZMod 2) Y' = 4 * f := by
    haveI : Fact (CFSG.Quasithin.B42Sp4.repOf σ).IsIrreducible :=
      ⟨sp4_repOf_isIrreducible σ hσirr⟩
    have hσnt' := sp4_exists_repOf_ne_one σ hσnt
    have hdim := CFSG.Quasithin.Ch3E215M.Sp4.finrank_eq_four_of_card_le hF hf σ hσnt' hY'card
    obtain ⟨i, φ, -⟩ := CFSG.Quasithin.B42Sp4.exists_natural_of_four hF hf σ hσnt' hdim
    have h4fin : Nat.card (Fin 4) = 4 := by simp
    have hnat : Nat.card Y' = 2 ^ (4 * f) := by
      rw [Nat.card_congr φ.toEquiv, Nat.card_fun, hKc, h4fin, ← pow_mul, Nat.mul_comm]
    have h := Module.natCard_eq_pow_finrank (K := ZMod 2) (V := Y')
    rw [Nat.card_zmod, hnat] at h
    exact (Nat.pow_right_injective (le_refl 2) h).symm
  haveI : Fact (CFSG.Quasithin.B42Sp4.repOf ρ).IsIrreducible :=
    ⟨sp4_repOf_isIrreducible ρ (hfull hY'fin)⟩
  obtain ⟨g, hg⟩ := CFSG.Quasithin.Ch3E215M.Sp4.exists_apply_eq_of_card_le hF hf ρ
    (sp4_exists_repOf_ne_one ρ hρnt) hYcard2.le hy hy'
  exact ⟨antiSpEquiv K g, hg⟩

end CFSG.RankThree.GF2n.Stroth80
