module

public import CFSG.LocalAnalysis.StandardType.TwE6MaxEleven.Defs
public import CFSG.LieType.Chevalley.TwistedE6FieldTwoCyclicKernel
public import CFSG.LieType.Chevalley.C2E6NativeF4Building
public import CFSG.Monster.B.E6.GStarStructure
public import CFSG.Monster.Existence.StdOdd.Cert.TableOne
public import CFSG.Monster.Existence.StdOdd.Cert.ThreeLocal
public import CFSG.Monster.Existence.StdOdd.Cert.Cent17
public import CFSG.Monster.Existence.StdOdd.Cert.Reps
public import CFSG.Assembly.OrderReductions.InvertedSubgroup
public import CFSG.Assembly.OrderReductions.OddInversion
public import CFSG.GroupTheory.LocalCores.Fitting
public import CFSG.LieType.Chevalley.C2E6A5ExteriorCubeModel
public import CFSG.LieType.Chevalley.C2E6D4NaturalOrthogonal
public import CFSG.LieType.Chevalley.C2E6FourthResidueMinusEight
public import CFSG.LieType.Chevalley.E6GraphHighestRootNormalizer
public import CFSG.LieType.Chevalley.SimplyLacedFieldTwoCover
public import CFSG.LieType.Chevalley.TwistedE6FieldTwoRelativeData
public import CFSG.LieType.Steinberg.Classical.SpinFrame
public import CFSG.LieType.Steinberg.Families
public import CFSG.LieType.Universal.Spin.Generation
public import CFSG.LieType.Universal.Spin.OddCT
public import CFSG.LieType.Universal.Spin.PlusCT
public import CFSG.LieType.Universal.Spin.Structure
public import CFSG.LieType.Universal.SpinOmega
public import CFSG.LieType.Universal.Unitary
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBDerivedNormalSectionBound
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalPointActionModels
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalPointDataModelWitness
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalSemilinearDataCompatibility
public import CFSG.LocalAnalysis.ComponentInitial.LinearHigherSubspaceIndex
public import CFSG.LocalAnalysis.ComponentInitial.LinearInvolutionFixedField
public import CFSG.LocalAnalysis.ComponentInitial.OrthogonalFamilyLemmasFive
public import CFSG.LocalAnalysis.ComponentInitial.OrthogonalReflectionSplitting
public import CFSG.LocalAnalysis.ComponentInitial.OrthogonalStandardFormsRegular
public import CFSG.LocalAnalysis.ComponentInitial.OrthogonalTailModelBorel
public import CFSG.LocalAnalysis.ComponentInitial.OrthogonalTailPolar
public import CFSG.LocalAnalysis.SectionRank.ClassicalOdd
public import CFSG.LocalAnalysis.SectionRank.EvenCover.LinearStep
public import CFSG.LocalAnalysis.SectionRank.SporadicCover
public import CFSG.Sporadic.M23.M23Group
public import CFSG.Sporadic.Th.F2Spec
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Defs
public import TauCeti.LinearAlgebra.CliffordAlgebra.Monomials

public section

namespace CFSG.StandardType.TwE6MaxEleven

open CFSG.Blueprint CFSG.LieType.Chevalley CFSG.LieType.Chevalley.C2E6Std
open CFSG.Monster.Existence.StdOdd CFSG.Monster.Existence.StdOdd.Cert
open Subgroup

variable {X : Type} [Group X] [Finite X]


private theorem nonempty_mulEquiv_stdGroup_of_model
    (h : ChevalleyExceptionalModel X .twistedE6 2 1) : Nonempty (X ≃* stdGroup) := by
  obtain ⟨K, _, _, σ, hcard, hσ, ⟨e⟩⟩ := exists_mulEquiv_graphFixedRootGroup_E6 h
  have h4 : Nat.card K = 4 := by
    rw [hcard]
    norm_num
  obtain ⟨e'⟩ := nonempty_mulEquiv_stdGroup_of_card_eq_four h4 σ.toRingHom fun c => by
    simpa using hσ c
  exact ⟨e.trans e'⟩

private theorem card_centralizer_map {Y : Type} [Group Y] (e : X ≃* Y) (x : X) :
    Nat.card (Subgroup.centralizer ({e x} : Set Y)) =
      Nat.card (Subgroup.centralizer ({x} : Set X)) := by
  have hmap : (Subgroup.centralizer ({x} : Set X)).map e.toMonoidHom =
      Subgroup.centralizer ({e x} : Set Y) := by
    refine le_antisymm ?_ ?_
    · simpa using Subgroup.map_centralizer_le_centralizer_image ({x} : Set X) e.toMonoidHom
    · rintro y hy
      refine ⟨e.symm y, ?_, e.apply_symm_apply y⟩
      rw [Subgroup.mem_centralizer_iff] at hy
      intro z hz
      rw [Set.mem_singleton_iff] at hz
      rw [hz]
      apply e.injective
      rw [map_mul, map_mul, e.apply_symm_apply]
      exact hy (e x) (Set.mem_singleton (e x))
  calc Nat.card (Subgroup.centralizer ({e x} : Set Y))
      = Nat.card ((Subgroup.centralizer ({x} : Set X)).map e.toMonoidHom) := by rw [hmap]
    _ = Nat.card (Subgroup.centralizer ({x} : Set X)) :=
        (Nat.card_congr (Subgroup.equivMapOfInjective _ _ e.injective).toEquiv).symm

private theorem card_map_mulEquiv {Y : Type} [Group Y] (e : X ≃* Y) (A : Subgroup X) :
    Nat.card (A.map e.toMonoidHom) = Nat.card A :=
  (Nat.card_congr (Subgroup.equivMapOfInjective A e.toMonoidHom e.injective).toEquiv).symm

private theorem mem_map_normalizer {Y : Type} [Group Y] (e : X ≃* Y) {A : Subgroup X}
    {g : X} (hg : g ∈ Subgroup.normalizer (A : Set X)) :
    e g ∈ Subgroup.normalizer ((A.map e.toMonoidHom : Subgroup Y) : Set Y) := by
  have h : e g ∈ (Subgroup.normalizer (A : Set X)).map e.toMonoidHom := ⟨g, hg, rfl⟩
  rwa [Subgroup.map_equiv_normalizer_eq A e] at h

theorem card_of_model (h : ChevalleyExceptionalModel X .twistedE6 2 1) :
    Nat.card X = 2 ^ 36 * 3 ^ 9 * 5 ^ 2 * 7 ^ 2 * 11 * 13 * 17 * 19 := by
  obtain ⟨e⟩ := nonempty_mulEquiv_stdGroup_of_model h
  rw [Nat.card_congr e.toEquiv, card_stdGroup]
  norm_num

theorem isSimpleGroup_of_model (h : ChevalleyExceptionalModel X .twistedE6 2 1) :
    IsSimpleGroup X := by
  obtain ⟨e⟩ := nonempty_mulEquiv_stdGroup_of_model h
  haveI : IsSimpleGroup stdGroup := CFSG.Monster.B.E6.stdGroup_isSimpleGroup
  exact e.isSimpleGroup

theorem c11_of_model (h : ChevalleyExceptionalModel X .twistedE6 2 1) :
    ∀ t : X, orderOf t = 11 →
      Nat.card (Subgroup.centralizer ({t} : Set X)) ∣ 2 * 3 * 11 := by
  intro t ht
  obtain ⟨e⟩ := nonempty_mulEquiv_stdGroup_of_model h
  have hstd : Nat.card (Subgroup.centralizer ({e t} : Set stdGroup)) ∣ 2 * 3 * 11 :=
    centralizerFacts_std.c11 (e t) (by rw [MulEquiv.orderOf_eq, ht])
  rwa [card_centralizer_map e t] at hstd

theorem c17_of_model (h : ChevalleyExceptionalModel X .twistedE6 2 1) :
    ∀ s : X, orderOf s = 17 →
      Nat.card (Subgroup.centralizer ({s} : Set X)) = 17 := by
  intro s hs
  haveI : Fact (Nat.Prime 17) := ⟨by norm_num⟩
  obtain ⟨e⟩ := nonempty_mulEquiv_stdGroup_of_model h
  have hp2 : ¬ 17 ^ 2 ∣ Nat.card X := by
    rw [card_of_model h]
    norm_num
  have hx : orderOf (e.symm rep17) = 17 := by
    rw [MulEquiv.orderOf_eq, orderOf_rep17]
  have hxcard : Nat.card (Subgroup.centralizer ({e.symm rep17} : Set X)) = 17 := by
    rw [← card_centralizer_map e (e.symm rep17), e.apply_symm_apply, card_centralizer_rep17]
  rw [card_centralizer_eq_of_sylow_prime hp2 hx hs, hxcard]

theorem rank3_of_model (h : ChevalleyExceptionalModel X .twistedE6 2 1) :
    ∀ A : Subgroup X, (∀ a ∈ A, a ^ 3 = 1) →
      (∀ a ∈ A, ∀ b ∈ A, a * b = b * a) → Nat.card A ≤ 3 ^ 5 := by
  intro A h3 hc
  obtain ⟨e⟩ := nonempty_mulEquiv_stdGroup_of_model h
  set B : Subgroup stdGroup := A.map e.toMonoidHom with hB
  have hB3 : ∀ a ∈ B, a ^ 3 = 1 := by
    rintro _ ⟨a, ha, rfl⟩
    rw [← map_pow, h3 a ha, map_one]
  have hBc : ∀ a ∈ B, ∀ b ∈ B, a * b = b * a := by
    rintro _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩
    rw [← map_mul, ← map_mul, hc a ha b hb]
  have hle := (threeLocalFacts_std centralizerFacts_std).rank3 B hB3 hBc
  rwa [show Nat.card B = Nat.card A from card_map_mulEquiv e A] at hle

theorem elem11_of_model (h : ChevalleyExceptionalModel X .twistedE6 2 1) :
    ∀ A : Subgroup X, (∀ a ∈ A, a ^ 3 = 1) →
      (∀ a ∈ A, ∀ b ∈ A, a * b = b * a) → Nat.card A = 3 ^ 5 →
      ∀ g ∈ Subgroup.normalizer (A : Set X), orderOf g ≠ 11 := by
  intro A h3 hc hA g hg hg11
  obtain ⟨e⟩ := nonempty_mulEquiv_stdGroup_of_model h
  set B : Subgroup stdGroup := A.map e.toMonoidHom with hB
  have hB3 : ∀ a ∈ B, a ^ 3 = 1 := by
    rintro _ ⟨a, ha, rfl⟩
    rw [← map_pow, h3 a ha, map_one]
  have hBc : ∀ a ∈ B, ∀ b ∈ B, a * b = b * a := by
    rintro _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩
    rw [← map_mul, ← map_mul, hc a ha b hb]
  have hBcard : Nat.card B = 3 ^ 5 := by
    rw [hB, card_map_mulEquiv e A, hA]
  have hgn : e g ∈ Subgroup.normalizer (B : Set stdGroup) := by
    rw [hB]
    exact mem_map_normalizer e hg
  have hgord : orderOf (e g) = 11 := by rw [MulEquiv.orderOf_eq, hg11]
  exact (threeLocalFacts_std centralizerFacts_std).elem11 B hB3 hBc hBcard (e g) hgn hgord

end CFSG.StandardType.TwE6MaxEleven
