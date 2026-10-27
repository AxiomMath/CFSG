module

public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.Eight105KRadDefs
public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.Eight102KFacts
import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.Eight105KRadU4
import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.Eight105KRadU5
import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.Eight105KRadTransport
import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.Eight105KTorusU4Lines
import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.Eight105KTorusU5Lines
import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.Eight102KTypesMap
import CFSG.Blueprint.SourceClassicalTransport
import CFSG.Models.PGL
public import CFSG.CGT.Timmesfeld75.Statements
public import CFSG.Foundations
public import CFSG.GroupTheory.LocalCores.Fitting
public import CFSG.LocalAnalysis.ComponentClassification.DisjointSolvableKernels
public import CFSG.LocalAnalysis.ComponentClassification.LBalanceComponentLifts
public import CFSG.LocalAnalysis.ComponentClassification.LayerMultiplication
public import CFSG.LocalAnalysis.ComponentClassification.MinimalBCenter
public import CFSG.LocalAnalysis.ComponentClassification.OrdinaryComponentJoins
public import CFSG.LocalAnalysis.ComponentClassification.TwoLayer
public import CFSG.LocalAnalysis.ComponentClassification.UniversalOrbitBlock
public import CFSG.LocalAnalysis.ComponentInitial.LayerComponentOrbit
public import CFSG.LocalAnalysis.RankThreeUC.Asc1930
public import CFSG.Quasithin.Background.A1bGroups
public import CFSG.RankThree.PartOne.S10.ThetaContract
public import CFSG.RankThree.PartOne.S12.InputsBase
import CFSG.LocalAnalysis.ComponentClassification.CatalogueBDerivedNormalSectionBound
import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalPointActionModels
import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalPointDataModelWitness
import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalSemilinearDataCompatibility
import CFSG.LocalAnalysis.ComponentInitial.OrthogonalFamilyLemmasFive
import CFSG.LocalAnalysis.ComponentInitial.OrthogonalFamilyLemmasSix
import CFSG.LocalAnalysis.ComponentInitial.OrthogonalReflectionSplitting
import CFSG.LocalAnalysis.ComponentInitial.OrthogonalStandardFormsRegular
import CFSG.LocalAnalysis.ComponentInitial.OrthogonalTailModelBorel
import CFSG.LocalAnalysis.ComponentInitial.OrthogonalTailPolar
import CFSG.LocalAnalysis.ComponentInitial.UnitaryHigherEvenOrthogonalModel
import TauCeti.LinearAlgebra.QuadraticForm.OrthogonalBasis

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.K105

open CFSG.Open Subgroup
open CFSG.LocalAnalysis.UniquenessCase.UC22
open CFSG.RankThree.PartTwo.Sec21.U4Lines (mapL embedOf torusD unitaryInvolution_rootsOfUnity
  card_rootsOfUnity_three nonempty_projSU_mulEquiv_SU card_galoisField_two_mul)
open CFSG.RankThree.PartOne.KFU (D8Mod d8Comb_four d8Vec_mem_SU)
open CFSG.LieType.BorelTits (unitaryInvolution)
open CFSG.LieType.Universal.Unitary (SU)

private theorem mapL_zpowers {G G' : Type} [Group G] [Group G'] {L : Subgroup G}
    {L' : Subgroup G'} (E : L ≃* L') (x : L) :
    mapL E (zpowers (x : G)) = zpowers ((E x : L') : G') := by
  have hsub : (zpowers (x : G)).subgroupOf L = zpowers x := by
    ext y
    rw [Subgroup.mem_subgroupOf, Subgroup.mem_zpowers_iff, Subgroup.mem_zpowers_iff]
    exact ⟨fun ⟨k, hk⟩ => ⟨k, Subtype.ext hk⟩, fun ⟨k, hk⟩ => ⟨k, congrArg Subtype.val hk⟩⟩
  rw [mapL, hsub, MonoidHom.map_zpowers]
  rfl

private theorem exists_of_mulEquiv {X G : Type} [Group X] [Finite X] [Group G] [Finite G]
    {L : Subgroup G} (φ : X ≃* L) {P : Subgroup G} {n : ℕ} {x : L}
    (hN : F08.NotationB8103 L P n (zpowers (x : G))) (hR : RadicalFacts L (zpowers x)) :
    ∃ S B : Subgroup X, IsPGroup 3 S ∧ ¬ 3 ∣ S.index ∧ F08.NotationB8103 ⊤ S n B ∧
      RadicalFacts X B := by
  have hN' := (KTypes.notationB8103_mapL_iff (φ.symm.trans topEquiv.symm)
    (Subgroup.zpowers_le.mpr x.2) (P := P)).mpr hN
  rw [mapL_zpowers] at hN'
  have hcard : Nat.card (zpowers x) = 3 := by
    rw [Nat.card_zpowers, ← Subgroup.orderOf_coe, ← Nat.card_zpowers]
    exact hN.1
  have hRX := RadicalFacts.of_mulEquiv φ.symm hcard hR
  rw [MonoidHom.map_zpowers] at hRX
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have h3 : IsPGroup 3 (zpowers (φ.symm x)) := IsPGroup.of_card (hN'.1.trans (pow_one 3).symm)
  obtain ⟨S, hS⟩ := h3.exists_le_sylow
  exact ⟨S, zpowers (φ.symm x), S.isPGroup', S.not_dvd_index, ⟨hN'.1, hS, hN'.2.2⟩, hRX⟩

private theorem exists_radicalFacts_of_isU4 {X : Type} [Group X] [Finite X] {n : ℕ}
    (hU4 : IsU4 X n) (hn : Even n) :
    ∃ S B : Subgroup X, IsPGroup 3 S ∧ ¬ 3 ∣ S.index ∧ F08.NotationB8103 ⊤ S n B ∧
      RadicalFacts X B := by
  have hn0 : 0 < n := (CFSG.Blueprint.LieModel.admissible hU4).2.1
  obtain ⟨e⟩ := CFSG.Blueprint.EvenSource.nonempty_mulEquiv_of_statedClassicalModel
    (CFSG.Blueprint.LieModel.statedClassicalModel hU4 (by decide))
    (CFSG.PGLModel.statedClassicalModel_of_mulEquiv_projSU
      (CFSG.Blueprint.LieModel.admissible hU4) (MulEquiv.refl _))
  obtain ⟨e₀⟩ := nonempty_projSU_mulEquiv_SU n hn0
  have hF := card_galoisField_two_mul n hn0
  have hμ := card_rootsOfUnity_three hn hF
  have : Nontrivial (rootsOfUnity 3 (GaloisField 2 (2 * n))) :=
    Finite.one_lt_card_iff_nontrivial.mp (by rw [hμ]; norm_num)
  obtain ⟨ω, hω⟩ := exists_ne (1 : rootsOfUnity 3 (GaloisField 2 (2 * n)))
  have hmem : torusD ((ω, ω) : D8Mod 3 (GaloisField 2 (2 * n))) ∈
      SU (unitaryInvolution (GaloisField 2 (2 * n)) 2 n) 4 :=
    d8Vec_mem_SU (Or.inl rfl) d8Comb_four _ (unitaryInvolution_rootsOfUnity hn) _
  exact exists_of_mulEquiv (e.trans e₀) (x := ⟨_, hmem⟩)
    ((u4_notationB_d8Tor_iff hn0 hn hF hω).mpr (Or.inl rfl)) (u4_radicalFacts hn0 hn hF hω rfl)

private theorem exists_radicalFacts_of_isU5 {X : Type} [Group X] [Finite X]
    (hU5 : IsU5 X 2) :
    ∃ S B : Subgroup X, IsPGroup 3 S ∧ ¬ 3 ∣ S.index ∧ F08.NotationB8103 ⊤ S 2 B ∧
      RadicalFacts X B := by
  obtain ⟨e⟩ := CFSG.Blueprint.EvenSource.nonempty_mulEquiv_of_statedClassicalModel
    (CFSG.Blueprint.LieModel.statedClassicalModel hU5 (by decide))
    (CFSG.PGLModel.statedClassicalModel_of_mulEquiv_projSU
      (CFSG.Blueprint.LieModel.admissible hU5) (MulEquiv.refl _))
  have hK := card_galoisField_two_mul 2 (by norm_num)
  have hμ := card_rootsOfUnity_three even_two hK
  have : Nontrivial (rootsOfUnity 3 (GaloisField 2 (2 * 2))) :=
    Finite.one_lt_card_iff_nontrivial.mp (by rw [hμ]; norm_num)
  obtain ⟨ω, hω⟩ := exists_ne (1 : rootsOfUnity 3 (GaloisField 2 (2 * 2)))
  have h1 : (ω : (GaloisField 2 (2 * 2))ˣ) ≠ 1 := fun h => hω (Subtype.ext h)
  have h3 : (ω : (GaloisField 2 (2 * 2))ˣ) ^ 3 = 1 := (mem_rootsOfUnity 3 _).mp ω.2
  have hfix := unitaryInvolution_rootsOfUnity even_two ω
  have hfix' : unitaryInvolution (GaloisField 2 (2 * 2)) 2 2
      (((ω : (GaloisField 2 (2 * 2))ˣ)⁻¹ : (GaloisField 2 (2 * 2))ˣ) :
        GaloisField 2 (2 * 2)) = ((ω : (GaloisField 2 (2 * 2))ˣ)⁻¹ : (GaloisField 2 (2 * 2))ˣ) := by
    rw [Units.val_inv_eq_inv_val, map_inv₀, hfix]
  let x₃ : ↥(SU (unitaryInvolution (GaloisField 2 (2 * 2)) 2 2) 5) :=
    ⟨_, CFSG.RankThree.PartOne.KFU.diagU_dvec5_mem_SU _ hfix hfix⟩
  let x₄ : ↥(SU (unitaryInvolution (GaloisField 2 (2 * 2)) 2 2) 5) :=
    ⟨_, CFSG.RankThree.PartOne.KFU.diagU_dvec5_mem_SU _ hfix hfix'⟩
  have hN := (u5_notationB_torus_iff hK h1 h3 (x₃ := x₃) (x₄ := x₄) rfl rfl).mpr (Or.inl rfl)
  have hR := RadicalFacts.of_mulEquiv topEquiv.symm hN.1 (u5_radicalFacts hK h1 h3 (x₃ := x₃) rfl)
  rw [MonoidHom.map_zpowers] at hR
  exact exists_of_mulEquiv ((e.trans (CFSG.PGLModel.projSUEquivStatedProj 5 2 2)).trans
    topEquiv.symm) (x := ⟨_, mem_top _⟩) hN hR

theorem exists_radicalFacts_of_isU45 {X : Type} [Group X] [Finite X] {n : ℕ} (hX : IsU45 X n) :
    ∃ S B : Subgroup X, IsPGroup 3 S ∧ ¬ 3 ∣ S.index ∧ F08.NotationB8103 ⊤ S n B ∧
      RadicalFacts X B := by
  rcases hX with ⟨hU5, rfl⟩ | ⟨hU4, hn⟩
  · exact exists_radicalFacts_of_isU5 hU5
  · exact exists_radicalFacts_of_isU4 hU4 hn

end CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.K105
