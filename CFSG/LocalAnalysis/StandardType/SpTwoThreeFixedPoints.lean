module

public import CFSG.LocalAnalysis.StandardType.GGKGroupFusionSeitzExcGenuine
public import CFSG.LieType.SeitzGeneration.SpPlaneThreeF2Exceptional
public import CFSG.LieType.SeitzGeneration.OuterSpData
public import CFSG.RankThree.PartTwo.KFacts.AutPSp
public import CFSG.LieType.Steinberg.CentralExt.F4E8Multiplier
public import CFSG.LieType.Steinberg.CentralExt.PSpEvenMultiplier
public import CFSG.LieType.Steinberg.CentralExt.PSpMultiplier
public import CFSG.LinearAlgebra.SL2MinimalFaithfulMatrix
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBDerivedNormalSectionBound
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBHeldSmallCorePrimeCore
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBHigherLinearFieldDeterminant
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
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCatalogSpExclusion
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCatalogSpSuzukiCentralizer
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCatalogSpWedge
public import CFSG.LocalAnalysis.ComponentInitial.LinearInvolutionFixedField
public import CFSG.LocalAnalysis.ComponentInitial.OrthogonalFamilyLemmasFive
public import CFSG.LocalAnalysis.ComponentInitial.OrthogonalFamilyLemmasSix
public import CFSG.LocalAnalysis.ComponentInitial.OrthogonalReflectionSplitting
public import CFSG.LocalAnalysis.ComponentInitial.OrthogonalStandardFormsRegular
public import CFSG.LocalAnalysis.ComponentInitial.SymplecticSmallFieldPerfect
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.X7bPairs
public import CFSG.LocalAnalysis.ZStar.BrauerSylowFusion
public import CFSG.LocalAnalysis.ZStar.PrincipalBlockTraceApplication
public import CFSG.RankThree.Classical.SteinbergBJSymplecticSquareZeroCentralizer
public import CFSG.RankThree.LocalRank.SelectorCases
public import CFSG.RankThree.PartOne.CTP.SeitzSpOuter
public import CFSG.RankThree.PartOne.CTP.StrongPFinal
public import CFSG.RankThree.PartOne.KC.SymplecticInnerPlaneCore
public import CFSG.RankThree.PartOne.S11d.OutClassicalTwo
public import CFSG.RankThree.PartOne.S11d.OutSymplectic
public import CFSG.RankThree.PartOne.S11d.OutUnitary
public import CFSG.RankThree.PartOne.S11d.PSLDescent
public import CFSG.RankThree.PartOne.S9.Sylow.ExclusionBasic
public import CFSG.RankThree.Theta.ThreeComponentOrbitCover
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.External.Huppert.IV.theorem_3_3
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.External.Isaacs.VII.lemma_7_7
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.FiniteFieldFixedSubfieldCard
public import CFSG.Walter.Defs
public import Certificates.Certificate1
public import Certificates.Certificate2
public import TauCeti.LinearAlgebra.Dimension.IsQuadraticExtension
public import TauCeti.LinearAlgebra.QuadraticForm.OrthogonalBasis
public import TauCeti.LinearAlgebra.QuadraticForm.OrthogonalGroup.LowRank

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.Assembly.LowTwoRank CFSG.Blueprint
open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.SymplecticHigher
open CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag

namespace SpTwoThree

theorem exists_subgroup_of_all_inner {G K : Type} [Group G] [Group K] (φ : G ≃* K)
    (hc : ∀ a : G, (∀ b, a * b = b * a) → a = 1)
    (hin : ∀ α : MulAut K, ∃ k : K, α = MulAut.conj k)
    (E : Subgroup (MulAut K)) (hE : IsElemAbelian 3 E) :
    ∃ E1 : Subgroup G, Nat.card E1 = Nat.card E ∧
      (∀ x ∈ E1, ∀ y ∈ E1, x * y = y * x) ∧ (∀ x ∈ E1, x ^ 3 = 1) ∧
      ggFixedClosure E =
        (Subgroup.closure {g : G | ∃ x ∈ E1, x ≠ 1 ∧ g * x = x * g}).map φ.toMonoidHom ∧
      (∀ g : G, φ g ∈ ggFixedSubgroup E ↔ ∀ x ∈ E1, g * x = x * g) := by
  classical
  let ψ : G →* MulAut K := (MulAut.conj : K →* MulAut K).comp φ.toMonoidHom
  have hψ : ∀ (g : G) (k : K), ψ g k = φ g * k * (φ g)⁻¹ := fun g k => rfl
  have hfix : ∀ x g : G, ψ x (φ g) = φ g ↔ g * x = x * g := by
    intro x g
    rw [hψ, mul_inv_eq_iff_eq_mul, ← map_mul, ← map_mul, φ.injective.eq_iff, eq_comm]
  have hψinj : Function.Injective ψ := by
    rw [injective_iff_map_eq_one]
    intro g hg
    refine hc g fun b => ?_
    have h1 := hfix g b
    rw [hg, MulAut.one_apply] at h1
    exact (h1.mp rfl).symm
  have hψsurj : Function.Surjective ψ := by
    intro α
    obtain ⟨k, rfl⟩ := hin α
    exact ⟨φ.symm k, by ext m; simp [ψ]⟩
  let E1 : Subgroup G := E.comap ψ
  refine ⟨E1, ?_, ?_, ?_, ?_, ?_⟩
  · rw [← Subgroup.card_map_of_injective hψinj, Subgroup.map_comap_eq_self_of_surjective hψsurj]
  · intro x hx y hy
    have h := congrArg Subtype.val (hE.1.is_comm.comm (⟨ψ x, hx⟩ : E) ⟨ψ y, hy⟩)
    exact hψinj (by simpa using h)
  · intro x hx
    apply hψinj
    rw [map_pow, map_one]
    exact hE.2 _ hx
  · rw [ggFixedClosure, MonoidHom.map_closure]
    congr 1
    ext k
    constructor
    · rintro ⟨ε, hεE, hε1, hεk⟩
      obtain ⟨x, rfl⟩ := hψsurj ε
      refine ⟨φ.symm k, ⟨x, hεE, fun h => hε1 (by rw [h, map_one]), ?_⟩, by simp⟩
      exact (hfix x (φ.symm k)).mp (by rw [MulEquiv.apply_symm_apply]; exact hεk)
    · rintro ⟨g, ⟨x, hx, hx1, hgx⟩, rfl⟩
      exact ⟨ψ x, hx, fun h => hx1 (hψinj (by rw [h, map_one])), (hfix x g).mpr hgx⟩
  · intro g
    constructor
    · intro hg x hx
      exact (hfix x g).mp (hg (ψ x) hx)
    · intro hg ε hε
      obtain ⟨x, rfl⟩ := hψsurj ε
      exact (hfix x g).mpr (hg x hε)

theorem eq_one_of_forall_commute {F : Type} [Field F] [Finite F] (hF : Nat.card F = 2) {r : ℕ}
    (hr : 2 ≤ r) (a : StatedSp r F) (ha : ∀ b, a * b = b * a) : a = 1 := by
  have hinj : Function.Injective (proj r F) :=
    CFSG.RankThree.PartOne.proj_injective_sp (f := 1) (by simpa using hF) le_rfl (by omega)
  have hz : proj r F a ∈ Subgroup.center (StatedProj (StatedSp r F)) := by
    rw [Subgroup.mem_center_iff]
    intro s
    obtain ⟨b, rfl⟩ := proj_surjective (r := r) (K := F) s
    rw [← map_mul, ← map_mul, ha b]
  rw [CFSG.LieType.SeitzGeneration.center_statedProj_statedSp_eq_bot hr, Subgroup.mem_bot] at hz
  exact hinj (hz.trans (map_one _).symm)

theorem all_inner_statedProj {F : Type} [Field F] [Finite F] (hF : Nat.card F = 2) {r : ℕ}
    (hr : 3 ≤ r) (α : MulAut (StatedProj (StatedSp r F))) :
    ∃ g : StatedProj (StatedSp r F), α = MulAut.conj g := by
  have hF01 : ∀ c : F, c = 0 ∨ c = 1 := fun c => by
    by_cases h : c = 0
    · exact Or.inl h
    · exact Or.inr (CFSG.LieType.SeitzGeneration.SpPlaneThreeF2.eq_one_of_card_two hF h)
  obtain ⟨-, hform⟩ := automorphism_generation (K := F) (r := r) hr
  obtain ⟨A, σ, hα⟩ := hform α
  have hσ : fieldAut r F σ = 1 := by
    have : σ = 1 := by
      ext x
      rcases hF01 x with rfl | rfl <;> simp
    rw [this, map_one]
  have hA : (A : GL (Fin r ⊕ Fin r) F) ∈ StatedSp r F := by
    obtain ⟨μ, hμ⟩ := A.2
    have hμ1 : μ = 1 := Units.ext (by
      rcases hF01 (μ : F) with h | h
      · exact absurd h μ.ne_zero
      · exact h)
    subst hμ1
    rw [Units.val_one, one_smul] at hμ
    exact SymplecticTorusWeyl.mem_statedSp_iff.2 hμ
  refine ⟨proj r F ⟨A, hA⟩, ?_⟩
  rw [hα, hσ, mul_one, CFSG.RankThree.PartTwo.KFacts.conj_proj_eq_spConjAut]

theorem isPGroup_fixedSubgroup {F : Type} [Field F] [Finite F] (hF : Nat.card F = 2) {r : ℕ}
    (hr : 3 ≤ r) {K : Type} [Group K] (e : K ≃* StatedProj (StatedSp r F))
    (E : Subgroup (MulAut K)) (hE : IsElemAbelian 3 E) (hcard : Nat.card E = 3 ^ 2)
    (hne : ggFixedClosure E ≠ ⊤) : IsPGroup 3 ↥(ggFixedSubgroup E) := by
  have hinj : Function.Injective (proj r F) :=
    CFSG.RankThree.PartOne.proj_injective_sp (f := 1) (by simpa using hF) le_rfl (by omega)
  let φ : StatedSp r F ≃* K :=
    (MulEquiv.ofBijective (proj r F) ⟨hinj, proj_surjective⟩).trans e.symm
  have hin : ∀ α : MulAut K, ∃ k : K, α = MulAut.conj k := by
    intro α
    obtain ⟨g, hg⟩ := all_inner_statedProj hF hr (MulAut.congr e α)
    obtain ⟨k, hk⟩ := (CFSG.RankThree.PartTwo.KFacts.isInnerAut_congr e α).mp ⟨g, hg.symm⟩
    exact ⟨k, hk.symm⟩
  obtain ⟨E1, hE1card, hE1comm, hE1exp, hD, hFix⟩ := exists_subgroup_of_all_inner φ
    (fun a ha => eq_one_of_forall_commute hF (by omega) a ha) hin E hE
  have hE1card9 : Nat.card E1 = 9 := by rw [hE1card, hcard]; norm_num
  have hne1 : Subgroup.closure {g : StatedSp r F | ∃ x ∈ E1, x ≠ 1 ∧ g * x = x * g} ≠ ⊤ := by
    intro h
    apply hne
    rw [hD, h]
    exact Subgroup.map_top_of_surjective _ φ.surjective
  rw [IsPGroup.iff_orderOf]
  rintro ⟨k, hk⟩
  obtain ⟨g, rfl⟩ := φ.surjective k
  have hg : g ^ 3 = 1 := CFSG.LieType.SeitzGeneration.pow_three_eq_one_of_commute_of_closure_ne_top
    hF hE1comm hE1exp hE1card9 hne1 g ((hFix g).mp hk)
  have hk3 : (⟨φ g, hk⟩ : ↥(ggFixedSubgroup E)) ^ 3 = 1 := by
    apply Subtype.ext
    change (φ g) ^ 3 = 1
    rw [← map_pow, hg, map_one]
  rcases (Nat.dvd_prime Nat.prime_three).mp (orderOf_dvd_of_pow_eq_one hk3) with h | h
  · exact ⟨0, by simpa using h⟩
  · exact ⟨1, by simpa using h⟩

end SpTwoThree

theorem ggSeitzExcSpSixCentralizerInput_holds : GGSeitzExcSpSixCentralizerInput := by
  intro K _ _ d q hq2 hq1 hd he E hE hcard hne
  obtain ⟨e⟩ := he
  obtain ⟨-, F, _, _, hF, ⟨e'⟩⟩ :=
    (ggLieModel_symplectic_two d q hq2 hq1 3 le_rfl hd e).statedClassicalModel (by decide)
  exact SpTwoThree.isPGroup_fixedSubgroup (by simpa using hF) le_rfl e' E hE hcard hne

theorem ggSeitzExcSpEightCentralizerInput_holds : GGSeitzExcSpEightCentralizerInput := by
  intro K _ _ d q hq2 hq1 hd he E hE hcard hne
  obtain ⟨e⟩ := he
  obtain ⟨-, F, _, _, hF, ⟨e'⟩⟩ :=
    (ggLieModel_symplectic_two d q hq2 hq1 4 (by norm_num) hd e).statedClassicalModel
      (by decide)
  exact SpTwoThree.isPGroup_fixedSubgroup (by simpa using hF) (by norm_num) e' E hE hcard hne

end CFSG.StandardType
