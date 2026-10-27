module

public import CFSG.LocalAnalysis.StandardType.GGSecFiveWeylB
public import CFSG.RankThree.PartOne.AUTSL.SpParabolic
public import CFSG.RankThree.PartOne.SEITZ4.SpRational
public import CFSG.GroupTheory.HallHigmanPiCore
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
public import CFSG.LocalAnalysis.ComponentInitial.LayerComponentOrbit
public import CFSG.LocalAnalysis.ComponentInitial.LinearInvolutionFixedField
public import CFSG.LocalAnalysis.ComponentInitial.OrthogonalFamilyLemmasFive
public import CFSG.LocalAnalysis.ComponentInitial.OrthogonalFamilyLemmasSix
public import CFSG.LocalAnalysis.ComponentInitial.OrthogonalReflectionSplitting
public import CFSG.LocalAnalysis.ComponentInitial.OrthogonalStandardFormsRegular
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.X7bPairs
public import CFSG.LocalAnalysis.ZStar.BrauerSylowFusion
public import CFSG.LocalAnalysis.ZStar.PrincipalBlockTraceApplication
public import CFSG.RankThree.Classical.SteinbergBJSymplecticSquareZeroCentralizer
public import CFSG.RankThree.LocalRank.SelectorCases
public import CFSG.RankThree.PartOne.AUTSL.SpDiag
public import CFSG.RankThree.PartOne.CTP.SeitzSpOuter
public import CFSG.RankThree.PartOne.CTP.StrongPFinal
public import CFSG.RankThree.PartOne.KC.SymplecticInnerPlaneCore
public import CFSG.RankThree.PartOne.S11d.OutClassicalTwo
public import CFSG.RankThree.PartOne.S11d.OutSymplectic
public import CFSG.RankThree.PartOne.S11d.OutUnitary
public import CFSG.RankThree.PartOne.S11d.PSLDescent
public import CFSG.RankThree.PartOne.S9.Sylow.ExclusionBasic
public import CFSG.RankThree.PartTwo.Sec4.Census.Interface
public import CFSG.RankThree.Theta.ThreeComponentOrbitCover
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.External.Huppert.IV.theorem_3_3
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.External.Isaacs.VII.lemma_7_7
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.FiniteFieldFixedSubfieldCard
public import CFSG.Walter.Defs
public import Certificates.Certificate1
public import Certificates.Certificate2
public import TauCeti.GroupTheory.SpecificGroups.CFSG.TypeC.Agreement
public import TauCeti.LinearAlgebra.Dimension.IsQuadraticExtension
public import TauCeti.LinearAlgebra.QuadraticForm.OrthogonalBasis
public import TauCeti.LinearAlgebra.QuadraticForm.OrthogonalGroup.LowRank

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.Assembly.LowTwoRank CFSG.LieType.Universal.Symplectic
  CFSG.LieType.Universal.Symplectic.SpExtras CFSG.LocalAnalysis.ComponentInitial.SymplecticHigher
  TauCeti.GLSymplecticFin

section Aut

variable {r : ℕ} {K : Type} [Field K] [Finite K] [CharP K 2]

theorem exists_spConj_fieldSp_of_mulAut (hr : 3 ≤ r) (β : MulAut (StatedSp r K)) :
    ∃ (B : StatedSp r K) (σ : K ≃+* K), ∀ g, β g = B * fieldSp r K σ g * B⁻¹ := by
  have : NeZero r := ⟨by omega⟩
  have hbot : spScalars r K = ⊥ :=
    CFSG.RankThree.PartOne.AUTSL.spScalars_eq_bot_of_charTwo
  have hinj : Function.Injective (CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag.proj r K) :=
    (MonoidHom.ker_eq_bot_iff _).1 (by rw [ker_proj, hbot])
  let ψ : StatedSp r K ≃* StatedProj (StatedSp r K) :=
    MulEquiv.ofBijective (CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag.proj r K)
      ⟨hinj, proj_surjective⟩
  obtain ⟨A, σ, hα⟩ := (automorphism_generation (r := r) (K := K) hr).2 (MulAut.congr ψ β)
  obtain ⟨B, hB⟩ := CFSG.RankThree.PartOne.SEITZ4.exists_statedSp_conjSp_eq A
  refine ⟨B, σ, fun g => ?_⟩
  have h1 : CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag.proj r K (β g) =
      CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag.proj r K
        (conjSp r K A (fieldSp r K σ g)) := by
    have h2 := congrArg (fun φ : MulAut (StatedProj (StatedSp r K)) =>
      φ (CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag.proj r K g)) hα
    simp only [MulAut.mul_apply, conjAut_proj, fieldAut_proj] at h2
    rw [← h2]
    have hs : ψ.symm (CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag.proj r K g) = g :=
      ψ.symm_apply_apply g
    simp only [MulAut.congr_apply, MulEquiv.trans_apply]
    rw [hs]
    rfl
  rw [hinj h1, hB]

end Aut

section Field

variable {n : ℕ} {F : Type} [Field F]

theorem spFieldSp_elt (σ : F ≃+* F) (r : RootSubgroupIndex n) (c : F) :
    fieldSp n F σ (elt r c) = elt r (σ c) := by
  apply mat_injective
  have hE : (E F r).map σ = E F r := by
    cases r <;> simp [E, Matrix.map_sub, Matrix.map_add]
  have h : mat n F (fieldSp n F σ (elt r c)) = (mat n F (elt r c)).map σ := rfl
  rw [h, mat_elt, mat_elt]
  conv_rhs => rw [← hE]
  ext i j
  rcases eq_or_ne i j with rfl | hij
  · simp [Matrix.map_apply]
  · simp [Matrix.map_apply, Matrix.one_apply_ne hij]

theorem spFieldSp_weylRep (σ : F ≃+* F) (k : Fin n) :
    fieldSp n F σ (weylRep n F k) = weylRep n F k := by
  by_cases h : k.val + 1 < n
  · rw [weylRep_eq_elt_of_lt h]
    simp only [map_mul, spFieldSp_elt, map_one, map_neg]
  · rw [weylRep_eq_elt_of_not_lt h]
    simp only [map_mul, spFieldSp_elt, map_one, map_neg]

end Field

section Transfer

variable {n : ℕ} {F : Type} [Field F] [Finite F] [CharP F 2] {X : Type*} [Group X]

theorem ggSpEndNode_conj_of_mulAut (hn : 3 ≤ n) {φ φ' : StatedSp n F →* X}
    (hφ : Function.Injective φ) (hφ' : Function.Injective φ') (hr : φ.range = φ'.range) {T : X}
    (hT : GGSpEndNode φ T) : ∃ B : StatedSp n F, GGSpEndNode φ' (φ B * T * (φ B)⁻¹) := by
  let e : StatedSp n F ≃* φ.range := MonoidHom.ofInjective hφ
  let e' : StatedSp n F ≃* φ'.range := MonoidHom.ofInjective hφ'
  let α : MulAut (StatedSp n F) := (e'.trans (MulEquiv.subgroupCongr hr.symm)).trans e.symm
  have hα : ∀ g, φ (α g) = φ' g := fun g => by
    have h1 : (e (α g) : X) = φ (α g) := MonoidHom.ofInjective_apply hφ
    have h2 : e (α g) = MulEquiv.subgroupCongr hr.symm (e' g) := MulEquiv.apply_symm_apply e _
    have h3 : (e' g : X) = φ' g := MonoidHom.ofInjective_apply hφ'
    rw [← h1, h2, ← h3]
    rfl
  obtain ⟨B, σ, hB⟩ := exists_spConj_fieldSp_of_mulAut hn α
  have hφ'g : ∀ g, φ' g = φ B * φ (fieldSp n F σ g) * (φ B)⁻¹ := fun g => by
    rw [← hα, hB, map_mul, map_mul, map_inv]
  refine ⟨B, ?_, ?_, ?_⟩
  · calc φ B * T * (φ B)⁻¹ * (φ B * T * (φ B)⁻¹) = φ B * (T * T) * (φ B)⁻¹ := by group
      _ = 1 := by rw [hT.1, mul_one, mul_inv_cancel]
  · intro k hk
    rw [hφ'g, spFieldSp_weylRep]
    calc (φ B * T * (φ B)⁻¹ * (φ B * φ (weylRep n F k) * (φ B)⁻¹)) ^ 3 =
          (φ B * (T * φ (weylRep n F k)) * (φ B)⁻¹) ^ 3 := by group
      _ = φ B * (T * φ (weylRep n F k)) ^ 3 * (φ B)⁻¹ := conj_pow
      _ = 1 := by rw [hT.2.1 k hk, mul_one, mul_inv_cancel]
  · intro r hr c
    rw [hφ'g, spFieldSp_elt]
    calc φ B * T * (φ B)⁻¹ * (φ B * φ (elt r (σ c)) * (φ B)⁻¹) =
          φ B * (T * φ (elt r (σ c))) * (φ B)⁻¹ := by group
      _ = φ B * (φ (elt r (σ c)) * T) * (φ B)⁻¹ := by rw [hT.2.2 r hr (σ c)]
      _ = φ B * φ (elt r (σ c)) * (φ B)⁻¹ * (φ B * T * (φ B)⁻¹) := by group

end Transfer

@[expose] def GGSpJoinEndNodeSomeInput : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (p : ℕ) (B Bs : Subgroup G) (x : G) (L D J : Subgroup G)
    (n f : ℕ) (y : G) (K : Subgroup G), GGConfig p B Bs x L D J → GGOpAutTrivial p Bs →
    GGInnerDiagAll p B Bs x L D J → GGNoTransvection p Bs → GGTypeCNbr p B Bs x L D J n f y K →
    ∃ φ₁ : StatedSp n (GaloisField 2 f) →* G, Function.Injective φ₁ ∧ φ₁.range = L ∧
      ∃ T : G, T ∈ L ⊔ K ∧ GGSpEndNode φ₁ T ∧ K ≤ L ⊔ L.map (MulAut.conj T).toMonoidHom

theorem ggSpJoinEndNodeInput_of_some (h : GGSpJoinEndNodeSomeInput) : GGSpJoinEndNodeInput := by
  intro G _ _ p B Bs x L D J n f y K hcfg hOp hInn hNoTr hN φ' hφ' hφ'L
  obtain ⟨φ, hφ, hφL, T, hTLK, hT, hKT⟩ := h G p B Bs x L D J n f y K hcfg hOp hInn hNoTr hN
  have hn : 3 ≤ n := by have := hN.2.1; omega
  obtain ⟨g, hg⟩ := ggSpEndNode_conj_of_mulAut hn hφ hφ' (hφL.trans hφ'L.symm) hT
  have ha : φ g ∈ L := hφL ▸ ⟨g, rfl⟩
  set a := φ g with ha_def
  refine ⟨a * T * a⁻¹, ?_, hg, ?_⟩
  · have haLK : a ∈ L ⊔ K := Subgroup.mem_sup_left ha
    exact (L ⊔ K).mul_mem ((L ⊔ K).mul_mem haLK hTLK) ((L ⊔ K).inv_mem haLK)
  · intro k hk
    set H := L ⊔ L.map (MulAut.conj T).toMonoidHom with hH
    have haH : a ∈ H := Subgroup.mem_sup_left ha
    have hk' : a⁻¹ * k * a ∈ H := H.mul_mem (H.mul_mem (H.inv_mem haH) (hKT hk)) haH
    have hle : H.map (MulAut.conj a).toMonoidHom ≤
        L ⊔ L.map (MulAut.conj (a * T * a⁻¹)).toMonoidHom := by
      rw [hH, Subgroup.map_sup]
      refine sup_le_sup ?_ ?_
      · rintro _ ⟨l, hl, rfl⟩
        exact L.mul_mem (L.mul_mem ha hl) (L.inv_mem ha)
      · rintro _ ⟨_, ⟨l, hl, rfl⟩, rfl⟩
        refine ⟨a * l * a⁻¹, L.mul_mem (L.mul_mem ha hl) (L.inv_mem ha), ?_⟩
        simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
        group
    have e : k = (MulAut.conj a).toMonoidHom (a⁻¹ * k * a) := by
      simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
      group
    rw [e]
    exact hle ⟨_, hk', rfl⟩

end CFSG.StandardType
