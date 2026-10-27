module

public import CFSG.LocalAnalysis.StandardType.GGNbrLangFNIOrthogonalSemilin
public import CFSG.LocalAnalysis.StandardType.GGNbrLangFNIOrthogonalBlocks
public import CFSG.LocalAnalysis.StandardType.GGNbrLangFNIOrthogonal
public import CFSG.LocalAnalysis.StandardType.GGNbrLangFNIOrthogonalUnitary4
public import CFSG.LocalAnalysis.StandardType.GGNbrLangFNIVac
public import CFSG.LocalAnalysis.StandardType.GGNbrLangFNIRows
public import CFSG.LocalAnalysis.StandardType.GGNbrLangFNIRestr
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalPointSemilinearRealizationBasic
public import CFSG.LocalAnalysis.StandardType.GGClassicalBlockOmegaDecomp
public import CFSG.LocalAnalysis.StandardType.GGClassicalBlockOmegaIsoOneLinear
public import CFSG.LocalAnalysis.StandardType.GGNbrLangFNIOne
public import CFSG.LocalAnalysis.SteinbergBMEvenG2FixedNoNormalSL2
public import CFSG.RankThree.PartOne.F106.OddRadTools
public import CFSG.LocalAnalysis.StandardType.GGCentInnerDiagOmega
public import CFSG.RankThree.PartOne.S11d.OrthGoodSingle
public import CFSG.GroupTheory.WeirSylow.OrthogonalModels
public import CFSG.HardMathSupport.Dickson.Sec6.I1431Fam.OrtHFixed
public import CFSG.HardMathSupport.Dickson.Sec6.I1431Fam.KeyAbstract
public import CFSG.HardMathSupport.Dickson.Sec6.I1431Fam.OrtHShell
public import CFSG.HardMathSupport.Dickson.Sec6.I1431LieAux.Inner
public import CFSG.HardMathSupport.Dickson.Sec6.I1431LieAux.Split

public section

namespace CFSG.StandardType

open CFSG.Assembly
open CFSG.Open
open CFSG.ComponentClassification.CatalogueBOrthogonalSemilinear
open CFSG.StandardType.ClassicalBlocks
open CFSG.LocalAnalysis.ComponentInitial
open CFSG.LocalAnalysis.ComponentInitial.OrthogonalTail
open CFSG.ComponentClassification.CatalogueBOrthogonalPointData
open CFSG.StandardType.ClassicalBlocks
open CFSG.StandardType.RecipeFieldOmega
open CFSG.ClassicalGroups.Orthogonal
open CFSG.RankThree.PartOne.KCPrimary
open CFSG.RankThree.PartOne.KCOrthogonal
open CFSG.RankThree.PartOne.KCOrthComm
open Polynomial
open CFSG.RankThree.PartOne.AUTSL
open CFSG.StandardType.ClassicalPosition
open Matrix

theorem component_transport_of_mulEquiv {R Γ : Type} [Group R] [Group Γ]
    (Θ : R ≃* Γ) {h : MulAut R} {b : Γ}
    (hγ : MulAut.congr Θ h = MulAut.conj b)
    (J0 : Subgroup R)
    (hJ0 : CFSG.Assembly.IsComponentOf J0
      (MonoidHom.eqLocus (h : R →* R) (MonoidHom.id R))) :
    CFSG.Assembly.IsComponentOf (J0.map Θ.toMonoidHom)
      (MonoidHom.eqLocus ((MulAut.conj b : MulAut Γ) : Γ →* Γ) (MonoidHom.id Γ)) := by
  have h' := @CFSG.LocalAnalysis.ComponentInitial.isComponentOf_map_of_injective R Γ _ _
    J0 (MonoidHom.eqLocus (h : R →* R) (MonoidHom.id R)) hJ0
    Θ.toMonoidHom Θ.injective
  have hmap := CFSG.LocalAnalysis.SteinbergBM.map_eqLocus_mulAut_congr Θ h
  change (Subgroup.map Θ.toMonoidHom ((h : R →* R).eqLocus (MonoidHom.id R))) =
    ((MulAut.congr Θ h : MulAut Γ) : Γ →* Γ).eqLocus (MonoidHom.id Γ) at hmap
  rw [hγ] at hmap
  rw [hmap] at h'
  exact h'

variable {K : Type} [Field K]

noncomputable def SemiSim.toCoordSemilinearEquiv (d : ℕ)
    {Qc : QuadraticForm K (Fin d → K)} (T : SemiSim Qc Qc) :
    (Fin d → K) ≃ₛₗ[T.σ.toRingHom] (Fin d → K) where
  toAddEquiv :=
    { toFun := ⇑T.e
      invFun := ⇑T.e.symm
      left_inv := T.e.left_inv
      right_inv := T.e.right_inv
      map_add' := T.map_add' }
  map_smul' := T.map_smul'

noncomputable def SemiSim.toCoordinatePair (d : ℕ)
    {Qc : QuadraticForm K (Fin d → K)} (T : SemiSim Qc Qc) :
    coordinateSemilinearGroup d K :=
  @CFSG.ComponentClassification.CatalogueBOrthogonalPointSemilinearRealization.realizingPair K _ d
    T.σ (SemiSim.toCoordSemilinearEquiv d T)

theorem SemiSim.coordinateSemilinearMap_toCoordinatePair (d : ℕ)
    {Qc : QuadraticForm K (Fin d → K)} (T : SemiSim Qc Qc) :
    coordinateSemilinearMap (SemiSim.toCoordinatePair d T) =
      (SemiSim.toCoordSemilinearEquiv d T).toAddEquiv := by
  unfold SemiSim.toCoordinatePair
  rw [@CFSG.ComponentClassification.CatalogueBOrthogonalPointSemilinearRealization.realizingPair_addEquiv K _ d
    T.σ (SemiSim.toCoordSemilinearEquiv d T)]

theorem SemiSim.toCoordinatePair_mem_similarityPairs (d : ℕ)
    {Qc : QuadraticForm K (Fin d → K)} (T : SemiSim Qc Qc) :
    SemiSim.toCoordinatePair d T ∈ similarityPairs Qc := by
  refine ⟨Units.mk0 T.μ T.μ_ne_zero, ?_⟩
  intro v
  rw [SemiSim.coordinateSemilinearMap_toCoordinatePair d T]
  exact T.map_quad' v

noncomputable def SemiSim.toSimilarityPair (d : ℕ)
    {Qc : QuadraticForm K (Fin d → K)} (T : SemiSim Qc Qc) : similarityPairs Qc :=
  ⟨SemiSim.toCoordinatePair d T, SemiSim.toCoordinatePair_mem_similarityPairs d T⟩

noncomputable def SemiSim.fixedBasisSemilinSemiSim (d : ℕ)
    {W : Type} [AddCommGroup W] [Module K W]
    {QW : QuadraticForm K W} {Qc : QuadraticForm K (Fin d → K)}
    (eIso : QW.IsometryEquiv Qc) (T : W ≃+ W) (σ : K ≃+* K) (μ : K)
    (hμ : μ ≠ 0)
    (hTsmul : ∀ (c : K) (w : W), T (c • w) = σ c • T w)
    (hTQ : ∀ w : W, QW (T w) = μ * σ (QW w)) : SemiSim Qc Qc where
  e := (fixedBasisSemilin eIso.toLinearEquiv T).toEquiv
  σ := σ
  μ := μ
  μ_ne_zero := hμ
  map_add' x y := by
    change fixedBasisSemilin eIso.toLinearEquiv T (x + y) =
      fixedBasisSemilin eIso.toLinearEquiv T x + fixedBasisSemilin eIso.toLinearEquiv T y
    exact (fixedBasisSemilin eIso.toLinearEquiv T).map_add x y
  map_smul' c x := by
    change fixedBasisSemilin eIso.toLinearEquiv T (c • x) =
      σ c • fixedBasisSemilin eIso.toLinearEquiv T x
    exact fixedBasisSemilin_smul eIso.toLinearEquiv T hTsmul c x
  map_quad' v := by
    change Qc (fixedBasisSemilin eIso.toLinearEquiv T v) = μ * σ (Qc v)
    rw [fixedBasisSemilin_apply]
    calc
      Qc (eIso.toLinearEquiv (T (eIso.toLinearEquiv.symm v))) =
          QW (T (eIso.toLinearEquiv.symm v)) := eIso.map_app' _
      _ = μ * σ (QW (eIso.toLinearEquiv.symm v)) := hTQ _
      _ = μ * σ (Qc v) := by
        congr 1
        exact congrArg σ (eIso.symm.map_app v)

structure FixedDicksonData
    {K : Type} [Field K]
    {W : Type} [AddCommGroup W] [Module K W] [FiniteDimensional K W]
    (Q : QuadraticForm K W) (hQ : (QuadraticMap.polarBilin Q).Nondegenerate) where
  hD : CFSG.RankThree.PartOne.DicksonDerived Q hQ

noncomputable def fixedBlockForm
    {K : Type} [Field K] [Fintype K] [CharP K 2]
    {ι : Type} [Fintype ι] [DecidableEq ι]
    (Φ : QuadraticForm K (ι → K)) (b : GL ι K) :
    QuadraticForm K (Fin (Module.finrank K
      (CFSG.RankThree.PartOne.KCOrthogonal.fixedSpace (ggJSo2_ML b))) → K) :=
  (Φ.comp
    (CFSG.RankThree.PartOne.KCOrthogonal.fixedSpace (ggJSo2_ML b)).subtype).basisRepr
      (Module.finBasis K
        (CFSG.RankThree.PartOne.KCOrthogonal.fixedSpace (ggJSo2_ML b)))

noncomputable def fixedBlockIsometryEquiv
    {K : Type} [Field K] [Fintype K] [CharP K 2]
    {ι : Type} [Fintype ι] [DecidableEq ι]
    (Φ : QuadraticForm K (ι → K)) (b : GL ι K) :
    (Φ.comp
      (CFSG.RankThree.PartOne.KCOrthogonal.fixedSpace (ggJSo2_ML b)).subtype).IsometryEquiv
        (fixedBlockForm Φ b) :=
  QuadraticMap.isometryEquivBasisRepr _ _

@[expose] noncomputable def fixedBlockSemisim
    {K : Type} [Field K] [Fintype K] [CharP K 2]
    {ι : Type} [Fintype ι] [DecidableEq ι]
    (Φ : QuadraticForm K (ι → K)) (b : GL ι K)
    {σ : K ≃+* K} {S : (ι → K) ≃+ (ι → K)}
    (hS : ∀ (c : K) v, S (c • v) = σ c • S v)
    (hSx : ∀ v, S (ggJSo2_ML b v) = ggJSo2_ML b (S v))
    (hSQ : ∀ v, Φ (S v) = σ (Φ v)) :
    SemiSim (fixedBlockForm Φ b) (fixedBlockForm Φ b) :=
  SemiSim.fixedBasisSemilinSemiSim
    (Module.finrank K
      (CFSG.RankThree.PartOne.KCOrthogonal.fixedSpace (ggJSo2_ML b)))
    (fixedBlockIsometryEquiv Φ b) (fixedSemilinRestrict hSx) σ 1
    (by norm_num) (fixedSemilinRestrict_smul hS hSx)
    (fun w => by simpa using fixedSemilinRestrict_preserves_quadraticForm hSx hSQ w)

@[expose] noncomputable def fixedBlockSimilarityPair
    {K : Type} [Field K] [Fintype K] [CharP K 2]
    {ι : Type} [Fintype ι] [DecidableEq ι]
    (Φ : QuadraticForm K (ι → K)) (b : GL ι K)
    {σ : K ≃+* K} {S : (ι → K) ≃+ (ι → K)}
    (hS : ∀ (c : K) v, S (c • v) = σ c • S v)
    (hSx : ∀ v, S (ggJSo2_ML b v) = ggJSo2_ML b (S v))
    (hSQ : ∀ v, Φ (S v) = σ (Φ v)) :
    similarityPairs (fixedBlockForm Φ b) :=
  SemiSim.toSimilarityPair _ (fixedBlockSemisim Φ b hS hSx hSQ)

theorem fixedBlockSimilarityPair_right
    {K : Type} [Field K] [Fintype K] [CharP K 2]
    {ι : Type} [Fintype ι] [DecidableEq ι]
    (Φ : QuadraticForm K (ι → K)) (b : GL ι K)
    {σ : K ≃+* K} {S : (ι → K) ≃+ (ι → K)}
    (hS : ∀ (c : K) v, S (c • v) = σ c • S v)
    (hSx : ∀ v, S (ggJSo2_ML b v) = ggJSo2_ML b (S v))
    (hSQ : ∀ v, Φ (S v) = σ (Φ v)) :
    (fixedBlockSimilarityPair Φ b hS hSx hSQ).val.right = σ := by
  rfl

theorem kgFieldRestriction_orthogonalFixedBlock_quasisimple_of_semilinear
    {K : Type} [Field K] [Fintype K] [CharP K 2]
    {ι : Type} [Fintype ι] [DecidableEq ι]
    (Φ : QuadraticForm K (ι → K)) (hΦ : (QuadraticMap.polarBilin Φ).Nondegenerate)
    (b : GL ι K) (hb : b ∈ StatedOmega ⇑Φ) (hodd : Odd (orderOf b))
    (h8 : 8 ≤ Fintype.card ι)
    {ε : Matrix ι ι K}
    (hε : IsPrimAdjIdemIn (RingHom.id K)
      (LinearMap.toMatrix₂' K (QuadraticMap.polarBilin Φ))
      (Algebra.adjoin K (Units.val '' ({b} : Set (GL ι K)))) ε)
    (h1 : (b : Matrix ι ι K) * ε = ε)
    (QW : QuadraticForm K
      (CFSG.RankThree.PartOne.KCOrthogonal.fixedSpace (ggJSo2_ML b)))
    (hQW : (QuadraticMap.polarBilin QW).Nondegenerate)
    (hW : QW = Φ.comp
      (CFSG.RankThree.PartOne.KCOrthogonal.fixedSpace (ggJSo2_ML b)).subtype)
    (D : FixedDicksonData QW hQW)
    (hx : CFSG.RankThree.PartOne.KCOrthogonal.OddOrderIsometry Φ (orderOf b)
      (ggJSo2_ML b))
    {d : ℕ} {Φ₁ : QuadraticForm K (Fin d → K)}
    (eIso : QW.IsometryEquiv Φ₁)
    (hdim : 6 ≤ d ∨ (d = 4 ∧ ¬ ∃ T : Submodule K (Fin d → K),
      Module.finrank K T = 2 ∧ ∀ x ∈ T, Φ₁ x = 0))
    (hK : 4 ≤ Nat.card K)
    {σ : K ≃+* K} (hσ : σ ≠ 1) {S : (ι → K) ≃+ (ι → K)}
    (hS : ∀ (c : K) v, S (c • v) = σ c • S v)
    (hSx : ∀ v, S (ggJSo2_ML b v) = ggJSo2_ML b (S v))
    (hSQ : ∀ v, Φ (S v) = σ (Φ v))
    (C : Subgroup (StatedOmega ⇑Φ))
    (hC : CFSG.Assembly.IsComponentOf C
      (glBlockCentralizer (StatedOmega ⇑Φ).subtype ({b} : Set (GL ι K)) ε))
    (fC : MulAut ↥C)
    (hfC : ∀ c : ↥C, ∀ v : ι → K,
      ggJSo2_ML (((fC c : ↥C) : StatedOmega ⇑Φ) : GL ι K) v =
        S (ggJSo2_ML (((c : ↥C) : StatedOmega ⇑Φ) : GL ι K) (S.symm v))) :
    GGMarkingAll (K := ↥C) fun _ _ _ I _ θ => kgInducedAut θ fC ∉ I := by
  classical
  subst hW
  have hD : CFSG.RankThree.PartOne.DicksonDerived
      (Φ.comp (CFSG.RankThree.PartOne.KCOrthogonal.fixedSpace (ggJSo2_ML b)).subtype)
      hx.polarBilin_fixed_nondegenerate := by
    simpa using D.hD
  have hΦ₁ : (QuadraticMap.polarBilin Φ₁).Nondegenerate :=
    CFSG.GroupTheory.WeirSylow.nondegenerate_polarBilin_of_isometryEquiv eIso hQW
  let F : Subgroup (StatedOmega ⇑Φ) :=
    glBlockCentralizer (StatedOmega ⇑Φ).subtype ({b} : Set (GL ι K)) ε
  let eB : ↥F ≃* ↥(CFSG.RankThree.Classical2.orthDerived Φ₁) :=
    glBlockCentralizerEquivFixedDerivedBasis Φ hΦ b hb hodd hε h1 hD eIso
  let CF : Subgroup ↥F := C.subgroupOf F
  have hCF : CFSG.Assembly.IsComponentOf CF ⊤ := by
    have hmapC : CF.map F.subtype = C := by
      rw [Subgroup.subgroupOf_map_subtype, inf_of_le_left hC.1]
    have hmapTop : (⊤ : Subgroup ↥F).map F.subtype = F := by
      rw [Subgroup.map_top, Subgroup.range_subtype]
    have hcomp : CFSG.Assembly.IsComponentOf (CF.map F.subtype) ((⊤ : Subgroup ↥F).map F.subtype) := by
      simpa [hmapC, hmapTop] using hC
    exact (CFSG.LocalAnalysis.ComponentInitial.isComponentOf_map_iff (f := F.subtype) F.subtype_injective).1 hcomp
  let C' : Subgroup (↥(CFSG.RankThree.Classical2.orthDerived Φ₁)) := CF.map eB.toMonoidHom
  have hC' : CFSG.Assembly.IsComponentOf C' ⊤ := by
    simpa [C'] using CFSG.LocalAnalysis.ComponentInitial.isComponentOf_map_of_injective hCF eB.toMonoidHom eB.injective
  have hqWhole : CFSG.Assembly.IsQuasisimple ↥(CFSG.RankThree.Classical2.orthDerived Φ₁) := by
    let eS : matrixDerived Φ₁ ≃*
        StatedOmega ⇑Φ₁ :=
      MulEquiv.subgroupCongr
        (CFSG.RankThree.PartOne.AUTSL.matrixDerived_eq_statedOmega Φ₁)
    let eO : CFSG.RankThree.Classical2.orthDerived Φ₁ ≃* StatedOmega ⇑Φ₁ :=
      (CFSG.RankThree.PartOne.KCOrthComm.matrixDerivedEquiv Φ₁).symm.trans eS
    have hdim' : 6 ≤ Fintype.card (Fin d) ∨ (Fintype.card (Fin d) = 4 ∧
        ¬ ∃ T : Submodule K (Fin d → K), Module.finrank K T = 2 ∧ ∀ x ∈ T, Φ₁ x = 0) := by
      simpa [Fintype.card_fin] using hdim
    exact CFSG.Assembly.IsQuasisimple.of_mulEquiv eO (isQuasisimple_statedOmega Φ₁ hΦ₁ hdim')
  have hqO : CFSG.Assembly.IsQuasisimple ↥(⊤ : Subgroup ↥(CFSG.RankThree.Classical2.orthDerived Φ₁)) :=
    CFSG.Assembly.IsQuasisimple.of_mulEquiv Subgroup.topEquiv hqWhole
  have hC'eq : C' = ⊤ := GGHalf.eq_of_isComponentOf_isQuasisimple hqO hC'
  let eCF : ↥C ≃* ↥CF := (Subgroup.subgroupOfEquivOfLe hC.1).symm
  let eCmap : ↥CF ≃* ↥C' := Subgroup.equivMapOfInjective CF eB.toMonoidHom eB.injective
  let eC : ↥C ≃* ↥(CFSG.RankThree.Classical2.orthDerived Φ₁) :=
    eCF.trans (eCmap.trans ((MulEquiv.subgroupCongr hC'eq).trans Subgroup.topEquiv))
  have heC_apply (x : ↥C) : eC x = eB ⟨x, hC.1 x.2⟩ := rfl
  let f' : MulAut ↥(CFSG.RankThree.Classical2.orthDerived Φ₁) := MulAut.congr eC fC
  let Tσ : (Fin d → K) ≃+ (Fin d → K) :=
    fixedBasisSemilin eIso.toLinearEquiv (fixedSemilinRestrict hSx)
  have hTsmul : ∀ (c : K) (v : Fin d → K), Tσ (c • v) = σ c • Tσ v :=
    fixedBasisSemilin_smul eIso.toLinearEquiv (fixedSemilinRestrict hSx)
      (fixedSemilinRestrict_smul hS hSx)
  have hTQ : ∀ v : Fin d → K, Φ₁ (Tσ v) = σ (Φ₁ v) :=
    fixedBasisSemilin_preserves_quadraticForm eIso (fixedSemilinRestrict hSx)
      (fun w => by simpa using fixedSemilinRestrict_preserves_quadraticForm hSx hSQ w)
  have hf' : ∀ (g : CFSG.RankThree.Classical2.orthDerived Φ₁) (v : Fin d → K),
      (f' g : (Fin d → K) ≃ₗ[K] (Fin d → K)) v = Tσ ((g : (Fin d → K) ≃ₗ[K] (Fin d → K))
        (Tσ.symm v)) := by
    intro g v
    let c : ↥C := eC.symm g
    have hgc : eC c = g := eC.apply_symm_apply g
    have hf'g : f' g = eC (fC c) := by
      simp [f', c]
    have hsq := glBlockCentralizerEquivFixedDerivedBasis_square Φ hΦ b hb hodd hε h1 hD eIso
      (S := S) hSx (g := ⟨c, hC.1 c.2⟩) (g' := ⟨fC c, hC.1 (fC c).2⟩)
      (fun v => hfC c v) v
    rw [hf'g, heC_apply, ← hgc, heC_apply]
    simpa [Tσ] using hsq
  have hV : 4 ≤ Module.finrank K (Fin d → K) := by
    have hd4 : 4 ≤ d := by
      rcases hdim with h6 | ⟨h4, -⟩ <;> omega
    simpa [Module.finrank_fintype_fun_eq_card] using hd4
  have hf'not : f' ∉ CFSG.ComponentClassification.OuterAutomorphisms.inner
      ↥(CFSG.RankThree.Classical2.orthDerived Φ₁) :=
    CFSG.RankThree.PartOne.not_inner_orthDerived_of_semilinear (Q := Φ₁) hΦ₁ hK hV hσ Tσ
      hTsmul hTQ f' hf'
  let eS : matrixDerived Φ₁ ≃*
      StatedOmega ⇑Φ₁ :=
    MulEquiv.subgroupCongr
      (CFSG.RankThree.PartOne.AUTSL.matrixDerived_eq_statedOmega Φ₁)
  let eO : CFSG.RankThree.Classical2.orthDerived Φ₁ ≃* StatedOmega ⇑Φ₁ :=
    (CFSG.RankThree.PartOne.KCOrthComm.matrixDerivedEquiv Φ₁).symm.trans eS
  have hmarkTag : LargeEvenMarking ↥(CFSG.RankThree.Classical2.orthDerived Φ₁)
      (fun lab R _ I _ _ => GGChevStTag lab ∧ I = LargeEvenInnSet R) :=
    largeEvenMarking_congr eO (fun _ _ _ _ _ _ h => h)
      (largeEvenMarking_statedOmega_inn Φ₁ hΦ₁ (by simpa [Fintype.card_fin] using hdim))
  have hmarkO : LargeEvenMarking ↥(CFSG.RankThree.Classical2.orthDerived Φ₁)
      (fun _ _ _ I _ _ => I = LargeEvenInnSet _) :=
    largeEvenMarking_mono (fun _ _ _ _ _ _ h => h.2) hmarkTag
  have hmarkNeg : LargeEvenMarking ↥(CFSG.RankThree.Classical2.orthDerived Φ₁)
      (fun _ _ _ I _ θ => ¬ ∃ φ ∈ Subgroup.closure I,
        LargeEvenInduces θ (fun j k : ↥(CFSG.RankThree.Classical2.orthDerived Φ₁) => k = f' j) φ) :=
    largeEvenMarking_not_induces_of_not_inner ⟨hqWhole.1⟩ f' hf'not hmarkO
  exact kgFieldRestriction_of_oneMarking_congr eC fC f' (fun c => by simp [f']) hmarkNeg

theorem kgFieldRestriction_orthogonalFixedBlock_coordinate_of_semilinear
    {K : Type} [Field K] [Fintype K] [CharP K 2]
    {ι : Type} [Fintype ι] [DecidableEq ι]
    (Φ : QuadraticForm K (ι → K)) (hΦ : (QuadraticMap.polarBilin Φ).Nondegenerate)
    (b : GL ι K) (hb : b ∈ StatedOmega ⇑Φ) (hodd : Odd (orderOf b))
    (h8 : 8 ≤ Fintype.card ι)
    {ε : Matrix ι ι K}
    (hε : IsPrimAdjIdemIn (RingHom.id K)
      (LinearMap.toMatrix₂' K (QuadraticMap.polarBilin Φ))
      (Algebra.adjoin K (Units.val '' ({b} : Set (GL ι K)))) ε)
    (h1 : (b : Matrix ι ι K) * ε = ε)
    {d : ℕ} {Φ₁ : QuadraticForm K (Fin d → K)}
    (eIso : (Φ.comp
      (CFSG.RankThree.PartOne.KCOrthogonal.fixedSpace (ggJSo2_ML b)).subtype).IsometryEquiv Φ₁)
    (hdim : 6 ≤ d ∨ (d = 4 ∧ ¬ ∃ T : Submodule K (Fin d → K),
      Module.finrank K T = 2 ∧ ∀ x ∈ T, Φ₁ x = 0))
    (hK : 4 ≤ Nat.card K)
    {σ : K ≃+* K} (hσ : σ ≠ 1) {S : (ι → K) ≃+ (ι → K)}
    (hS : ∀ (c : K) v, S (c • v) = σ c • S v)
    (hSx : ∀ v, S (ggJSo2_ML b v) = ggJSo2_ML b (S v))
    (hSQ : ∀ v, Φ (S v) = σ (Φ v))
    (C : Subgroup (StatedOmega ⇑Φ))
    (hC : CFSG.Assembly.IsComponentOf C
      (glBlockCentralizer (StatedOmega ⇑Φ).subtype ({b} : Set (GL ι K)) ε))
    (fC : MulAut ↥C)
    (hfC : ∀ c : ↥C, ∀ v : ι → K,
      ggJSo2_ML (((fC c : ↥C) : StatedOmega ⇑Φ) : GL ι K) v =
        S (ggJSo2_ML (((c : ↥C) : StatedOmega ⇑Φ) : GL ι K) (S.symm v))) :
    GGMarkingAll (K := ↥C) fun _ _ _ I _ θ => kgInducedAut θ fC ∉ I := by
  have hnot : ¬ (Nat.card K = 2 ∧
      Module.finrank K (CFSG.RankThree.PartOne.KCOrthogonal.fixedSpace (ggJSo2_ML b)) = 4) := by
    rintro ⟨hK2, -⟩
    rw [hK2] at hK
    omega
  let hx := ggJSo2_oddOrderIsometry Φ hΦ b hb hodd
  let QW : QuadraticForm K
      (CFSG.RankThree.PartOne.KCOrthogonal.fixedSpace (ggJSo2_ML b)) :=
    Φ.comp (CFSG.RankThree.PartOne.KCOrthogonal.fixedSpace (ggJSo2_ML b)).subtype
  have hQW : (QuadraticMap.polarBilin QW).Nondegenerate := hx.polarBilin_fixed_nondegenerate
  exact kgFieldRestriction_orthogonalFixedBlock_quasisimple_of_semilinear
    Φ hΦ b hb hodd h8 hε h1 (QW := QW) (hQW := hQW) (hW := rfl)
    ⟨ggJSo2_dicksonDerived_generic Φ hΦ b hb hodd hnot⟩ hx eIso hdim hK hσ hS hSx hSQ C hC fC hfC

theorem kgFieldRestriction_orthogonalFixedBlock_nonsplit_of_semilinear
    {K : Type} [Field K] [Fintype K] [CharP K 2]
    {ι : Type} [Fintype ι] [DecidableEq ι]
    (Φ : QuadraticForm K (ι → K)) (hΦ : (QuadraticMap.polarBilin Φ).Nondegenerate)
    (b : GL ι K) (hb : b ∈ StatedOmega ⇑Φ) (hodd : Odd (orderOf b))
    (h8 : 8 ≤ Fintype.card ι)
    {ε : Matrix ι ι K}
    (hε : IsPrimAdjIdemIn (RingHom.id K)
      (LinearMap.toMatrix₂' K (QuadraticMap.polarBilin Φ))
      (Algebra.adjoin K (Units.val '' ({b} : Set (GL ι K)))) ε)
    (h1 : (b : Matrix ι ι K) * ε = ε)
    (hK : 4 ≤ Nat.card K)
    (hnotSplit : ¬ (Module.finrank K
        (CFSG.RankThree.PartOne.KCOrthogonal.fixedSpace (ggJSo2_ML b)) = 4 ∧
      ∃ T : Submodule K
        (CFSG.RankThree.PartOne.KCOrthogonal.fixedSpace (ggJSo2_ML b)),
        Module.finrank K T = 2 ∧
          ∀ x ∈ T, Φ x = 0))
    {σ : K ≃+* K} (hσ : σ ≠ 1) {S : (ι → K) ≃+ (ι → K)}
    (hS : ∀ (c : K) v, S (c • v) = σ c • S v)
    (hSx : ∀ v, S (ggJSo2_ML b v) = ggJSo2_ML b (S v))
    (hSQ : ∀ v, Φ (S v) = σ (Φ v))
    (C : Subgroup (StatedOmega ⇑Φ))
    (hC : CFSG.Assembly.IsComponentOf C
      (glBlockCentralizer (StatedOmega ⇑Φ).subtype ({b} : Set (GL ι K)) ε))
    (fC : MulAut ↥C)
    (hfC : ∀ c : ↥C, ∀ v : ι → K,
      ggJSo2_ML (((fC c : ↥C) : StatedOmega ⇑Φ) : GL ι K) v =
        S (ggJSo2_ML (((c : ↥C) : StatedOmega ⇑Φ) : GL ι K) (S.symm v))) :
    GGMarkingAll (K := ↥C) fun _ _ _ I _ θ => kgInducedAut θ fC ∉ I := by
  classical
  let W := CFSG.RankThree.PartOne.KCOrthogonal.fixedSpace (ggJSo2_ML b)
  let QW : QuadraticForm K W := Φ.comp W.subtype
  let hx := ggJSo2_oddOrderIsometry Φ hΦ b hb hodd
  have hQW : (QuadraticMap.polarBilin QW).Nondegenerate := hx.polarBilin_fixed_nondegenerate
  have hnot : ¬ (Nat.card K = 2 ∧
      Module.finrank K (CFSG.RankThree.PartOne.KCOrthogonal.fixedSpace (ggJSo2_ML b)) = 4) := by
    rintro ⟨hK2, -⟩
    rw [hK2] at hK
    omega
  have h4 : 4 ≤ Module.finrank K W := by
    by_contra hlt
    have hle3 : Module.finrank K W ≤ 3 := by omega
    have hEven : Even (Module.finrank K W) := by
      simpa [W] using hx.even_finrank_fixed
    have hle2 : Module.finrank K W ≤ 2 := by
      rcases hEven with ⟨s, hs⟩
      omega
    let F : Subgroup (StatedOmega ⇑Φ) :=
      glBlockCentralizer (StatedOmega ⇑Φ).subtype ({b} : Set (GL ι K)) ε
    let eB : ↥F ≃* ↥(CFSG.RankThree.Classical2.orthDerived QW) :=
      glBlockCentralizerEquivFixedDerived_of_generic Φ hΦ b hb hodd hε h1 hnot
    let CF : Subgroup ↥F := C.subgroupOf F
    have hCF : CFSG.Assembly.IsComponentOf CF ⊤ := by
      have hmapC : CF.map F.subtype = C := by
        rw [Subgroup.subgroupOf_map_subtype, inf_of_le_left hC.1]
      have hmapTop : (⊤ : Subgroup ↥F).map F.subtype = F := by
        rw [Subgroup.map_top, Subgroup.range_subtype]
      have hcomp : CFSG.Assembly.IsComponentOf (CF.map F.subtype)
          ((⊤ : Subgroup ↥F).map F.subtype) := by
        simpa [hmapC, hmapTop] using hC
      exact (CFSG.LocalAnalysis.ComponentInitial.isComponentOf_map_iff
        (f := F.subtype) F.subtype_injective).1 hcomp
    let C' : Subgroup ↥(CFSG.RankThree.Classical2.orthDerived QW) := CF.map eB.toMonoidHom
    have hC' : CFSG.Assembly.IsComponentOf C' ⊤ := by
      simpa [C'] using CFSG.LocalAnalysis.ComponentInitial.isComponentOf_map_of_injective
        hCF eB.toMonoidHom eB.injective
    let eCmap : ↥CF ≃* ↥C' := Subgroup.equivMapOfInjective CF eB.toMonoidHom eB.injective
    have hC'q : CFSG.Assembly.IsQuasisimple ↥C' :=
      CFSG.Assembly.IsQuasisimple.of_mulEquiv eCmap.symm hCF.2.2
    have hO : Group.IsSolvable ↥(TauCeti.QuadraticMap.orthogonalGroup QW) :=
      CFSG.HardMathSupport.Dickson.Sec6.I1431.t6orth_isSolvable_orthogonalGroup_of_finrank_le_two
        hQW hle2
    have hΩ : Group.IsSolvable ↥(CFSG.RankThree.Classical2.orthDerived QW) :=
      Group.isSolvable_of_isSolvable_injective
        (f := Subgroup.inclusion (CFSG.RankThree.Classical.orthDerived_le_orthogonalGroup QW))
        (Subgroup.inclusion_injective _)
    have hC'solv : Group.IsSolvable ↥C' :=
      Group.isSolvable_of_isSolvable_injective
        (f := Subgroup.inclusion hC'.1) (Subgroup.inclusion_injective _)
    have hC'native : CFSG.IsQuasisimple ↥C' :=
      (CFSG.ComponentClassification.AssemblyBPredicates.isQuasisimple_iff_native _).1 hC'q
    exact CFSG.LocalAnalysis.ComponentInitial.not_isSolvable_of_isQuasisimple hC'native hC'solv
  let d := Module.finrank K W
  let eW : W ≃ₗ[K] (Fin d → K) := (Module.finBasis K W).equivFun
  let Φ₁ : QuadraticForm K (Fin d → K) := QW.comp eW.symm
  let eIso : QW.IsometryEquiv Φ₁ :=
    { toLinearEquiv := eW
      map_app' := by intro w; simp [Φ₁, eW] }
  have hdim : 6 ≤ d ∨ (d = 4 ∧ ¬ ∃ T : Submodule K (Fin d → K),
      Module.finrank K T = 2 ∧ ∀ x ∈ T, Φ₁ x = 0) := by
    have hEven : Even d := by
      simpa [d, W] using hx.even_finrank_fixed
    have h4d : 4 ≤ d := by simpa [d] using h4
    by_cases hd4 : d = 4
    · right
      refine ⟨hd4, ?_⟩
      rintro ⟨T, hT2, hT0⟩
      apply hnotSplit
      refine ⟨by simpa [d, W] using hd4, T.map eW.symm.toLinearMap, ?_, ?_⟩
      · rw [LinearEquiv.finrank_map_eq]
        exact hT2
      · intro y hy
        obtain ⟨x, hxT, rfl⟩ := hy
        have h := hT0 x hxT
        change Φ ((eW.symm x : W) : ι → K) = 0
        exact h
    · left
      rcases hEven with ⟨s, hs⟩
      omega
  exact kgFieldRestriction_orthogonalFixedBlock_coordinate_of_semilinear Φ hΦ b hb hodd h8 hε h1 eIso
    hdim hK hσ hS hSx hSQ C hC fC hfC

theorem kgfni_kgInducedAut_congr_local
    {X Y R : Type*} [Group X] [Group Y] [Group R]
    (e : X ≃* Y) (θ : X ⧸ Subgroup.center X ≃* R) (f : MulAut X) :
    kgInducedAut ((centerQuotCongr e).symm.trans θ) (e.symm.trans (f.trans e)) =
      kgInducedAut θ f := by
  ext x
  obtain ⟨q, rfl⟩ := θ.surjective x
  obtain ⟨y, rfl⟩ := QuotientGroup.mk_surjective q
  simp [kgInducedAut, MulAut.congr_apply, centerQuotAut_mk, centerQuotCongr_mk,
    MulEquiv.trans_apply]
  rw [← centerQuotCongr_mk e (f y)]
  exact MulEquiv.symm_apply_apply (centerQuotCongr e) _

theorem kgfni_kgInducedAut_transport
    {X Y R : Type*} [Group X] [Group Y] [Group R]
    (e : X ≃* Y) (θ : Y ⧸ Subgroup.center Y ≃* R) (fX : MulAut X) (fY : MulAut Y)
    (hf : fY = e.symm.trans (fX.trans e)) :
    kgInducedAut ((centerQuotCongr e).trans θ) fX =
      kgInducedAut θ fY := by
  have h := kgfni_kgInducedAut_congr_local e ((centerQuotCongr e).trans θ) fX
  have hmark : (centerQuotCongr e).symm.trans ((centerQuotCongr e).trans θ) = θ := by
    ext y
    simp [MulEquiv.trans_apply]
  have h' : kgInducedAut θ fY = kgInducedAut ((centerQuotCongr e).trans θ) fX := by
    simpa [hf, hmark] using h
  exact h'.symm

theorem ggMarkingAll_transport
    {X Y : Type*} [Group X] [Group Y] (e : X ≃* Y)
    (fX : MulAut X) (fY : MulAut Y)
    (hf : fY = e.symm.trans (fX.trans e))
    (hY : GGMarkingAll (K := X) fun _ _ _ I _ θ => kgInducedAut θ fX ∉ I) :
    GGMarkingAll (K := Y) fun _ _ _ I _ θ => kgInducedAut θ fY ∉ I := by
  refine ggMarkingAll_congr e ?_ hY
  intro lab R _ I F θ hθ
  rw [← kgfni_kgInducedAut_transport e θ fX fY hf]
  exact hθ

theorem mulAut_congr_apply_apply
    {X Y : Type*} [Group X] [Group Y] (e : X ≃* Y) (f : MulAut X) (x : X) :
    MulAut.congr e f (e x) = e (f x) := by
  rw [MulAut.congr_apply]
  simp [MulEquiv.trans_apply]

theorem matrixLinearEquiv_stated_of_orthDerived
    {K : Type} [Field K] {d : ℕ} (Q : QuadraticForm K (Fin d → K))
    (x : CFSG.RankThree.Classical2.orthDerived Q) :
    matrixLinearEquiv
      ((MulEquiv.subgroupCongr
        (CFSG.RankThree.PartOne.AUTSL.matrixDerived_eq_statedOmega Q)
        ((CFSG.RankThree.PartOne.KCOrthComm.matrixDerivedEquiv Q).symm x) :
          StatedOmega ⇑Q) : GL (Fin d) K) =
      (x : (Fin d → K) ≃ₗ[K] (Fin d → K)) := by
  change matrixLinearEquiv
    ((CFSG.RankThree.PartOne.KCOrthComm.matrixDerivedEquiv Q).symm x).val = _
  rw [← CFSG.RankThree.PartOne.KCOrthComm.coe_matrixDerivedEquiv,
    MulEquiv.apply_symm_apply]

theorem componentMap_coe
    {A B D : Type} [Group A] [Group B] [Group D]
    (F C : Subgroup A) (hCF : C ≤ F) (eB : F ≃* B) (eO : B ≃* D)
    (x : C) :
    (((((Subgroup.subgroupOfEquivOfLe hCF).symm.trans
      (Subgroup.equivMapOfInjective (C.subgroupOf F) eB.toMonoidHom eB.injective)).trans
      (Subgroup.equivMapOfInjective
        ((C.subgroupOf F).map eB.toMonoidHom) eO.toMonoidHom eO.injective)) x) : D) =
      eO (eB ⟨x.val, hCF x.property⟩) := by
  rfl

theorem fixedBlock_component_transport_semilinear
    {K : Type} [Field K] [Fintype K] [CharP K 2]
    {ι : Type} [Fintype ι] [DecidableEq ι]
    (Φ : QuadraticForm K (ι → K)) (hΦ : (QuadraticMap.polarBilin Φ).Nondegenerate)
    (b : GL ι K) (hb : b ∈ StatedOmega ⇑Φ) (hodd : Odd (orderOf b))
    {ε : Matrix ι ι K}
    (hε : IsPrimAdjIdemIn (RingHom.id K)
      (LinearMap.toMatrix₂' K (QuadraticMap.polarBilin Φ))
      (Algebra.adjoin K (Units.val '' ({b} : Set (GL ι K)))) ε)
    (h1 : (b : Matrix ι ι K) * ε = ε) (hK : 4 ≤ Nat.card K)
    {σ : K ≃+* K} {S : (ι → K) ≃+ (ι → K)}
    (hS : ∀ (c : K) v, S (c • v) = σ c • S v)
    (hSx : ∀ v, S (ggJSo2_ML b v) = ggJSo2_ML b (S v))
    (hSQ : ∀ v, Φ (S v) = σ (Φ v))
    (C : Subgroup (StatedOmega ⇑Φ))
    (hC : CFSG.Assembly.IsComponentOf C
      (glBlockCentralizer (StatedOmega ⇑Φ).subtype ({b} : Set (GL ι K)) ε))
    (fC : MulAut ↥C)
    (hfC : ∀ (c : ↥C) (v : ι → K),
      ggJSo2_ML (((fC c : ↥C) : StatedOmega ⇑Φ) : GL ι K) v =
        S (ggJSo2_ML (((c : ↥C) : StatedOmega ⇑Φ) : GL ι K) (S.symm v))) :
    ∃ (C' : Subgroup (StatedOmega ⇑(fixedBlockForm Φ b)))
      (hC' : CFSG.Assembly.IsComponentOf C' ⊤) (eC : ↥C ≃* ↥C') (fC' : MulAut ↥C'),
      fC' = MulAut.congr eC fC ∧
      (∀ c : ↥C, eC (fC c) = fC' (eC c)) ∧
      (∀ (c' : ↥C') (v : Fin (Module.finrank K
          (CFSG.RankThree.PartOne.KCOrthogonal.fixedSpace (ggJSo2_ML b))) → K),
        matrixLinearEquiv (((fC' c' : ↥C') : StatedOmega ⇑(fixedBlockForm Φ b)) : GL _ K) v =
          coordinateSemilinearMap (fixedBlockSimilarityPair Φ b hS hSx hSQ).val
            (matrixLinearEquiv ((c' : StatedOmega ⇑(fixedBlockForm Φ b)) : GL _ K)
              ((coordinateSemilinearMap (fixedBlockSimilarityPair Φ b hS hSx hSQ).val).symm v))) := by
  classical
  let W := CFSG.RankThree.PartOne.KCOrthogonal.fixedSpace (ggJSo2_ML b)
  let Φ₁ : QuadraticForm K (Fin (Module.finrank K W) → K) := fixedBlockForm Φ b
  let eIso : (Φ.comp W.subtype).IsometryEquiv Φ₁ := fixedBlockIsometryEquiv Φ b
  have hnot : ¬ (Nat.card K = 2 ∧ Module.finrank K W = 4) := by
    rintro ⟨hK2, -⟩
    rw [hK2] at hK
    omega
  let hD : CFSG.RankThree.PartOne.DicksonDerived (Φ.comp W.subtype)
      (ggJSo2_oddOrderIsometry Φ hΦ b hb hodd).polarBilin_fixed_nondegenerate :=
    ggJSo2_dicksonDerived_generic Φ hΦ b hb hodd hnot
  let F : Subgroup (StatedOmega ⇑Φ) :=
    glBlockCentralizer (StatedOmega ⇑Φ).subtype ({b} : Set (GL ι K)) ε
  let eB : ↥F ≃* ↥(CFSG.RankThree.Classical2.orthDerived Φ₁) :=
    glBlockCentralizerEquivFixedDerivedBasis Φ hΦ b hb hodd hε h1 hD eIso
  let CF : Subgroup ↥F := C.subgroupOf F
  have hCF : CFSG.Assembly.IsComponentOf CF ⊤ := by
    have hmapC : CF.map F.subtype = C := by
      rw [Subgroup.subgroupOf_map_subtype, inf_of_le_left hC.1]
    have hmapTop : (⊤ : Subgroup ↥F).map F.subtype = F := by
      rw [Subgroup.map_top, Subgroup.range_subtype]
    have hcomp : CFSG.Assembly.IsComponentOf (CF.map F.subtype) ((⊤ : Subgroup ↥F).map F.subtype) := by
      simpa [hmapC, hmapTop] using hC
    exact (isComponentOf_map_iff (f := F.subtype) F.subtype_injective).1 hcomp
  let Corth := CF.map eB.toMonoidHom
  have hCorth : CFSG.Assembly.IsComponentOf Corth ⊤ := by
    simpa [Corth] using CFSG.LocalAnalysis.ComponentInitial.isComponentOf_map_of_injective hCF eB.toMonoidHom eB.injective
  let eCF : ↥C ≃* ↥CF := (Subgroup.subgroupOfEquivOfLe hC.1).symm
  let eCorth : ↥CF ≃* ↥Corth := Subgroup.equivMapOfInjective CF eB.toMonoidHom eB.injective
  let eS : matrixDerived Φ₁ ≃* StatedOmega ⇑Φ₁ :=
    MulEquiv.subgroupCongr (matrixDerived_eq_statedOmega Φ₁)
  let eO : CFSG.RankThree.Classical2.orthDerived Φ₁ ≃* StatedOmega ⇑Φ₁ :=
    (CFSG.RankThree.PartOne.KCOrthComm.matrixDerivedEquiv Φ₁).symm.trans eS
  let C' := Corth.map eO.toMonoidHom
  have hC' : CFSG.Assembly.IsComponentOf C' ⊤ := by
    simpa [C'] using CFSG.LocalAnalysis.ComponentInitial.isComponentOf_map_of_injective hCorth eO.toMonoidHom eO.injective
  let eCmap : ↥Corth ≃* ↥C' := Subgroup.equivMapOfInjective Corth eO.toMonoidHom eO.injective
  let eC : ↥C ≃* ↥C' := (eCF.trans eCorth).trans eCmap
  let fC' := MulAut.congr eC fC
  refine ⟨C', hC', eC, fC', rfl, ?_, ?_⟩
  · intro c
    exact (mulAut_congr_apply_apply eC fC c).symm
  · intro c' v
    let c := eC.symm c'
    have hc : eC c = c' := eC.apply_symm_apply c'
    rw [← hc]
    have hf' : fC' (eC c) = eC (fC c) := mulAut_congr_apply_apply eC fC c
    rw [hf']
    have hcoe (x : C) :
        matrixLinearEquiv (((eC x : C') : StatedOmega ⇑Φ₁) : GL _ K) =
          ((eB ⟨x.val, hC.1 x.property⟩ : CFSG.RankThree.Classical2.orthDerived Φ₁) :
            (Fin (Module.finrank K W) → K) ≃ₗ[K] (Fin (Module.finrank K W) → K)) := by
      have heC : ((eC x : C') : StatedOmega ⇑Φ₁) = eO (eB ⟨x.val, hC.1 x.property⟩) :=
        componentMap_coe F C hC.1 eB eO x
      rw [heC]
      exact matrixLinearEquiv_stated_of_orthDerived Φ₁ _
    rw [hcoe, hcoe]
    let Tσ := fixedBasisSemilin eIso.toLinearEquiv (fixedSemilinRestrict hSx)
    have hp : coordinateSemilinearMap (fixedBlockSimilarityPair Φ b hS hSx hSQ).val = Tσ := by
      change coordinateSemilinearMap
        (SemiSim.toCoordinatePair _ (fixedBlockSemisim Φ b hS hSx hSQ)) = Tσ
      rw [SemiSim.coordinateSemilinearMap_toCoordinatePair]
      rfl
    have hsq := glBlockCentralizerEquivFixedDerivedBasis_square Φ hΦ b hb hodd hε h1 hD eIso
      (S := S) hSx (g := ⟨c, hC.1 c.2⟩) (g' := ⟨fC c, hC.1 (fC c).2⟩)
      (fun v => hfC c v) v
    have heq := congrArg
      (fun T : (Fin (Module.finrank K W) → K) ≃+ (Fin (Module.finrank K W) → K) =>
        T ((eB ⟨c, hC.1 c.2⟩).val (T.symm v))) hp
    exact hsq.trans heq.symm

theorem kgFieldRestriction_orthogonalFixedBlock_of_semilinear
    {K : Type} [Field K] [Fintype K] [CharP K 2]
    {ι : Type} [Fintype ι] [DecidableEq ι]
    (Φ : QuadraticForm K (ι → K)) (hΦ : (QuadraticMap.polarBilin Φ).Nondegenerate)
    (b : GL ι K) (hb : b ∈ StatedOmega ⇑Φ) (hodd : Odd (orderOf b))
    (h8 : 8 ≤ Fintype.card ι)
    {ε : Matrix ι ι K}
    (hε : IsPrimAdjIdemIn (RingHom.id K)
      (LinearMap.toMatrix₂' K (QuadraticMap.polarBilin Φ))
      (Algebra.adjoin K (Units.val '' ({b} : Set (GL ι K)))) ε)
    (h1 : (b : Matrix ι ι K) * ε = ε)
    (hK : 4 ≤ Nat.card K)
    {σ : K ≃+* K} (hσ : σ ≠ 1) {S : (ι → K) ≃+ (ι → K)}
    (hS : ∀ (c : K) v, S (c • v) = σ c • S v)
    (hSx : ∀ v, S (ggJSo2_ML b v) = ggJSo2_ML b (S v))
    (hSQ : ∀ v, Φ (S v) = σ (Φ v))
    (C : Subgroup (StatedOmega ⇑Φ))
    (hC : CFSG.Assembly.IsComponentOf C
      (glBlockCentralizer (StatedOmega ⇑Φ).subtype ({b} : Set (GL ι K)) ε))
    (fC : MulAut ↥C)
    (hfC : ∀ c : ↥C, ∀ v : ι → K,
      ggJSo2_ML (((fC c : ↥C) : StatedOmega ⇑Φ) : GL ι K) v =
        S (ggJSo2_ML (((c : ↥C) : StatedOmega ⇑Φ) : GL ι K) (S.symm v))) :
    GGMarkingAll (K := ↥C) fun _ _ _ I _ θ => kgInducedAut θ fC ∉ I := by
  classical
  let W := CFSG.RankThree.PartOne.KCOrthogonal.fixedSpace (ggJSo2_ML b)
  by_cases hd4 : Module.finrank K W = 4
  · by_cases hsplitW : ∃ T : Submodule K W,
        Module.finrank K T = 2 ∧ ∀ x ∈ T, Φ x = 0
    · obtain ⟨C', hC', eC, fC', hfC'def, hintertw, hsquare⟩ :=
        fixedBlock_component_transport_semilinear Φ hΦ b hb hodd hε h1 hK hS hSx hSQ C hC fC hfC
      let Φ₁ : QuadraticForm K (Fin (Module.finrank K W) → K) := fixedBlockForm Φ b
      let eIso : (Φ.comp W.subtype).IsometryEquiv Φ₁ := fixedBlockIsometryEquiv Φ b
      have hx := ggJSo2_oddOrderIsometry Φ hΦ b hb hodd
      have hQW : (QuadraticMap.polarBilin (Φ.comp W.subtype)).Nondegenerate :=
        hx.polarBilin_fixed_nondegenerate
      have hQ : (QuadraticMap.polarBilin Φ₁).Nondegenerate :=
        CFSG.GroupTheory.WeirSylow.nondegenerate_polarBilin_of_isometryEquiv eIso hQW
      have hsplitQ : ∃ T : Submodule K (Fin (Module.finrank K W) → K),
          Module.finrank K T = 2 ∧ ∀ x ∈ T, Φ₁ x = 0 := by
        obtain ⟨T, hT, hT0⟩ := hsplitW
        refine ⟨T.map eIso.toLinearEquiv.toLinearMap, ?_, ?_⟩
        · rw [LinearEquiv.finrank_map_eq]
          exact hT
        · intro y hy
          obtain ⟨x, hxT, rfl⟩ := hy
          have h := hT0 x hxT
          exact (eIso.map_app' x).trans h
      haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
      letI : Algebra (ZMod 2) K := ZMod.algebra _ _
      let e := Module.finrank (ZMod 2) K
      have hKcard : Nat.card K = 2 ^ e :=
        (FiniteField.pow_finrank_eq_natCard 2 K).symm
      have he2 : 2 ≤ e := by
        by_contra hlt
        have he1 : e ≤ 1 := by omega
        have h2 : 2 ^ e ≤ 2 := Nat.pow_le_pow_right (by norm_num) he1
        rw [hKcard] at hK
        omega
      let g := fixedBlockSimilarityPair Φ b hS hSx hSQ
      have hg : g.val.right ≠ 1 := by
        simpa [g, fixedBlockSimilarityPair_right Φ b hS hSx hSQ] using hσ
      have hfC' : ∀ c : ↥C', ∀ v : Fin (Module.finrank K W) → K,
          CFSG.ClassicalGroups.Orthogonal.toLinEquiv (Fin (Module.finrank K W)) K
            (((fC' c : ↥C') : StatedOmega ⇑Φ₁) : GL (Fin (Module.finrank K W)) K) v =
            coordinateSemilinearMap g.val
              (CFSG.ClassicalGroups.Orthogonal.toLinEquiv (Fin (Module.finrank K W)) K
                (((c : ↥C') : StatedOmega ⇑Φ₁) : GL (Fin (Module.finrank K W)) K)
                ((coordinateSemilinearMap g.val).symm v)) := by
        intro c v
        change matrixLinearEquiv (((fC' c : ↥C') : StatedOmega ⇑Φ₁) :
            GL (Fin (Module.finrank K W)) K) v =
          coordinateSemilinearMap g.val
            (matrixLinearEquiv (((c : ↥C') : StatedOmega ⇑Φ₁) :
              GL (Fin (Module.finrank K W)) K)
              ((coordinateSemilinearMap g.val).symm v))
        exact hsquare c v
      have hmark := kgFieldRestriction_statedOmegaFourComponent_of_semilinearPair
        (hd := hd4) Φ₁ hQ hsplitQ hKcard he2 g hg C' hC' fC' hfC'
      have hback : fC = (eC.symm).symm.trans (fC'.trans eC.symm) := by
        apply MulEquiv.ext
        intro c
        apply eC.injective
        change eC (fC c) = eC (eC.symm (fC' (eC c)))
        rw [eC.apply_symm_apply]
        exact hintertw c
      exact ggMarkingAll_transport eC.symm fC' fC hback hmark
    · exact kgFieldRestriction_orthogonalFixedBlock_nonsplit_of_semilinear
        Φ hΦ b hb hodd h8 hε h1 hK
        (by rintro ⟨_, T, hT, hT0⟩; exact hsplitW ⟨T, hT, hT0⟩) hσ hS hSx hSQ C hC fC hfC
  · exact kgFieldRestriction_orthogonalFixedBlock_nonsplit_of_semilinear
      Φ hΦ b hb hodd h8 hε h1 hK
      (by rintro ⟨hd, _⟩; exact hd4 hd) hσ hS hSx hSQ C hC fC hfC
section OrthogonalHighRows

theorem kgFieldRestriction_orthogonalCentralizer_of_semilinear
    {K : Type} [Field K] [Fintype K] [CharP K 2]
    {ι : Type} [Fintype ι] [DecidableEq ι]
    (Φ : QuadraticForm K (ι → K)) (hΦ : (QuadraticMap.polarBilin Φ).Nondegenerate)
    (h8 : 8 ≤ Fintype.card ι) (b : GL ι K)
    (hb : b ∈ StatedOmega ⇑Φ) (hodd : Odd (orderOf b))
    {σ : K ≃+* K} (hσ : σ ≠ 1) {S : (ι → K) ≃+ (ι → K)}
    (hS : ∀ (c : K) v, S (c • v) = σ c • S v)
    (hSx : ∀ v, S (ggJSo2_ML b v) = ggJSo2_ML b (S v))
    (hSQ : ∀ v, Φ (S v) = σ (Φ v))
    (hcardK : 4 ≤ Nat.card K)
    (hfix : ∀ a ∈ CFSG.RankThree.PartOne.KCPrimary.primaryFactors
      (Matrix.toLin' (b : Matrix ι ι K)), a.map (σ : K →+* K) = a)
    (C : Subgroup (StatedOmega ⇑Φ))
    (hC : CFSG.Assembly.IsComponentOf C (omegaCentralizerSubgroup Φ b))
    (fC : MulAut ↥C)
    (hfC : ∀ c : ↥C, ∀ v : ι → K,
      ggJSo2_ML (((fC c : ↥C) : StatedOmega ⇑Φ) : GL ι K) v =
        S (ggJSo2_ML (((c : ↥C) : StatedOmega ⇑Φ) : GL ι K) (S.symm v))) :
    GGMarkingAll (K := ↥C) fun _ _ _ I _ θ => kgInducedAut θ fC ∉ I := by
  obtain ⟨ε, hε, hCε⟩ :=
    exists_isPrimAdjIdemIn_isComponentOf_glBlockCentralizer Φ hΦ h8 b hb hodd C hC
  by_cases h1 : (b : Matrix ι ι K) * ε = ε
  · exact kgFieldRestriction_orthogonalFixedBlock_of_semilinear
      Φ hΦ b hb hodd h8 hε h1 hcardK (σ := σ) hσ (S := S)
      hS hSx hSQ C hCε fC hfC
  · classical
    let G : Matrix ι ι K := LinearMap.toMatrix₂' K (QuadraticMap.polarBilin Φ)
    have hG : IsUnit G.det := by
      simpa [G] using ggOmegaBlk_G_isUnit_det Φ hΦ
    have hGh : Matrix.transpose (G.map (RingHom.id K)) = G := by
      simpa [G] using ggOmegaBlk_G_transpose Φ
    have hbquad : ∀ v : ι → K, Φ (Matrix.mulVec ((b : GL ι K) : Matrix ι ι K) v) = Φ v := by
      have hbiso := CFSG.GroupTheory.WeirSylow.statedOmega_le_isometryCore ⇑Φ hb
      intro v
      exact CFSG.GroupTheory.WeirSylow.apply_mulVec_of_mem_isometryCore hbiso v
    have hSUb : Matrix.transpose (((b : GL ι K) : Matrix ι ι K).map (RingHom.id K)) *
        G * ((b : GL ι K) : Matrix ι ι K) = G := by
      simpa [G] using omegaSemilin_isometry_mul_eq Φ b hbquad
    have hScomm : ∀ s ∈ ({b} : Set (GL ι K)), ∀ s' ∈ ({b} : Set (GL ι K)),
        Commute s s' := by
      intro s hs s' hs'
      rw [Set.mem_singleton_iff] at hs hs'
      subst hs
      subst hs'
      exact Commute.refl _
    have hSU' : ∀ s ∈ ({b} : Set (GL ι K)),
        Matrix.transpose (((s : GL ι K) : Matrix ι ι K).map (RingHom.id K)) *
          G * ((s : GL ι K) : Matrix ι ι K) = G := by
      intro s hs
      rw [Set.mem_singleton_iff] at hs
      subst hs
      exact hSUb
    obtain ⟨e, he, hee, hcase⟩ :=
      CFSG.StandardType.ClassicalPosition.exists_isPrimIdemIn_of_isPrimAdjIdemIn
        (σ := RingHom.id K) (hσ := fun x => rfl) (G := G) hG hGh
        (S := ({b} : Set (GL ι K))) hScomm hSU' hε
    have hx : CFSG.RankThree.PartOne.KCOrthogonal.OddOrderIsometry Φ (orderOf b)
        (toLinEquiv ι K b) := by
      simpa [ggJSo2_ML, CFSG.ClassicalGroups.Orthogonal.toLinEquiv] using
        ggJSo2_oddOrderIsometry Φ hΦ b hb hodd
    have hsqMat : Squarefree (minpoly K (Matrix.toLin' (b : Matrix ι ι K))) := by
      rw [← ggOmegaBlk_toLinEquiv_toLinearMap b]
      exact hx.squarefree_minpoly
    rcases hcase with heEq | ⟨hene, he'ne, heps⟩
    ·
      obtain ⟨a, ha, hae⟩ := ggOmegaBlk_prim_idem_eq_primaryProjection b hsqMat he
      have haeAlg : Matrix.toLinAlgEquiv' e =
          primaryProjection (toLinEquiv ι K b).toLinearMap a := by
        simpa [ggOmegaBlk_toLinEquiv_toLinearMap b,
          ggOmegaBlk_toLinAlgEquiv'_eq_toLin'] using hae
      have hax : a ∈ primaryFactors (toLinEquiv ι K b).toLinearMap := by
        simpa [ggOmegaBlk_toLinEquiv_toLinearMap b] using ha
      have haeε : Matrix.toLin' ε =
          primaryProjection (Matrix.toLin' (b : Matrix ι ι K)) a := by
        rw [← heEq]
        simpa [ggOmegaBlk_toLinAlgEquiv'_eq_toLin'] using hae
      have hself0 := selfDual_primaryProjection_of_prim_adjoint
        Φ hΦ b hb hodd hε ha haeε
      have hself : a = reciprocalPolynomial a := hself0.symm
      have hne1 : a ≠ X - 1 := ggJSo3_ne_one b hodd ha haeε h1
      haveI : Fact (Irreducible a) :=
        ⟨CFSG.RankThree.PartOne.KCPrimary.irreducible_of_mem_primaryFactors ha⟩
      have haσ : a.map (σ : K →+* K) = a := hfix a ha
      exact kgFieldRestriction_orthogonalSelfDualBlock_of_semilinear
        Φ hΦ h8 b hx hodd hax haeAlg hself hne1 heEq.symm
        hS hSx hSQ haσ hσ C hCε fC hfC
    ·
      let e' : Matrix ι ι K := formAdj (RingHom.id K) G e
      have he' : IsPrimIdemIn (Algebra.adjoin K (Units.val '' ({b} : Set (GL ι K)))) e' :=
        omegaSemilin_isPrimIdemIn_formAdj hG hGh b hSUb he
      obtain ⟨a, ha, hae⟩ := ggOmegaBlk_prim_idem_eq_primaryProjection b hsqMat he
      obtain ⟨a', ha', ha'e⟩ := ggOmegaBlk_prim_idem_eq_primaryProjection b hsqMat he'
      have haeAlg : Matrix.toLinAlgEquiv' e =
          primaryProjection (toLinEquiv ι K b).toLinearMap a := by
        simpa [ggOmegaBlk_toLinEquiv_toLinearMap b,
          ggOmegaBlk_toLinAlgEquiv'_eq_toLin'] using hae
      have ha'eAlg : Matrix.toLinAlgEquiv' e' =
          primaryProjection (toLinEquiv ι K b).toLinearMap a' := by
        simpa [ggOmegaBlk_toLinEquiv_toLinearMap b,
          ggOmegaBlk_toLinAlgEquiv'_eq_toLin'] using ha'e
      have hax : a ∈ primaryFactors (toLinEquiv ι K b).toLinearMap := by
        simpa [ggOmegaBlk_toLinEquiv_toLinearMap b] using ha
      have ha'x : a' ∈ primaryFactors (toLinEquiv ι K b).toLinearMap := by
        simpa [ggOmegaBlk_toLinEquiv_toLinearMap b] using ha'
      have hεePair : ε = e + e' := by
        simpa [e'] using heps
      have hnePair : e ≠ e' := by
        intro h
        exact he'ne (by simpa [e'] using h.symm)
      have hrec := paired_prim_idem_primary_reciprocal Φ hΦ b hx hax ha'x
        haeAlg ha'eAlg hεePair hnePair hε he he'
      have ha'eRec : Matrix.toLinAlgEquiv' e' =
          primaryProjection (toLinEquiv ι K b).toLinearMap (reciprocalPolynomial a) := by
        rw [← hrec.1]
        exact ha'eAlg
      have haσ : a.map (σ : K →+* K) = a := hfix a ha
      haveI : Fact (Irreducible a) :=
        ⟨CFSG.RankThree.PartOne.KCPrimary.irreducible_of_mem_primaryFactors ha⟩
      let basis : Module.Basis (Fin (Module.finrank (AdjoinRoot a)
          (primaryComponent (toLinEquiv ι K b).toLinearMap a)))
          (AdjoinRoot a) (primaryComponent (toLinEquiv ι K b).toLinearMap a) :=
        Module.finBasisOfFinrankEq _ _ rfl
      exact kgFieldRestriction_orthogonalPairedBlock_of_semilinear
        Φ hΦ h8 b hx hodd hax haeAlg ha'eRec hrec.2 hεePair
        basis hS hSx haσ hσ C hCε fC hfC

private lemma ggJSo2_ML_subgroupCongr_apply
    {K : Type} [Field K] {d : ℕ} {Q : QuadraticForm K (Fin d → K)}
    (x : matrixDerived Q) (v : Fin d → K) :
    ggJSo2_ML ((((MulEquiv.subgroupCongr
      (CFSG.RankThree.PartOne.AUTSL.matrixDerived_eq_statedOmega Q)) x :
        StatedOmega ⇑Q) : GL (Fin d) K)) v =
      matrixLinearEquiv (x : GL (Fin d) K) v := by
  simp [ggJSo2_ML, CFSG.ClassicalGroups.Orthogonal.toLinEquiv_apply,
    MulEquiv.subgroupCongr_apply, matrixLinearEquiv_apply]

private lemma conjAct_matrixLinearEquiv_apply
    {K : Type} [Field K] {d : ℕ} {Q : QuadraticForm K (Fin d → K)}
    (g : similarityPairs Q) (X : matrixDerived Q) (v : Fin d → K) :
    matrixLinearEquiv (((CFSG.RankThree.PartOne.AUTSL.conjAct Q g X : matrixDerived Q) : GL (Fin d) K)) v =
      CFSG.RankThree.PartOne.KCOrthComm.pairMap Q g
        (matrixLinearEquiv (X : GL (Fin d) K)
          ((CFSG.RankThree.PartOne.KCOrthComm.pairMap Q g).symm v)) := by
  rw [CFSG.RankThree.PartOne.AUTSL.conjAct_apply, matrixDerivedConjugation_val]
  change matrixLinearEquiv (matrixConjugation g.val X.val) v =
    CFSG.RankThree.PartOne.KCOrthComm.pairMap Q g
      (matrixLinearEquiv (X : GL (Fin d) K)
        ((CFSG.RankThree.PartOne.KCOrthComm.pairMap Q g).symm v))
  rw [matrixConjugation_vector]

theorem kgFieldRestriction_orthogonalSuppliedSemilinear
    {K : Type} [Field K] [Fintype K] [CharP K 2]
    {d p : ℕ} {Q : QuadraticForm K (Fin d → K)}
    (hQ : (QuadraticMap.polarBilin Q).Nondegenerate)
    (data : SemilinearRepresentative Q p)
    (hp : p.Prime) (hp2 : p ≠ 2)
    {R : Type} [Group R] (Theta : R ≃* matrixDerived Q)
    {h f : MulAut R}
    (hgamma : MulAut.congr Theta h = MulAut.conj data.gamma)
    (hfTheta : MulAut.congr Theta f = CFSG.RankThree.PartOne.AUTSL.conjAct Q data.g)
    (hd : 8 ≤ d) (hcardK : 4 ≤ Nat.card K)
    (J0 : Subgroup R)
    (hJ0 : CFSG.Assembly.IsComponentOf J0
      (MonoidHom.eqLocus (h : R →* R) (MonoidHom.id R)))
    (fprime : MulAut J0)
    (hfprime : ∀ j : J0, ((fprime j : J0) : R) = f j) :
    GGMarkingAll (K := ↥J0) fun _ _ _ I _ theta => kgInducedAut theta fprime ∉ I := by
  classical
  let eOmega : matrixDerived Q ≃* StatedOmega ⇑Q :=
    MulEquiv.subgroupCongr
      (CFSG.RankThree.PartOne.AUTSL.matrixDerived_eq_statedOmega Q)
  let e : R ≃* StatedOmega ⇑Q := Theta.trans eOmega
  let bStated : StatedOmega ⇑Q := eOmega data.gamma
  let bGL : GL (Fin d) K := (bStated : GL (Fin d) K)
  let sigma : K ≃+* K := data.g.val.right
  let S : (Fin d → K) ≃+ (Fin d → K) :=
    CFSG.RankThree.PartOne.KCOrthComm.pairMap Q data.g
  have hgammaE : MulAut.congr e h = MulAut.conj bStated := by
    have htrans : MulAut.congr e h =
        MulAut.congr eOmega (MulAut.congr Theta h) := by
      ext x
      simp [e, MulAut.congr_apply, MulEquiv.trans_apply]
    rw [htrans, hgamma]
    exact CFSG.ComponentClassification.OuterAutomorphisms.congr_conj eOmega data.gamma
  let C : Subgroup (StatedOmega ⇑Q) := J0.map e.toMonoidHom
  have hCeq : CFSG.Assembly.IsComponentOf C
      (MonoidHom.eqLocus (MulAut.conj bStated : StatedOmega ⇑Q →* StatedOmega ⇑Q)
        (MonoidHom.id (StatedOmega ⇑Q))) := by
    simpa [C] using component_transport_of_mulEquiv e hgammaE J0 hJ0
  have hcent : MonoidHom.eqLocus
        (MulAut.conj bStated : StatedOmega ⇑Q →* StatedOmega ⇑Q)
        (MonoidHom.id (StatedOmega ⇑Q)) = omegaCentralizerSubgroup Q bGL := by
    rw [CFSG.RankThree.PartOne.F106.eqLocus_conj_eq_centralizer]
    ext x
    simp only [omegaCentralizerSubgroup, Subgroup.mem_comap,
      Subgroup.mem_centralizer_singleton_iff]
    constructor
    · intro hx
      exact congrArg (fun z : StatedOmega ⇑Q => (z : GL (Fin d) K)) hx
    · intro hx
      exact Subtype.ext hx
  have hComega : CFSG.Assembly.IsComponentOf C (omegaCentralizerSubgroup Q bGL) := by
    simpa [hcent] using hCeq
  have hbOmega : bGL ∈ StatedOmega ⇑Q := bStated.2
  have hbcoeff : ((bGL : GL (Fin d) K) : Matrix (Fin d) (Fin d) K) = data.gamma.val := by
    simp [bGL, bStated, eOmega, MulEquiv.subgroupCongr_apply]
  have hordGamma : orderOf data.gamma ∣ p :=
    orderOf_dvd_of_pow_eq_one data.gamma_pow
  have hodd : Odd (orderOf bGL) := by
    rw [show orderOf bGL = orderOf bStated from Subgroup.orderOf_coe bStated]
    rw [show orderOf bStated = orderOf data.gamma from MulEquiv.orderOf_eq eOmega data.gamma]
    exact Odd.of_dvd_nat (hp.odd_of_ne_two hp2) hordGamma
  have hML : ∀ v : Fin d → K, ggJSo2_ML bGL v = matrixLinearEquiv data.gamma.val v := by
    intro v
    rw [show ggJSo2_ML bGL = toLinEquiv (Fin d) K bGL from rfl,
      toLinEquiv_apply, matrixLinearEquiv_apply, hbcoeff]
  have hS : ∀ (c : K) v, S (c • v) = sigma c • S v := by
    intro c v
    exact CFSG.RankThree.PartOne.KCOrthComm.pairMap_smul Q data.g c v
  have hSx : ∀ v, S (ggJSo2_ML bGL v) = ggJSo2_ML bGL (S v) := by
    intro v
    rw [hML, hML]
    exact data.pair_comm v
  have hSQ : ∀ v, Q (S v) = sigma (Q v) := by
    intro v
    exact data.isIsoPair v
  have hfixData := CFSG.StandardType.RecipeFieldOmega.primaryFactors_map_right_eq_self
    data hp hp2
  have htoLin : Matrix.toLin' (bGL : Matrix (Fin d) (Fin d) K) =
      (matrixLinearEquiv data.gamma.val : Module.End K (Fin d → K)) := by
    ext v
    simp [Matrix.toLin'_apply, matrixLinearEquiv_apply, hbcoeff]
  have hfix : ∀ a ∈ primaryFactors
        (Matrix.toLin' (bGL : Matrix (Fin d) (Fin d) K)), a.map sigma = a := by
    intro a ha
    exact hfixData a (by simpa [htoLin] using ha)
  let eJ : J0 ≃* C := e.subgroupMap J0
  let fC : MulAut C := MulAut.congr eJ fprime
  have hfC : ∀ (c : C) v,
      ggJSo2_ML (((fC c : C) : StatedOmega ⇑Q) : GL (Fin d) K) v =
        S (ggJSo2_ML (((c : C) : StatedOmega ⇑Q) : GL (Fin d) K) (S.symm v)) := by
    intro c v
    obtain ⟨j, rfl⟩ := eJ.surjective c
    have hcoe : ((eJ j : C) : StatedOmega ⇑Q) = e j := rfl
    have hfcoe : ((fC (eJ j) : C) : StatedOmega ⇑Q) = e (fprime j) := by
      change ((MulAut.congr eJ fprime) (eJ j) : C) = e (fprime j)
      rw [MulAut.congr_apply]
      simp only [MulEquiv.trans_apply, MulEquiv.symm_apply_apply]
      exact Subgroup.coe_equivMapOfInjective_apply J0 e.toMonoidHom e.injective (fprime j)
    rw [hcoe, hfcoe]
    rw [hfprime j]
    have hef : e (f j) = (MulAut.congr e f) (e j) := by
      rw [MulAut.congr_apply]
      simp
    rw [hef]
    have hFe : MulAut.congr e f = MulAut.congr eOmega
        (CFSG.RankThree.PartOne.AUTSL.conjAct Q data.g) := by
      have htrans : MulAut.congr e f =
          MulAut.congr eOmega (MulAut.congr Theta f) := by
        ext x
        simp [e, MulAut.congr_apply, MulEquiv.trans_apply]
      rw [htrans, hfTheta]
    rw [hFe]
    have hej : e j = eOmega (Theta j) := rfl
    rw [hej]
    have happ : (MulAut.congr eOmega
          (CFSG.RankThree.PartOne.AUTSL.conjAct Q data.g)) (eOmega (Theta j)) =
        eOmega (CFSG.RankThree.PartOne.AUTSL.conjAct Q data.g (Theta j)) := by
      rw [MulAut.congr_apply]
      simp
    rw [happ]
    rw [show ggJSo2_ML (((eOmega
          (CFSG.RankThree.PartOne.AUTSL.conjAct Q data.g (Theta j)) :
            StatedOmega ⇑Q) : GL (Fin d) K)) v =
        matrixLinearEquiv
          (((CFSG.RankThree.PartOne.AUTSL.conjAct Q data.g (Theta j)) :
            matrixDerived Q) : GL (Fin d) K) v from by
      simpa [eOmega] using ggJSo2_ML_subgroupCongr_apply
        (CFSG.RankThree.PartOne.AUTSL.conjAct Q data.g (Theta j)) v]
    rw [show ggJSo2_ML (((eOmega (Theta j) : StatedOmega ⇑Q) :
          GL (Fin d) K)) (S.symm v) =
        matrixLinearEquiv ((Theta j : matrixDerived Q) : GL (Fin d) K) (S.symm v) from by
      simpa [eOmega] using ggJSo2_ML_subgroupCongr_apply (Theta j) (S.symm v)]
    rw [conjAct_matrixLinearEquiv_apply]
  have hsigma : sigma ≠ 1 := by
    intro hs
    have h1 : orderOf sigma = 1 := by rw [hs]; exact orderOf_one
    have h1' : orderOf data.g.val.right = 1 := by simpa [sigma] using h1
    rw [data.field_order] at h1'
    exact hp.ne_one h1'
  have hAllC := kgFieldRestriction_orthogonalCentralizer_of_semilinear
    Q hQ (by simpa using hd) bGL hbOmega hodd (σ := sigma) hsigma (S := S)
    hS hSx hSQ hcardK hfix C hComega fC hfC
  have hprime : fprime = (eJ.symm).symm.trans (fC.trans eJ.symm) := by
    ext j
    simp only [MulEquiv.trans_apply, MulEquiv.symm_symm]
    exact congrArg (fun x : J0 => (x : R)) (by
      have hfCj : fC (eJ j) = eJ (fprime j) := by
        change (MulAut.congr eJ fprime) (eJ j) = eJ (fprime j)
        rw [MulAut.congr_apply]
        simp [MulEquiv.trans_apply]
      rw [hfCj]
      exact (MulEquiv.symm_apply_apply eJ (fprime j)).symm)
  exact ggMarkingAll_transport eJ.symm fC fprime hprime hAllC

private lemma cardK_ge_four_of_dvd_pow_two
    {K : Type} [Field K] [Finite K] {n p : ℕ}
    (hp : p.Prime) (hp2 : p ≠ 2) (hnpos : 0 < n) (hdiv : p ∣ n)
    (hK : Nat.card K = 2 ^ n) : 4 ≤ Nat.card K := by
  have hpodd : Odd p := hp.odd_of_ne_two hp2
  have hp3 : 3 ≤ p := by
    rcases hpodd with ⟨k, hk⟩
    have h2 := hp.two_le
    omega
  have hp_le_n : p ≤ n := Nat.le_of_dvd hnpos hdiv
  have hn3 : 3 ≤ n := by omega
  rw [hK]
  calc
    4 = 2 ^ 2 := by norm_num
    _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) (by omega)

theorem kgFieldRestriction_orthogonalPlus
    {K : Type} [Field K] [Fintype K] [CharP K 2]
    {m p n : ℕ} (hm4 : 4 ≤ m) (hp : p.Prime) (hp2 : p ≠ 2)
    (hdiv : p ∣ n) (hK : Nat.card K = 2 ^ n) :
    KGFieldRestrictionCont p
      (LargeEvenProj (LargeEvenOmega (LargeEvenQPlus K m)))
      (LargeEvenInnSet (LargeEvenProj (LargeEvenOmega (LargeEvenQPlus K m))))
      (LargeEvenMatFieldImage
        (LargeEvenProjMk (LargeEvenOmega (LargeEvenQPlus K m)))) := by
  intro f hf hford h hh hhp hcomm J0 hJ0 fprime hfprime
  have hm1 : 1 ≤ m := by omega
  have hnpos : 0 < n := by
    by_contra hn
    have hn0 : n = 0 := by omega
    subst hn0
    have h1 : Nat.card K = 1 := by simpa using hK
    have h2 : 1 < Nat.card K := Finite.one_lt_card
    omega
  have hcardK := cardK_ge_four_of_dvd_pow_two hp hp2 hnpos hdiv hK
  obtain ⟨sigma, data, hgamma, hsigmaF, hgdef, hFg, hright⟩ :=
    exists_plus_semilinear_representatives (m := m) hm1 hm4 hp hp2
      hf hford hh hhp hcomm
  have hQ : (QuadraticMap.polarBilin (coordinateQuadPlus m K)).Nondegenerate :=
    (regular_coordinateQuadPlus m K (by omega : 3 ≤ m)).1
  exact kgFieldRestriction_orthogonalSuppliedSemilinear
    (Q := coordinateQuadPlus m K) hQ data hp hp2 (plusEquiv hm1) hgamma hFg
    (by omega : 8 ≤ 2 * m) hcardK J0 hJ0 fprime hfprime

theorem kgFieldRestriction_orthogonalMinus
    {K : Type} [Field K] [Fintype K] [CharP K 2]
    {n e p : ℕ} {b c : K}
    (hn1 : 1 ≤ n) (hn4 : 4 ≤ n) (hp : p.Prime) (hp2 : p ≠ 2)
    (he : 1 ≤ e) (hK : Nat.card K = 2 ^ e)
    (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0)
    (hdiv : p ∣ e) :
    KGFieldRestrictionCont p
      (LargeEvenProj (LargeEvenOmega (LargeEvenQMinus (n - 1) b c)))
      (LargeEvenInnSet (LargeEvenProj (LargeEvenOmega (LargeEvenQMinus (n - 1) b c))))
      (LargeEvenPhiQ (n - 1) b c
        (LargeEvenProjMk (LargeEvenOmega (LargeEvenQMinus (n - 1) b c)))) := by
  intro f hf hford h hh hhp hcomm J0 hJ0 fprime hfprime
  obtain ⟨k, data, hgamma, hFfrob, hgdef, hFg, hright⟩ :=
    exists_minus_semilinear_representatives hn4 hn1 he hK hirr hp hp2
      hf hford hh hhp hcomm
  have hQ : (QuadraticMap.polarBilin (coordinateQuadMinus n K hn1 b c)).Nondegenerate :=
    (regular_coordinateQuadMinus n K b c hn4 hirr).1
  have hcardK := cardK_ge_four_of_dvd_pow_two hp hp2 (by omega : 0 < e) hdiv hK
  exact kgFieldRestriction_orthogonalSuppliedSemilinear
    (Q := coordinateQuadMinus n K hn1 b c) hQ data hp hp2 (minusEquiv hn4 b c)
    hgamma hFg (by omega : 8 ≤ 2 * n) hcardK J0 hJ0 fprime hfprime

theorem kgFieldRestrictionOn_orthogonal_high :
    KGFieldRestrictionOn
      (fun p lab => kgfniRow .orthogonal p lab ∧ 4 ≤ lab.rank) := by
  intro p lab hp hp2 hlab ht3 hrow
  obtain ⟨t, r, n⟩ := lab
  obtain ⟨hrow, h4⟩ := hrow
  obtain ⟨htag, hdvd⟩ := hrow
  have h4r : 4 ≤ r := by simpa using h4
  have hn1 : 1 ≤ n := by simpa using hlab.1
  intro Q hQ
  rcases htag with htag | htag
  · cases htag
    dsimp only [LargeEvenRawDatum] at hQ ⊢
    have h3 : ¬ r = 3 := by omega
    rw [if_neg h3] at hQ ⊢
    dsimp only [LargeEvenRecipeOmegaPlus] at hQ ⊢
    obtain ⟨K, i1, i2, hK, hQK⟩ := hQ
    letI : Fintype K := Fintype.ofFinite K
    haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    haveI : CharP K 2 := charP_of_card_eq_prime_pow (p := 2) (f := n)
      (by simpa [Nat.card_eq_fintype_card] using hK)
    refine ⟨K, i1, i2, hK, hQK, ?_⟩
    exact kgFieldRestriction_orthogonalPlus (K := K) (m := r) (p := p)
      (n := n) h4r hp hp2 hdvd hK
  · cases htag
    dsimp only [LargeEvenRawDatum] at hQ ⊢
    have h2 : ¬ r = 2 := by omega
    have h3 : ¬ r = 3 := by omega
    rw [if_neg h2, if_neg h3] at hQ ⊢
    dsimp only [LargeEvenRecipeOmegaMinus] at hQ ⊢
    obtain ⟨K, i1, i2, hK, b, c, hirr, hQK⟩ := hQ
    letI : Fintype K := Fintype.ofFinite K
    haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    haveI : CharP K 2 := charP_of_card_eq_prime_pow (p := 2) (f := n)
      (by simpa [Nat.card_eq_fintype_card] using hK)
    refine ⟨K, i1, i2, hK, b, c, hirr, hQK, ?_⟩
    exact kgFieldRestriction_orthogonalMinus (K := K) (n := r) (e := n)
      (p := p) (b := b) (c := c) (by omega) h4r hp hp2 hn1 hK hirr hdvd

theorem kgFieldRestrictionOn_orthogonal_of_high
    (hHigh : KGFieldRestrictionOn
      (fun p lab => kgfniRow .orthogonal p lab ∧ 4 ≤ lab.rank)) :
    KGFieldRestrictionOn (kgfniRow .orthogonal) := by
  intro p lab hp hp2 hlab ht3 hrow
  by_cases h4 : 4 ≤ lab.rank
  · exact hHigh p lab hp hp2 hlab ht3 ⟨hrow, h4⟩
  · rcases hrow with ⟨htag | htag, hdvd⟩
    · have h3 : lab.rank = 3 := by
        have hle := hlab
        rw [LargeEvenInLambda2] at hle
        simp only [htag] at hle
        omega
      exact kgFieldRestrictionOn_D_three p lab hp hp2 hlab ht3 ⟨htag, h3, hdvd⟩
    · have h2 : 2 ≤ lab.rank := by
        have hle := hlab
        rw [LargeEvenInLambda2] at hle
        simp only [htag] at hle
        exact hle.2
      by_cases h3 : lab.rank = 3
      · exact kgFieldRestrictionOn_twD_three p lab hp hp2 hlab ht3 ⟨htag, h3, hdvd⟩
      · have h2' : lab.rank = 2 := by omega
        exact kgFieldRestrictionOn_twD_two p lab hp hp2 hlab ht3 ⟨htag, h2', hdvd⟩

theorem kgFieldRestrictionOn_orthogonal :
    KGFieldRestrictionOn (kgfniRow .orthogonal) :=
  kgFieldRestrictionOn_orthogonal_of_high
    kgFieldRestrictionOn_orthogonal_high

theorem kgFieldNotInnerInputOn_orthogonal :
    KGFieldNotInnerInputOn (kgfniRow .orthogonal) :=
  kgFieldNotInnerInputOn_of_restriction
    (kgfniRawSimpleOn_of_parts kgfni_rawSimple_classical
      kgfni_rawSimple_chev kgfni_rawSimple_twisted)
    kgFieldRestrictionOn_orthogonal

end OrthogonalHighRows

end CFSG.StandardType
