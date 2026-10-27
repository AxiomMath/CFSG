module

public import CFSG.LocalAnalysis.StandardType.GGSixRCKRPrimeCarrierSLRat
public import CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6ThreeTwNotAll24ConnGenActs
public import CFSG.HardMathSupport.Timmesfeld.CrossChar.TwCompSUStd
public import CFSG.HardMathSupport.Timmesfeld.LangTorus.Defs
public import CFSG.LieType.Chevalley.CoordinateFieldFixedSubgroup
public import CFSG.LieType.Chevalley.RootCharacterKernelProduct
import CFSG.HardMathSupport.S2MathAs1.I1486.Geometry
import CFSG.LieType.Chevalley.ParabolicRadicalLevi
import CFSG.RankThree.Classical2.SLnConjLemmas
public import CFSG.HardMathSupport.Dickson.Sec6.Up34Chev2Aux.InnExcSuNHom
public import CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6ThreeTwNotAll24CentreHom
public import CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6ThreeTwNotAll24ConnGenFrame
public import CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6ThreeTwNotAll24ConnGenPin
public import CFSG.HardMathSupport.Timmesfeld.CrossChar.ExcInnerE8Five
public import CFSG.HardMathSupport.Timmesfeld.CrossChar.ExcInnerResiduals
public import CFSG.HardMathSupport.Timmesfeld.CrossChar.ExcInnerTwE6
public import CFSG.HardMathSupport.Timmesfeld.CrossChar.ExcInnerTwF4
public import CFSG.HardMathSupport.Timmesfeld.CrossChar.ExcInnerTwRigid
public import CFSG.HardMathSupport.Timmesfeld.CrossChar.SmallQThreeE6FourCore
public import CFSG.HardMathSupport.Timmesfeld.LangTorus.CentralizerTrivialPoly
public import CFSG.HardMathSupport.Timmesfeld.LangTorus.OuterField
public import CFSG.HardMathSupport.Timmesfeld.LangTorus.RigidField
public import CFSG.HardMathSupport.Timmesfeld.LangTorus.RigidNorm
public import CFSG.HardMathSupport.Timmesfeld.LocalTwo.CrossLin
public import CFSG.HardMathSupport.Timmesfeld.LocalTwo.LangFrame
public import CFSG.LieType.Chevalley.EvenTrialityOuterInvolutions
public import CFSG.LieType.Chevalley.OddTrialityCosetInvolutions
public import CFSG.LieType.SeitzGeneration.ExtSeitzReeF4Cyclic
public import CFSG.LocalAnalysis.ComponentClassification.AutL2FactsCentModel
public import CFSG.LocalAnalysis.ComponentClassification.AutL2FactsFieldAut
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalSixStructure
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueUStatement
public import CFSG.LocalAnalysis.ComponentClassification.GSLitType
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCatalogSpExclusion
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCorrCentralSylowMaximality
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedGSAContainedSource
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedLayerOddCoreUnbalancingTriple
public import CFSG.LocalAnalysis.ComponentInitial.UnitaryHigherEvenOrthogonalModel
public import CFSG.LocalAnalysis.QuasithinUnique.SQTK.TypeB2
public import CFSG.LocalAnalysis.QuasithinUnique.SQTK.Unitary
public import CFSG.RankThree.CentralLiftSO.SplitTorusWeyl
public import CFSG.RankThree.Chevalley.SteinbergBTTwistedCosetDescent
public import CFSG.RankThree.Classical.SteinbergBJSymplecticSquareZeroCentralizer
public import CFSG.RankThree.PartOne.BRANCH.RankRee
public import CFSG.RankThree.PartOne.CTP.StrongPBridgeRest
public import CFSG.RankThree.PartOne.KC.LinearCommutatorOdd
public import CFSG.RankThree.PartOne.KC.LinearDegreeFive
public import CFSG.RankThree.PartOne.KC.OrthogonalD4WitnessEven
public import CFSG.RankThree.PartOne.KC.OrthogonalD4WitnessOdd
public import CFSG.RankThree.PartOne.KC.UnitaryHigherCrossPrimeTorus
public import CFSG.RankThree.PartOne.KC.UnitaryPlaneEndpoints
public import CFSG.RankThree.PartOne.KD4T.Certs
public import CFSG.RankThree.PartOne.KE.SLnShape
public import CFSG.RankThree.PartOne.KE.StabGeneral
public import CFSG.RankThree.PartOne.N143.Weyl613Defs
public import CFSG.RankThree.PartOne.N143X.KF64WSimple
public import CFSG.RankThree.PartOne.S11d.OutExceptional
public import CFSG.RankThree.PartOne.S11d.OutLinear
public import CFSG.RankThree.PartTwo.KFacts.KS14SzLie
public import CFSG.RankThree.PartTwo.Sec4.Census.Interface
public import CFSG.RankThree.SteinbergR3EOrthogonalCoprimeCyclic
public import CFSG.SignalizerFunctorTheorem.Nonsolvable.SolComponent
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.External.Huppert.IV.theorem_3_3
public import Certificates.Certificate1
public import Certificates.Certificate2

public section

namespace CFSG.StandardType.RCKRP

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.AlgebraicGroups
  CFSG.HardMathSupport.Timmesfeld.LangTorus CFSG.HardMathSupport.Timmesfeld.CrossChar
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley CFSG.RankThree.Classical2
  CFSG.RankThree.PartOne.KE
  CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6Three.KSGen
open scoped MatrixGroups

section Acts

variable {τ : Tag} {L : Type} [Field L] {ν : ℕ} {ψ : SL(ν, L) →* ModGL τ L}
  {σ : Fin ν → Fin ν → Fin τ.rank → ℤ}

theorem torusGroup_le_actsOn_frame
    (hψ : IsSLFrame ψ σ) (hν : 0 < ν) : torusGroup τ L ≤ actsOn ψ := by
  intro t ht
  obtain ⟨b, rfl⟩ := exists_rootDiagUnit_eq_of_mem_torusGroup ht
  refine mem_actsOn.2 ⟨CFSG.RankThree.PartOne.KE.diagGLn (fun i => rootChar b (σ i ⟨0, hν⟩)), fun X => ?_⟩
  rw [hψ.torus ⟨0, hν⟩ b X, conjDiagn_eq_conjSLn]

theorem torusSup_le_actsOn_frame
    {χ : Multiplicative (Fin τ.rank → ℤ) →* Lˣ} (hψ : IsSLFrame ψ σ) (hν : 0 < ν)
    (i : KernelComponent χ) (hΨ : componentRoots χ i = frameRoots σ) :
    torusGroup τ L ⊔ rootSpan τ L (kernelRoots χ) ≤ actsOn ψ := by
  refine sup_le (torusGroup_le_actsOn_frame hψ hν) ?_
  rw [← iSup_componentRootSpan L (χ := χ)]
  refine iSup_le fun j => ?_
  by_cases hji : j = i
  · subst hji
    have : componentRootSpan L χ j = ψ.range := by
      rw [hψ.range, ← hΨ]
      rfl
    rw [this]
    exact range_le_actsOn ψ
  · intro g hg
    have h1 := componentRootSpan_le_centralizer L (χ := χ) (Ne.symm hji)
    have h2 : ψ.range ≤ componentRootSpan L χ i := by
      rw [hψ.range, ← hΨ]
      exact le_rfl
    refine mem_actsOn_of_commute fun X => ?_
    have := Subgroup.mem_centralizer_iff.1 (h1 (h2 ⟨X, rfl⟩)) g hg
    exact this

end Acts

section Matrix

variable {L : Type} [Field L] {ν : ℕ} {G : Type*} [Group G]
  {ψ : SL(ν, L) →* G}

private lemma map_conjSLn_of_ringHom {K Ω : Type} [Field K] [Field Ω] (φ : K →+* Ω)
    {n : ℕ} (M : GL (Fin n) K) (X : Matrix.SpecialLinearGroup (Fin n) K) :
    (Matrix.SpecialLinearGroup.map φ) (CFSG.RankThree.Classical2.conjSLn M X) =
      CFSG.RankThree.Classical2.conjSLn (Matrix.GeneralLinearGroup.map φ M)
        ((Matrix.SpecialLinearGroup.map φ) X) := by
  apply Subtype.ext
  rw [Matrix.SpecialLinearGroup.map_apply_coe, CFSG.RankThree.Classical2.coe_conjSLn,
    CFSG.RankThree.Classical2.coe_conjSLn, Matrix.SpecialLinearGroup.map_apply_coe,
    RingHom.mapMatrix_apply, RingHom.mapMatrix_apply, Matrix.map_mul, Matrix.map_mul,
    ← Matrix.GeneralLinearGroup.map_inv]
  rfl

private lemma conjSLn_eq_smul_of_forall_range_conj (hν : 3 ≤ ν)
    (hker : ψ.ker ≠ ⊤) {B H : GL (Fin ν) L} {X X' : SL(ν, L)}
    (h : ∀ g ∈ ψ.range,
      ψ (conjSLn (B * H) X) * g * (ψ (conjSLn (B * H) X))⁻¹ =
      ψ (conjSLn H X') * g * (ψ (conjSLn H X'))⁻¹) :
    ∃ ζ : L, (((H⁻¹ * B * H) * Matrix.SpecialLinearGroup.toGL X *
        (H⁻¹ * B * H)⁻¹ : GL (Fin ν) L) : Matrix (Fin ν) (Fin ν) L) =
      ζ • ((Matrix.SpecialLinearGroup.toGL X' : GL (Fin ν) L) :
        Matrix (Fin ν) (Fin ν) L) := by
  let U₁ : SL(ν, L) := conjSLn (B * H) X
  let U₂ : SL(ν, L) := conjSLn H X'
  have hcomm : ∀ Y : SL(ν, L), ψ (U₂⁻¹ * U₁) * ψ Y = ψ Y * ψ (U₂⁻¹ * U₁) := by
    intro Y
    have key := h (ψ Y) (MonoidHom.mem_range.mpr ⟨Y, rfl⟩)
    calc ψ (U₂⁻¹ * U₁) * ψ Y
        = (ψ U₂)⁻¹ * ψ U₁ * ψ Y := by rw [map_mul, map_inv]
      _ = (ψ U₂)⁻¹ * (ψ U₁ * ψ Y * (ψ U₁)⁻¹) * ψ U₁ := by group
      _ = (ψ U₂)⁻¹ * (ψ U₂ * ψ Y * (ψ U₂)⁻¹) * ψ U₁ := by rw [key]
      _ = ψ Y * ((ψ U₂)⁻¹ * ψ U₁) := by group
      _ = ψ Y * ψ (U₂⁻¹ * U₁) := by rw [map_mul, map_inv]
  have hcent : U₂⁻¹ * U₁ ∈ Subgroup.center SL(ν, L) :=
    mem_center_SL_of_commute hν ψ hker hcomm
  obtain ⟨ζ, hζpow, hζscalar⟩ := (Matrix.SpecialLinearGroup.mem_center_iff).mp hcent
  have hζpow' : ζ ^ ν = 1 := by simpa using hζpow
  have hν0 : ν ≠ 0 := by omega
  have hζ0 : ζ ≠ 0 := by
    intro h0
    rw [h0, zero_pow hν0] at hζpow'
    exact one_ne_zero hζpow'.symm
  let S : SL(ν, L) := ⟨Matrix.scalar (Fin ν) ζ, by
    rw [Matrix.scalar_apply, Matrix.det_diagonal]
    simpa using hζpow'⟩
  have hSU : S = U₂⁻¹ * U₁ := Subtype.ext hζscalar
  have hU1eq : U₁ = U₂ * S := by rw [hSU]; group
  have hGL : Matrix.SpecialLinearGroup.toGL U₁ =
      Matrix.SpecialLinearGroup.toGL U₂ * Matrix.SpecialLinearGroup.toGL S := by
    rw [hU1eq, map_mul]
  have htoGL₁ : Matrix.SpecialLinearGroup.toGL U₁ =
      (B * H : GL (Fin ν) L) * Matrix.SpecialLinearGroup.toGL X * (B * H)⁻¹ := by
    apply Units.ext
    rw [Matrix.SpecialLinearGroup.coe_GL_coe_matrix]
    rw [show U₁ = conjSLn (B * H) X from rfl, coe_conjSLn]
    simp only [Matrix.SpecialLinearGroup.coe_GL_coe_matrix, Units.val_mul,
      Units.val_inv_eq_inv_val]
  have htoGL₂ : Matrix.SpecialLinearGroup.toGL U₂ =
      H * Matrix.SpecialLinearGroup.toGL X' * H⁻¹ := by
    apply Units.ext
    rw [Matrix.SpecialLinearGroup.coe_GL_coe_matrix]
    rw [show U₂ = conjSLn H X' from rfl, coe_conjSLn]
    simp only [Matrix.SpecialLinearGroup.coe_GL_coe_matrix, Units.val_mul,
      Units.val_inv_eq_inv_val]
  have hGL1 : (B * H : GL (Fin ν) L) * Matrix.SpecialLinearGroup.toGL X * (B * H)⁻¹ =
      (H * Matrix.SpecialLinearGroup.toGL X' * H⁻¹) * Matrix.SpecialLinearGroup.toGL S := by
    rw [← htoGL₁, ← htoGL₂]
    exact hGL
  have hSGL : Matrix.SpecialLinearGroup.toGL S =
      Matrix.GeneralLinearGroup.scalar (Fin ν) (Units.mk0 ζ hζ0) := Units.ext rfl
  have hScomm : (H⁻¹ : GL (Fin ν) L) * Matrix.SpecialLinearGroup.toGL S * H =
      Matrix.SpecialLinearGroup.toGL S := by
    have hcommS : Matrix.SpecialLinearGroup.toGL S * H =
        H * Matrix.SpecialLinearGroup.toGL S := by
      rw [hSGL]
      exact Matrix.GeneralLinearGroup.scalar_commute (Units.mk0 ζ hζ0) H
    calc (H⁻¹ : GL (Fin ν) L) * Matrix.SpecialLinearGroup.toGL S * H
        = (H⁻¹ : GL (Fin ν) L) * (Matrix.SpecialLinearGroup.toGL S * H) := by group
      _ = (H⁻¹ : GL (Fin ν) L) * (H * Matrix.SpecialLinearGroup.toGL S) := by rw [hcommS]
      _ = Matrix.SpecialLinearGroup.toGL S := by group
  have hconjGL : (H⁻¹ * B * H) * Matrix.SpecialLinearGroup.toGL X * (H⁻¹ * B * H)⁻¹ =
      Matrix.SpecialLinearGroup.toGL X' * Matrix.SpecialLinearGroup.toGL S := by
    calc (H⁻¹ * B * H) * Matrix.SpecialLinearGroup.toGL X * (H⁻¹ * B * H)⁻¹
        = (H⁻¹ : GL (Fin ν) L) *
            ((B * H) * Matrix.SpecialLinearGroup.toGL X * (B * H)⁻¹) * H := by group
      _ = (H⁻¹ : GL (Fin ν) L) *
            ((H * Matrix.SpecialLinearGroup.toGL X' * H⁻¹) *
              Matrix.SpecialLinearGroup.toGL S) * H := by rw [hGL1]
      _ = Matrix.SpecialLinearGroup.toGL X' * ((H⁻¹ : GL (Fin ν) L) *
            Matrix.SpecialLinearGroup.toGL S * H) := by group
      _ = Matrix.SpecialLinearGroup.toGL X' * Matrix.SpecialLinearGroup.toGL S := by
        rw [hScomm]
  refine ⟨ζ, ?_⟩
  have hv := congrArg (fun u : GL (Fin ν) L => (u : Matrix (Fin ν) (Fin ν) L)) hconjGL
  have hSmat : (Matrix.SpecialLinearGroup.toGL S : Matrix (Fin ν) (Fin ν) L) =
      Matrix.scalar (Fin ν) ζ := rfl
  have hscalar : Matrix.scalar (Fin ν) ζ = ζ • (1 : Matrix (Fin ν) (Fin ν) L) := by
    rw [Matrix.scalar_apply, Matrix.smul_one_eq_diagonal]
  have hR : (((Matrix.SpecialLinearGroup.toGL X' * Matrix.SpecialLinearGroup.toGL S :
      GL (Fin ν) L)) : Matrix (Fin ν) (Fin ν) L) =
      ζ • ((Matrix.SpecialLinearGroup.toGL X' : GL (Fin ν) L) :
        Matrix (Fin ν) (Fin ν) L) := by
    rw [Units.val_mul, hSmat, hscalar, Matrix.mul_smul, Matrix.mul_one]
  rw [hR] at hv
  exact hv

end Matrix

section Split


theorem exists_conjSLn_of_mem_torus_split {τ : Tag} {L : Type} [Field L] [IsAlgClosed L] [CharP L 2] {p₀ : ℕ} (S : LangSetup τ L p₀)
    {ta : Fin τ.rank → Lˣ} (hT : rootDiagUnit τ ta ∈ S.D.torus)
    (i : KernelComponent (rootCharHom ta)) {ν : ℕ} (hν : 3 ≤ ν) {ψ : SL(ν, L) →* ModGL τ L}
    {σ : Fin ν → Fin ν → Fin τ.rank → ℤ} (hψ : IsSLFrame ψ σ)
    (hΨ : componentRoots (rootCharHom ta) i = frameRoots σ)
    {Q : ℕ} (hQ2 : 2 ≤ Q) (σQ : L ≃+* L) (hσQ : ∀ c, σQ c = c ^ Q)
    {z : ModGL τ L} (hz : z ∈ torusGroup τ L ⊔ rootSpan τ L (kernelRoots (rootCharHom ta)))
    (f : SL(ν, ↥(fixSubfield σQ)) →* ModGL τ L)
    (hfrange : f.range = rationalComponent S.ρ S.Γ (rootCharHom ta) i)
    (hfact : ∀ (X : SL(ν, ↥(fixSubfield σQ))),
      ∀ g ∈ rootSpan τ L (componentRoots (rootCharHom ta) i),
        f X * g * (f X)⁻¹ =
          (z * ψ (Matrix.SpecialLinearGroup.map (fixSubfield σQ).subtype X) * z⁻¹) * g *
            (z * ψ (Matrix.SpecialLinearGroup.map (fixSubfield σQ).subtype X) * z⁻¹)⁻¹)
    {b : ModGL τ L} (hb : b ∈ S.D.torus) :
    ∃ M : GL (Fin ν) ↥(fixSubfield σQ), ∀ X, b⁻¹ * f X * b = f (conjSLn M X) := by
  classical
  let K : Subfield L := fixSubfield σQ
  let ι : SL(ν, ↥K) →* SL(ν, L) := Matrix.SpecialLinearGroup.map K.subtype
  have hker : ψ.ker ≠ ⊤ := by
    intro h
    have h01 : (⟨0, by omega⟩ : Fin ν) ≠ ⟨1, by omega⟩ := by simp
    obtain ⟨ε, hε⟩ := hψ.transv _ _ h01
    have h1 : Matrix.SpecialLinearGroup.transvection h01 (1 : L) ∈ ψ.ker := by
      rw [h]
      exact Subgroup.mem_top _
    rw [MonoidHom.mem_ker, hε, mul_one,
      ← pinnedX_zero τ L (σ ⟨0, by omega⟩ ⟨1, by omega⟩)] at h1
    exact Units.ne_zero ε (pinnedX_injective τ L _ h1)
  have hbinv : b⁻¹ ∈ S.D.torus := inv_mem hb
  have hb_tg : b⁻¹ ∈ torusGroup τ L := (mem_twistedTorusOf.1 hbinv).1
  have hb_tg_b : b ∈ torusGroup τ L := (mem_twistedTorusOf.1 hb).1
  have hstep : S.D.step b⁻¹ = b⁻¹ := by
    simpa [LangDatum.step, MulAut.conj_apply] using (mem_twistedTorusOf.1 hbinv).2
  obtain ⟨B, hB⟩ := mem_actsOn.1 (torusGroup_le_actsOn_frame hψ (by omega : 0 < ν) hb_tg)
  have hzacts : z ∈ actsOn ψ := torusSup_le_actsOn_frame hψ (by omega) i hΨ hz
  obtain ⟨H, hH⟩ := mem_actsOn.1 hzacts
  obtain ⟨Hinv, hHinv⟩ := mem_actsOn.1 (inv_mem hzacts)
  have hB' : ∀ U, b⁻¹ * ψ U * b = ψ (conjSLn B U) := fun U => by simpa using hB U
  let R : Subgroup (ModGL τ L) := rationalComponent S.ρ S.Γ (rootCharHom ta) i
  let Si : Subgroup (ModGL τ L) := rootSpan τ L (componentRoots (rootCharHom ta) i)
  have hSi : Si = ψ.range := by
    rw [hψ.range, ← hΨ]
  have hbSi : ∀ g ∈ Si, b * g * b⁻¹ ∈ Si := by
    have hbN : b ∈ Subgroup.normalizer (Si : Set (ModGL τ L)) := by
      simpa [Si] using CFSG.LieType.Chevalley.torusGroup_le_normalizer_rootSpan (K := L)
        (S := componentRoots (rootCharHom ta) i) (fun γ hγ => hγ.1.1) hb_tg_b
    intro g hg
    exact ((Subgroup.mem_normalizer_iff.1 hbN) g).1 hg
  have hA_mem_f : ∀ X : SL(ν, ↥K), b⁻¹ * f X * b ∈ f.range := by
    intro X
    have h1 := CFSG.HardMathSupport.S2MathAs1.I1486.conj_mem_rationalComponent_of_mem_sup_rootSpan
      S hT i (Subgroup.mem_sup_left hb_tg) hstep (f X) (by
        rw [← hfrange]
        exact MonoidHom.mem_range.mpr ⟨X, rfl⟩)
    simpa [hfrange] using h1
  have hex : ∀ X : SL(ν, ↥K), ∃ X' : SL(ν, ↥K), f X' = b⁻¹ * f X * b := by
    intro X
    exact MonoidHom.mem_range.mp (hA_mem_f X)
  choose X' hX' using hex
  let C : GL (Fin ν) L := H⁻¹ * B * H
  have hC : ∀ X : SL(ν, ↥K), ∃ (X' : SL(ν, ↥K)) (ζ : L),
      (C : Matrix (Fin ν) (Fin ν) L) *
        (Matrix.SpecialLinearGroup.map K.subtype X : Matrix (Fin ν) (Fin ν) L) *
        ((C⁻¹ : GL (Fin ν) L) : Matrix (Fin ν) (Fin ν) L) =
      ζ • (Matrix.SpecialLinearGroup.map K.subtype (X' : SL(ν, ↥K)) :
        Matrix (Fin ν) (Fin ν) L) := by
    intro X
    have hact : ∀ g ∈ ψ.range,
        ψ (conjSLn (B * H) (ι X)) * g * (ψ (conjSLn (B * H) (ι X)))⁻¹ =
        ψ (conjSLn H (ι (X' X))) * g * (ψ (conjSLn H (ι (X' X))))⁻¹ := by
      intro g hg
      have hgS : g ∈ Si := by rw [hSi]; exact hg
      have hbg : b * g * b⁻¹ ∈ Si := hbSi g hgS
      have h1 := hfact X (b * g * b⁻¹) hbg
      have h2 := hfact (X' X) g hgS
      have hleft : b⁻¹ * (z * ψ (ι X) * z⁻¹) * b = ψ (conjSLn (B * H) (ι X)) := by
        rw [hH (ι X), hB' (conjSLn H (ι X)), ← conjSLn_mul_apply]
      have hright : z * ψ (ι (X' X)) * z⁻¹ = ψ (conjSLn H (ι (X' X))) := hH _
      have hconj : (b⁻¹ * (z * ψ (ι X) * z⁻¹) * b) * g *
            (b⁻¹ * (z * ψ (ι X) * z⁻¹) * b)⁻¹ =
          (z * ψ (ι (X' X)) * z⁻¹) * g * (z * ψ (ι (X' X)) * z⁻¹)⁻¹ := by
        calc (b⁻¹ * (z * ψ (ι X) * z⁻¹) * b) * g *
              (b⁻¹ * (z * ψ (ι X) * z⁻¹) * b)⁻¹
            = b⁻¹ * ((z * ψ (ι X) * z⁻¹) * (b * g * b⁻¹) *
                (z * ψ (ι X) * z⁻¹)⁻¹) * b := by group
          _ = b⁻¹ * (f X * (b * g * b⁻¹) * (f X)⁻¹) * b := by rw [← h1]
          _ = (b⁻¹ * f X * b) * g * (b⁻¹ * f X * b)⁻¹ := by group
          _ = f (X' X) * g * (f (X' X))⁻¹ := by rw [hX' X]
          _ = (z * ψ (ι (X' X)) * z⁻¹) * g * (z * ψ (ι (X' X)) * z⁻¹)⁻¹ := h2
      rw [hleft, hright] at hconj
      exact hconj
    obtain ⟨ζ, hζ⟩ := conjSLn_eq_smul_of_forall_range_conj hν hker hact
    refine ⟨X' X, ζ, ?_⟩
    simpa only [ι, C, Units.val_mul, Matrix.SpecialLinearGroup.coe_GL_coe_matrix] using hζ
  obtain ⟨M, c, hc0, hCM⟩ := exists_smul_map_of_conj_char_two hQ2 (σQ : L →+* L) hσQ K
    (fun c => Iff.rfl) C hC
  have hB_mem_f : ∀ X : SL(ν, ↥K), f (conjSLn M X) ∈ f.range :=
    fun X => MonoidHom.mem_range.mpr ⟨_, rfl⟩
  have hB_mem_R : ∀ X : SL(ν, ↥K), f (conjSLn M X) ∈ R := by
    intro X
    have h := hB_mem_f X
    rwa [hfrange] at h
  have hCGL : (H⁻¹ * B * H : GL (Fin ν) L) =
      Matrix.GeneralLinearGroup.map K.subtype M *
        Matrix.GeneralLinearGroup.scalar (Fin ν) (Units.mk0 c hc0) := by
    apply Units.ext
    rw [hCM, Units.val_mul, Matrix.GeneralLinearGroup.coe_scalar, Units.val_mk0,
      ← (Matrix.scalar_commute c (fun r' => mul_comm c r') _).eq, Matrix.scalar_apply,
      ← Matrix.smul_eq_diagonal_mul]
    congr 1
  have hconjC : ∀ X : SL(ν, ↥K),
      conjSLn C (ι X) =
        conjSLn (Matrix.GeneralLinearGroup.map K.subtype M) (ι X) := by
    intro X
    rw [show C = Matrix.GeneralLinearGroup.map K.subtype M * Matrix.GeneralLinearGroup.scalar (Fin ν) (Units.mk0 c hc0) from hCGL, conjSLn_mul_scalar]
  have hleft : ∀ X : SL(ν, ↥K),
      b⁻¹ * (z * ψ (ι X) * z⁻¹) * b = ψ (conjSLn (B * H) (ι X)) := by
    intro X
    rw [hH (ι X), hB' (conjSLn H (ι X)), ← conjSLn_mul_apply]
  have hw_conj : ∀ X : SL(ν, ↥K),
      b⁻¹ * (z * ψ (ι X) * z⁻¹) * b = z * ψ (ι (conjSLn M X)) * z⁻¹ := by
    intro X
    have hmapconj : conjSLn (Matrix.GeneralLinearGroup.map K.subtype M) (ι X) =
        ι (conjSLn M X) := by
      simpa only [ι] using (map_conjSLn_of_ringHom K.subtype M X).symm
    have hconjBH : conjSLn (B * H) (ι X) = conjSLn H (ι (conjSLn M X)) := by
      have hBH : B * H = H * (H⁻¹ * B * H) := by group
      rw [hBH, conjSLn_mul_apply, hconjC X, hmapconj]
    calc b⁻¹ * (z * ψ (ι X) * z⁻¹) * b
        = ψ (conjSLn (B * H) (ι X)) := hleft X
      _ = ψ (conjSLn H (ι (conjSLn M X))) := by rw [hconjBH]
      _ = z * ψ (ι (conjSLn M X)) * z⁻¹ := (hH _).symm
  have hzS : ∀ g ∈ Si, z * g * z⁻¹ ∈ Si := by
    intro g hg
    rw [hSi] at hg ⊢
    obtain ⟨U, rfl⟩ := MonoidHom.mem_range.mp hg
    rw [hH U]
    exact MonoidHom.mem_range.mpr ⟨_, rfl⟩
  have hzinvS : ∀ g ∈ Si, z⁻¹ * g * z ∈ Si := by
    intro g hg
    rw [hSi] at hg ⊢
    obtain ⟨U, rfl⟩ := MonoidHom.mem_range.mp hg
    exact MonoidHom.mem_range.mpr ⟨_, by simpa using (hHinv U).symm⟩
  have hR_norm : ∀ r ∈ f.range, ∀ g ∈ Si, r * g * r⁻¹ ∈ Si := by
    intro r hr g hg
    obtain ⟨Y, rfl⟩ := MonoidHom.mem_range.mp hr
    have h1 : z⁻¹ * g * z ∈ Si := hzinvS g hg
    have hpsi : ψ (ι Y) ∈ Si := by
      rw [hSi]
      exact MonoidHom.mem_range.mpr ⟨_, rfl⟩
    have h2 : ψ (ι Y) * (z⁻¹ * g * z) * (ψ (ι Y))⁻¹ ∈ Si :=
      Si.mul_mem (Si.mul_mem hpsi h1) (Si.inv_mem hpsi)
    have h3 : z * (ψ (ι Y) * (z⁻¹ * g * z) * (ψ (ι Y))⁻¹) * z⁻¹ ∈ Si := hzS _ h2
    rw [hfact Y g hg]
    convert h3 using 2 <;> group
  have hAB : ∀ X : SL(ν, ↥K), ∀ g ∈ Si,
      (b⁻¹ * f X * b) * g * (b⁻¹ * f X * b)⁻¹ =
        f (conjSLn M X) * g * (f (conjSLn M X))⁻¹ := by
    intro X g hg
    have hbg : b * g * b⁻¹ ∈ Si := hbSi g hg
    have h1 := hfact X (b * g * b⁻¹) hbg
    have h2 := hfact (conjSLn M X) g hg
    calc (b⁻¹ * f X * b) * g * (b⁻¹ * f X * b)⁻¹
        = b⁻¹ * (f X * (b * g * b⁻¹) * (f X)⁻¹) * b := by group
      _ = b⁻¹ * ((z * ψ (ι X) * z⁻¹) * (b * g * b⁻¹) *
            (z * ψ (ι X) * z⁻¹)⁻¹) * b := by rw [h1]
      _ = (b⁻¹ * (z * ψ (ι X) * z⁻¹) * b) * g *
            (b⁻¹ * (z * ψ (ι X) * z⁻¹) * b)⁻¹ := by group
      _ = (z * ψ (ι (conjSLn M X)) * z⁻¹) * g *
            (z * ψ (ι (conjSLn M X)) * z⁻¹)⁻¹ := by rw [hw_conj X]
      _ = f (conjSLn M X) * g * (f (conjSLn M X))⁻¹ := h2.symm
  let A : SL(ν, ↥K) → ModGL τ L := fun X => b⁻¹ * f X * b
  let B' : SL(ν, ↥K) → ModGL τ L := fun X => f (conjSLn M X)
  let u : SL(ν, ↥K) → ModGL τ L := fun X => A X * (B' X)⁻¹
  have hu_mem_f : ∀ X, u X ∈ f.range :=
    fun X => f.range.mul_mem (hA_mem_f X) (f.range.inv_mem (hB_mem_f X))
  have hu_mem : ∀ X, u X ∈ R := by
    intro X
    have h := hu_mem_f X
    rwa [hfrange] at h
  have hu_cent_Si : ∀ X, ∀ g ∈ Si, u X * g * (u X)⁻¹ = g := by
    intro X g hg
    have hBg : (B' X)⁻¹ * g * B' X ∈ Si :=
      hR_norm (B' X)⁻¹ (f.range.inv_mem (hB_mem_f X)) g hg
    have h := hAB X ((B' X)⁻¹ * g * B' X) hBg
    calc u X * g * (u X)⁻¹
        = A X * ((B' X)⁻¹ * g * B' X) * (A X)⁻¹ := by
          simp only [u]; group
      _ = B' X * ((B' X)⁻¹ * g * B' X) * (B' X)⁻¹ := h
      _ = g := by group
  have hu_f : ∀ X, ∃ X'', f X'' = u X := fun X => MonoidHom.mem_range.mp (hu_mem_f X)
  choose X'' hX'' using hu_f
  have hu_center_R : ∀ X, (⟨u X, hu_mem X⟩ : ↥R) ∈ Subgroup.center ↥R := by
    intro X
    have hpsi_cent : ∀ h ∈ Si, ψ (ι (X'' X)) * h * (ψ (ι (X'' X)))⁻¹ = h := by
      intro h hh
      have hzh : z * h * z⁻¹ ∈ Si := hzS h hh
      have hw := hu_cent_Si X (z * h * z⁻¹) hzh
      have h1 : (z * ψ (ι (X'' X)) * z⁻¹) * (z * h * z⁻¹) *
          (z * ψ (ι (X'' X)) * z⁻¹)⁻¹ = z * h * z⁻¹ := by
        rw [(hfact (X'' X) (z * h * z⁻¹) hzh).symm, hX'' X, hw]
      calc ψ (ι (X'' X)) * h * (ψ (ι (X'' X)))⁻¹
          = z⁻¹ * ((z * ψ (ι (X'' X)) * z⁻¹) * (z * h * z⁻¹) *
              (z * ψ (ι (X'' X)) * z⁻¹)⁻¹) * z := by group
        _ = z⁻¹ * (z * h * z⁻¹) * z := by rw [h1]
        _ = h := by group
    have hcomm_range : ∀ U, ψ (ι (X'' X)) * ψ U = ψ U * ψ (ι (X'' X)) := by
      intro U
      have h := hpsi_cent (ψ U) (by rw [hSi]; exact MonoidHom.mem_range.mpr ⟨_, rfl⟩)
      calc ψ (ι (X'' X)) * ψ U
          = (ψ (ι (X'' X)) * ψ U * (ψ (ι (X'' X)))⁻¹) * ψ (ι (X'' X)) := by group
        _ = ψ U * ψ (ι (X'' X)) := by rw [h]
    have hcenter : ι (X'' X) ∈ Subgroup.center SL(ν, L) :=
      mem_center_SL_of_commute hν ψ hker hcomm_range
    have hincl_inj : Function.Injective ι := by
      intro A1 A2 hA
      apply Subtype.ext
      apply Matrix.map_injective K.subtype_injective
      have h := congrArg (fun C : SL(ν, L) => (C : Matrix (Fin ν) (Fin ν) L)) hA
      simpa [ι, Matrix.SpecialLinearGroup.map_apply_coe, RingHom.mapMatrix_apply] using h
    have hX''_center : X'' X ∈ Subgroup.center SL(ν, ↥K) := by
      rw [Subgroup.mem_center_iff]
      intro Y
      apply hincl_inj
      rw [map_mul, map_mul]
      exact (Subgroup.mem_center_iff.1 hcenter) (ι Y)
    rw [Subgroup.mem_center_iff]
    intro r
    apply Subtype.ext
    change (r : ModGL τ L) * u X = u X * (r : ModGL τ L)
    have hr : (r : ModGL τ L) ∈ f.range := by
      rw [hfrange]
      simpa only [R] using r.2
    obtain ⟨Y, hY⟩ := MonoidHom.mem_range.mp hr
    rw [← hY]
    rw [← hX'' X, ← map_mul, ← map_mul, (Subgroup.mem_center_iff.1 hX''_center) Y]
  have hA_mul : ∀ X Y, A (X * Y) = A X * A Y := by
    intro X Y
    simp only [A]
    rw [map_mul]
    group
  have hB'_mul : ∀ X Y, B' (X * Y) = B' X * B' Y := by
    intro X Y
    simp only [B']
    rw [map_mul, map_mul]
  have hu_mul : ∀ X Y, u (X * Y) = u X * u Y := by
    intro X Y
    have hAY : A Y = u Y * B' Y := by
      simp only [u]; group
    have hcommY : u Y * (B' X)⁻¹ = (B' X)⁻¹ * u Y := by
      have h := (Subgroup.mem_center_iff.1 (hu_center_R Y))
        ⟨(B' X)⁻¹, R.inv_mem (hB_mem_R X)⟩
      exact (congrArg (fun w : ↥R => (w : ModGL τ L)) h).symm
    calc u (X * Y)
        = A X * A Y * (B' X * B' Y)⁻¹ := by
          simp only [u, hA_mul, hB'_mul]
      _ = A X * (u Y * B' Y) * ((B' Y)⁻¹ * (B' X)⁻¹) := by
          rw [hAY, mul_inv_rev]
      _ = A X * u Y * (B' X)⁻¹ := by
          have hcancel : ∀ a u b c : ModGL τ L,
              a * (u * b) * (b⁻¹ * c⁻¹) = a * u * c⁻¹ := by
            intro a u b c
            group
          exact hcancel (A X) (u Y) (B' Y) (B' X)
      _ = A X * (u Y * (B' X)⁻¹) := by rw [mul_assoc]
      _ = A X * ((B' X)⁻¹ * u Y) := by rw [hcommY]
      _ = A X * (B' X)⁻¹ * u Y := by rw [← mul_assoc]
      _ = u X * u Y := rfl
  have hperf : commutator SL(ν, ↥K) = ⊤ := by
    have hQ : CFSG.IsQuasisimple SL(ν, ↥K) :=
      CFSG.RankThree.Classical2.isQuasisimple_specialLinearGroup hν
    exact Group.isPerfect_def.1 hQ.1
  let Uc : SL(ν, ↥K) →* Subgroup.center R :=
    { toFun := fun X => ⟨⟨u X, hu_mem X⟩, hu_center_R X⟩
      map_one' := by
        apply Subtype.ext
        apply Subtype.ext
        simp only [u, A, B', map_one]
        group
        rfl
      map_mul' := fun X Y => by
        apply Subtype.ext
        apply Subtype.ext
        exact hu_mul X Y }
  have hle : commutator SL(ν, ↥K) ≤ Uc.ker := Abelianization.commutator_subset_ker Uc
  rw [hperf] at hle
  have hu_eq_one : ∀ X, u X = 1 := by
    intro X
    have h1 : Uc X = 1 := hle (Subgroup.mem_top X)
    have h2 := congrArg (fun w : Subgroup.center R => ((w : R) : ModGL τ L)) h1
    simpa [Uc] using h2
  refine ⟨M, fun X => ?_⟩
  have h1 : b⁻¹ * f X * b = u X * f (conjSLn M X) := by
    simp only [u, A, B']
    group
  rw [h1, hu_eq_one X, one_mul]


end Split

end CFSG.StandardType.RCKRP

end
