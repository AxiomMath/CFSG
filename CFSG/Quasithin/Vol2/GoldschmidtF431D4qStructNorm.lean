module

public import CFSG.Quasithin.Vol2.GoldschmidtF431D4qStructLoc
public import CFSG.Quasithin.Vol2.GoldschmidtF431D4qYam
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.X6Triality
public import CFSG.LieType.Steinberg.CentralExt.GriessNativeModels
public import CFSG.Certificates.Kernel.LocalCompTits.Span
public import CFSG.Certificates.Kernel.Spor.ONKSound
public import CFSG.CharacterTheory.BrauerThirdMainTheorem.CentralResidueMaps
public import CFSG.CharacterTheory.BrauerThirdMainTheorem.NormalizerClassLifting
public import CFSG.CharacterTheory.BrauerThirdMainTheorem.PrincipalClassDefects
public import CFSG.CharacterTheory.Semidihedral.Principal.DegreeZeroGram
public import CFSG.CharacterTheory.TwoRankLowerBound.BrauerCharacterCriterion
public import CFSG.LieType.Multipliers.U62Sylow
public import CFSG.LocalAnalysis.ComponentInitial.UnitaryHigherEvenOrthogonalModel
public import CFSG.Quasithin.Background.F3
public import CFSG.Quasithin.Recognition.F4Moufang
public import CFSG.Quasithin.Recognition.F4Thirtyone
public import CFSG.Quasithin.Vol2.GoldschmidtF431Main
public import CFSG.Quasithin.Vol2.GoldschmidtF431SpAbs
public import CFSG.Quasithin.Vol2.GoldschmidtF431SpTrans
public import CFSG.Sporadic.Schreier.TitsOther
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.FiniteFieldPrimeOrderFixedSubfield
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.OrderThreeNormalizer
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.PGammaL2PSLRangeCentralizer
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section3.FirstCaseKleinInvolutionCount
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section3.FirstCaseKleinRestrictionSixCount
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section3.FirstCaseKleinUDecomposition
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section4.SecondCaseEquationEleven
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section4.SecondCaseEquationTen
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section4.SecondCaseEquationTenStructuralIdentities
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section4.SecondCasePSL2FieldProjectionArithmetic
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section4.SecondCasePSL2OrderPSubgroupCount
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Suzuki.OddGraphReconstruction
public import Certificates.Certificate1
public import Certificates.Certificate10
public import Certificates.Certificate11
public import Certificates.Certificate12
public import Certificates.Certificate2
public import Certificates.Certificate3
public import Certificates.Certificate4
public import Certificates.Certificate42
public import Certificates.Certificate44
public import Certificates.Certificate5
public import Certificates.Certificate6
public import Certificates.Certificate7
public import Certificates.Certificate8
public import Certificates.Certificate9
public import Certificates.Data.CFSGNative.MonsterB.Rep4371Model
public import Certificates.Kernel.J4Count.FixC
public import Certificates.Kernel.J4Count.FixCPairBase1
public import Certificates.Kernel.J4Count.KFactsBase
public import TauCeti.LinearAlgebra.QuadraticForm.OrthogonalBasis

public section

namespace CFSG.Quasithin.H13.F431.D4q.Struct

open CFSG.Quasithin CFSG.QuasithinUnique CFSG.LieType.Chevalley CFSG.Blueprint
  CFSG.Blueprint.Chevalley CFSG.QuasithinUnique.Setup.X6
  CFSG.LieType.Steinberg.CentralExt.GriessNative CFSG.Quasithin.H13.Sec53F.Yam

set_option linter.unusedSectionVars false

section Model

variable {K : Type} [Field K] (σ : K ≃+* K)

abbrev Cm : Type := ↥(graphFixedRootGroup TwistTag.D4 K σ.toRingHom)

noncomputable abbrev Ust : Subgroup (Cm σ) :=
  (graphFixedPosUnipotent TwistTag.D4 K σ.toRingHom).subgroupOf
    (graphFixedRootGroup TwistTag.D4 K σ.toRingHom)

noncomputable abbrev Pst0 : Subgroup (Cm σ) :=
  (graphFixedParabolic TwistTag.D4 K σ.toRingHom
    {(⟨0, by decide⟩ : Fin TwistTag.D4.foldedTag.rank)}).subgroupOf
    (graphFixedRootGroup TwistTag.D4 K σ.toRingHom)

noncomputable abbrev Pst1 : Subgroup (Cm σ) :=
  (graphFixedParabolic TwistTag.D4 K σ.toRingHom
    {(⟨1, by decide⟩ : Fin TwistTag.D4.foldedTag.rank)}).subgroupOf
    (graphFixedRootGroup TwistTag.D4 K σ.toRingHom)

structure IsNormalized (A : LieAmalgamExt (Cm σ)) : Prop where
  TD_eq : A.TD = Ust σ
  pair : (A.P1 = Pst0 σ ∧ A.P2 = Pst1 σ) ∨ (A.P1 = Pst1 σ ∧ A.P2 = Pst0 σ)

end Model

section Normalize

variable {D : Type} [Group D] {G : Type} [Group G] {M1 M2 : Subgroup G}

theorem map_conj_conj_inv {H : Type} [Group H] (U : Subgroup H) (c : H) :
    (U.map (MulAut.conj c).toMonoidHom).map (MulAut.conj c⁻¹).toMonoidHom = U := by
  rw [Subgroup.map_map]
  have : (MulAut.conj c⁻¹).toMonoidHom.comp (MulAut.conj c).toMonoidHom = MonoidHom.id H := by
    ext x
    simp [MulAut.conj_apply, mul_assoc]
  rw [this, Subgroup.map_id]

theorem map_refl_eq {H : Type} [Group H] (X : Subgroup H) :
    X.map (MulEquiv.refl H).toMonoidHom = X := by
  ext x
  simp

theorem exists_normalized {f : ℕ} (hD : ChevalleyExceptionalModel D .trialityD4 2 f)
    (E : LieExt D M1 M2) :
    ∃ (K : Type) (_ : Field K) (_ : Finite K) (σ : K ≃+* K), Nat.card K = (2 ^ f) ^ 3 ∧
      (∀ c, σ.toRingHom c = c ^ (2 ^ f)) ∧
      Nonempty (D ≃* Cm σ) ∧
      ∃ E' : LieExt (Cm σ) M1 M2, IsNormalized σ E'.toLieAmalgamExt ∧ Nonempty (LocIso E E') := by
  obtain ⟨hf, K, hF, hFin, σ, hK, hσ, ⟨e⟩⟩ := exists_mulEquiv_triality_model hD
  refine ⟨K, hF, hFin, σ, hK, fun c => hσ c, ⟨e⟩, ?_⟩
  have hS := CFSG.Quasithin.H13.F431.D4q.Hex.d4_yamStd σ hf hK (fun c => hσ c)
  let E1 : LieExt (Cm σ) M1 M2 := E.congr e
  let L1 : LocIso E E1 := E.congrOfLocIso e _ rfl
  obtain ⟨c, hTD, hP⟩ := hS.pair (MulEquiv.refl (Cm σ)) E1.yam
  rw [map_refl_eq] at hTD
  let E2 : LieExt (Cm σ) M1 M2 := E1.conjSylow c⁻¹
  let L2 : LocIso E1 E2 :=
    E1.congrOfLocIso (MulAut.conj c⁻¹) E1.Mbar (E1.Mbar_eq_map_conj c⁻¹)
  refine ⟨E2, ⟨?_, ?_⟩, ⟨L1.trans L2⟩⟩
  · show E1.TD.map (MulAut.conj c⁻¹).toMonoidHom = _
    rw [hTD, map_conj_conj_inv]
  · show (E1.P1.map (MulAut.conj c⁻¹).toMonoidHom = _ ∧
        E1.P2.map (MulAut.conj c⁻¹).toMonoidHom = _) ∨
      (E1.P1.map (MulAut.conj c⁻¹).toMonoidHom = _ ∧
        E1.P2.map (MulAut.conj c⁻¹).toMonoidHom = _)
    rcases hP with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · rw [map_refl_eq] at h1 h2
      left
      rw [h1, h2, map_conj_conj_inv, map_conj_conj_inv]
      exact ⟨rfl, rfl⟩
    · rw [map_refl_eq] at h1 h2
      right
      rw [h1, h2, map_conj_conj_inv, map_conj_conj_inv]
      exact ⟨rfl, rfl⟩

end Normalize

section Generation

variable {K : Type} [Field K] [Finite K] (σ : K ≃+* K)

theorem Pst_sup {f : ℕ} (hf : 1 ≤ f) (hK : Nat.card K = (2 ^ f) ^ 3)
    (hσ : ∀ c, σ.toRingHom c = c ^ (2 ^ f)) : Pst0 σ ⊔ Pst1 σ = ⊤ := by
  have hS := CFSG.Quasithin.H13.F431.D4q.Hex.d4_yamStd σ hf hK hσ
  exact hS.coatom₀.sup_eq_top_of_ne hS.coatom₁ hS.ne

theorem IsNormalized.inn_le_K {f : ℕ} (hf : 1 ≤ f) (hK : Nat.card K = (2 ^ f) ^ 3)
    (hσ : ∀ c, σ.toRingHom c = c ^ (2 ^ f)) {A : LieAmalgamExt (Cm σ)} (h : IsNormalized σ A) :
    (MulAut.conj : Cm σ →* MulAut (Cm σ)).range ≤ A.K := by
  refine A.range_conj_le_K ?_
  rcases h.pair with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · rw [h1, h2]
    exact Pst_sup σ hf hK hσ
  · rw [h1, h2, sup_comm]
    exact Pst_sup σ hf hK hσ

end Generation

section Reduction

@[expose] def TwoOutNorm (f : ℕ) : Prop :=
  ∀ (K : Type) [Field K] [Finite K] (σ : K ≃+* K), Nat.card K = (2 ^ f) ^ 3 →
    (∀ c, σ.toRingHom c = c ^ (2 ^ f)) → ∀ A : LieAmalgamExt (Cm σ), IsNormalized σ A →
      ¬ Odd (Nat.card ↥A.K / Nat.card (Cm σ)) → TwoOutConcl A

theorem f431TwoOutLieProp_of_normalized (f : ℕ) (H : TwoOutNorm f) :
    F431TwoOutLieProp .trialityD4 0 f := by
  intro D _ hD A hnodd
  obtain ⟨-, hX⟩ := chevalley_of_lieModel hD (by decide)
  obtain ⟨K, hF, hFin, σ, hK, hσ, ⟨e⟩, E', hN, ⟨L⟩⟩ := exists_normalized hX A.toLieExt
  have : Finite (ModGL TwistTag.D4.tag K) := finite_modGL
  have : Finite D := Finite.of_injective e e.injective
  have : Finite (MulAut D) :=
    Finite.of_injective (fun φ : MulAut D => (φ : D → D)) fun _ _ h => MulEquiv.ext (congrFun h)
  have : Finite ↥E'.K := inferInstance
  have hcard : Nat.card ↥E'.K / Nat.card (Cm σ) = Nat.card ↥A.K / Nat.card D := by
    rw [L.toKIso.card_K, Nat.card_congr e.toEquiv.symm]
    rfl
  exact L.toKIso.twoOutConcl (H K σ hK hσ E'.toLieAmalgamExt hN (hcard ▸ hnodd))

end Reduction

end CFSG.Quasithin.H13.F431.D4q.Struct
