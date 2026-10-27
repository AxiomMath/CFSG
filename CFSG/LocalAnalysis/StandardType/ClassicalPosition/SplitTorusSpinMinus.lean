module

public import CFSG.LocalAnalysis.StandardType.GGOmegaMinusRootGenConj
public import CFSG.LocalAnalysis.StandardType.GGTableBOrthogonalBasic
public import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotQ2OmegaPESpinM
public import CFSG.LocalAnalysis.StandardType.ClassicalPosition.SpinMinusRootTorus
public import CFSG.LieType.Ree.LargeReeInvolutionTwoCentralizers
public import CFSG.LieType.Steinberg.CentralExt.SpinPlusCentrallyClosed
public import CFSG.LocalAnalysis.ComponentClassification.CatLeafOddB
public import CFSG.LocalAnalysis.ComponentClassification.ExcSelectorEvenTriality
public import CFSG.LocalAnalysis.ComponentClassification.RankTwoHypIIL3Rigid
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Lin2.InA3Five
public import CFSG.LocalAnalysis.SeitzReduction.E6PilotLeviPerp
public import CFSG.LocalAnalysis.SeitzReduction.E8PilotQ2PositionWork
public import CFSG.LocalAnalysis.SeitzReduction.E8PilotSwapLift
public import CFSG.LocalAnalysis.SeitzReduction.F4PilotCatEvenClassical
public import CFSG.LocalAnalysis.SeitzReduction.F4PilotCatEvenExc
public import CFSG.LocalAnalysis.SeitzReduction.F4PilotMainGraphUnitaryNormal
public import CFSG.LocalAnalysis.SeitzReduction.LinearPilotQ2SmallJ
public import CFSG.LocalAnalysis.SeitzReduction.LinearPilotTwistedFusion
public import CFSG.LocalAnalysis.SeitzReduction.LinearPilotWeakCTGlobal
public import CFSG.LocalAnalysis.SeitzReduction.OmegaPilotCatCovers
public import CFSG.LocalAnalysis.SeitzReduction.OmegaPilotHR7iii
public import CFSG.LocalAnalysis.SeitzReduction.OmegaPilotHR8Field
public import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotGraphOmegaNeighbour
public import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotGraphUnitaryPower
public import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotHR14LUUnitary
public import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotHR14ModelUnitary
public import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotHR14OmegaOuterMinus
public import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotHR14PartnerCoset
public import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotHR14PartnerSp
public import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotHR14Transfer
public import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotKindUnitaryGlobal
public import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotOmegaRowUniqueStep
public import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotParamMain
public import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotQ2OmegaPEAbstract
public import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotQ2OmegaPESpin
public import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotQ2RowOmegaClass
public import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotQ2RowOmegaUnitaryRows
public import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotQ2RowUnitaryCover
public import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotRecognizeFieldFour
public import CFSG.LocalAnalysis.SeitzReduction.UnitaryPilotInvolutionTwoPartEvenInner
public import CFSG.LocalAnalysis.SeitzReduction.UnitaryPilotUniqueTypeGraph
public import CFSG.Monster.B.TwoA.Unitary.Orbit1408Points
public import CFSG.Quasithin.Background.A1cTransfer
public import CFSG.Sporadic.Bridge.LyData
public import CFSG.Sporadic.Fi24.Faithful
public import CFSG.Sporadic.Fi24.SepSpec
public import CFSG.Sporadic.HN.CertificateBase
public import CFSG.Sporadic.Ly.ActionBase
public import CFSG.Sporadic.Ly.CertificateBase
public import CFSG.Sporadic.Ly.FaithSpec
public import CFSG.Sporadic.Ly.OrbitSpec
public import CFSG.Sporadic.Ly.Simple
public import CFSG.Sporadic.LyBase
public import CFSG.Sporadic.ON.SimpleBase
public import CFSG.Sporadic.Presentation.Ly
public import CFSG.Sporadic.Schreier.LyChain11
public import Certificates.Certificate1016Base
public import Certificates.Certificate1021
public import Certificates.Certificate3085Base

public noncomputable section

namespace CFSG.StandardType.ClassicalPosition

open CFSG.Assembly CFSG.Open CFSG.LieType.Universal
open scoped Matrix

theorem spinMinus_splitTorus_mem_ggTorus
    {F : Type} [Field F] [Finite F] [CharP F 2] {b c : F} {m : ℕ}
    (hm : 3 ≤ m) (hirr : ∀ s : F, s ^ 2 + b * s + c ≠ 0)
    {p : ℕ} {ζ : Fˣ} (hζ : ζ ^ p = 1) (u : Fin m → Multiplicative (ZMod p)) :
    (CFSG.SeitzReduction.SymplecticPilot.peRhoMEquiv (by omega : 4 ≤ m + 1) hirr).symm
        (omMinusTorus b c hζ u) ∈ ggTorus (Spin.Twisted.minusDatum (m + 1) hirr) := by
  let e := CFSG.SeitzReduction.SymplecticPilot.peRhoMEquiv (by omega : 4 ≤ m + 1) hirr
  let g := e.symm (omMinusTorus b c hζ u)
  let t := omMinusTorusParam m hζ u
  have hg : CFSG.SeitzReduction.SymplecticPilot.peRhoM (by omega : 4 ≤ m + 1) hirr g =
      omMinusTorus b c hζ u := e.apply_symm_apply _
  have hact (v : Fin (m + 1 - 1) ⊕ Fin (m + 1 - 1) ⊕ Fin 2 → F) :
      Spin.spinAction (Spin.quadMinus (m + 1) F b c) g v =
        (CFSG.SeitzReduction.SymplecticPilot.kOmMDiag F m t :
          Matrix (Fin (m + 1 - 1) ⊕ Fin (m + 1 - 1) ⊕ Fin 2)
            (Fin (m + 1 - 1) ⊕ Fin (m + 1 - 1) ⊕ Fin 2) F) *ᵥ v := by
    rw [← CFSG.SeitzReduction.SymplecticPilot.peRhoM_mulVec
      (by omega : 4 ≤ m + 1) hirr g v, hg]
    rfl
  refine mem_ggTorus_minusDatum_of_frame_scalars hirr g
    (fun i s => if s then t i else (t i)⁻¹) ?_ ?_
  · intro i s
    rw [hact, CFSG.SeitzReduction.SymplecticPilot.kOmMDiag_coe]
    cases s
    · simp only [Spin.Twisted.minusVec_false, Spin.Twisted.fVec,
        Matrix.diagonal_mulVec_single, CFSG.SeitzReduction.SymplecticPilot.kOmMWeight_inr_inl,
        Bool.false_eq_true, ↓reduceIte, mul_one]
      rw [← Pi.single_smul, smul_eq_mul, mul_one]
    · simp only [Spin.Twisted.minusVec_true, Spin.Twisted.eVec,
        Matrix.diagonal_mulVec_single, CFSG.SeitzReduction.SymplecticPilot.kOmMWeight_inl,
        ↓reduceIte, mul_one]
      rw [← Pi.single_smul, smul_eq_mul, mul_one]
  · intro v
    rw [hact, CFSG.SeitzReduction.SymplecticPilot.kOmMDiag_coe]
    funext j
    rw [Matrix.mulVec_diagonal]
    rcases j with i | i | j <;>
      simp [Spin.Twisted.planeVec, CFSG.SeitzReduction.SymplecticPilot.kOmMWeight]

theorem exists_spinMinus_splitTorus_equiv
    {F : Type} [Field F] [Finite F] [CharP F 2] {b c : F}
    (hirr : ∀ s : F, s ^ 2 + b * s + c ≠ 0) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hpF : p ∣ Nat.card F - 1)
    (E : Subgroup ↥(spinGroup (Spin.quadMinus 4 F b c))) (hE : IsElemAbelian p E)
    (hcard : p ^ 3 ≤ Nat.card E) :
    ∃ (ζ : Fˣ) (hζ : ζ ^ p = 1), orderOf ζ = p ∧
      ∃ η : ↥(spinGroup (Spin.quadMinus 4 F b c)) ≃*
          ↥(StatedOmega (StatedQuadMinus 4 F b c)),
        E.map η.toMonoidHom = (omMinusTorus b c hζ).range := by
  have : Fact p.Prime := ⟨hp⟩
  let e : ↥(spinGroup (Spin.quadMinus 4 F b c)) ≃*
      ↥(StatedOmega (StatedQuadMinus 4 F b c)) :=
    CFSG.SeitzReduction.SymplecticPilot.peRhoMEquiv (by decide : 4 ≤ 4) hirr
  have hEe : IsElemAbelian p (E.map e.toMonoidHom) := IsElemAbelian.map hE e.toMonoidHom
  have hcarde : p ^ 3 ≤ Nat.card (E.map e.toMonoidHom) := by
    calc
      p ^ 3 ≤ Nat.card E := hcard
      _ = Nat.card (E.map e.toMonoidHom) :=
        (Subgroup.card_map_of_injective (K := E) (f := e.toMonoidHom) e.injective).symm
  obtain ⟨ζ, hζo, hζ, _, _⟩ := TableBOrth.exists_zeta hp hp2 hpF
  obtain ⟨α, hα⟩ := exists_mulEquiv_eq_map_omMinusTorus (m := 3) hp2 hirr hζ hζo hEe hcarde
  let η := e.trans α.symm
  have ha : α.symm.toMonoidHom.comp α.toMonoidHom = MonoidHom.id _ := by
    apply MonoidHom.ext
    intro x
    exact α.symm_apply_apply x
  refine ⟨ζ, hζ, hζo, η, ?_⟩
  calc
    E.map η.toMonoidHom = (E.map e.toMonoidHom).map α.symm.toMonoidHom := by
      rw [Subgroup.map_map]
      rfl
    _ = ((omMinusTorus b c hζ).range.map α.toMonoidHom).map α.symm.toMonoidHom := by rw [hα]
    _ = (omMinusTorus b c hζ).range := by rw [Subgroup.map_map, ha, Subgroup.map_id]

end CFSG.StandardType.ClassicalPosition
