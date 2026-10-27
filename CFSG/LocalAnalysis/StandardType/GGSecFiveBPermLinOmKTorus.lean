module

public import CFSG.LocalAnalysis.StandardType.GGOmegaMinusRootGenConj
public import CFSG.LocalAnalysis.StandardType.GGPsiDiagInnerMinusTorus
public import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotQ2OmegaPESpinM
import CFSG.LocalAnalysis.StandardType.GGOmegaMinusRootGenWeyl
import CFSG.LocalAnalysis.StandardType.GGOmegaMinusRootGenComp
public import CFSG.LieType.Ree.LargeReeInvolutionTwoCentralizers
public import CFSG.LieType.Steinberg.CentralExt.SpinPlusCentrallyClosed
public import CFSG.LocalAnalysis.ComponentClassification.CatLeafOddB
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalSixStructure
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
public import CFSG.RankThree.PartOne.AUTSL.OmegaFamily
public import CFSG.RankThree.PartOne.AUTSL.Rows
public import CFSG.RankThree.PartOne.AUTSL.SylowTrick
public import CFSG.RankThree.PartOne.CTP.StrongPSylow
public import CFSG.RankThree.PartOne.KC.OrthogonalHighWittFixedSpace
public import CFSG.RankThree.PartOne.KC.OrthogonalSubfieldFixed
public import CFSG.RankThree.PartOne.S12.Sec1511Y1
public import CFSG.RankThree.PartOne.S12.Sec15Items
public import CFSG.RankThree.SteinbergR3EOrthogonalCoprimeCyclic
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

public section

namespace CFSG.StandardType

open CFSG.Open CFSG.SeitzReduction CFSG.LieType.Universal CFSG.LieType.Universal.Spin
  CFSG.LieType.Universal.Spin.Twisted
open scoped Matrix

variable {F : Type} [Field F] [Finite F] [CharP F 2] {b c : F} {r p : ℕ} {ω : Fˣ}

@[expose] noncomputable def spinMinusSplitTorus (hr : 2 ≤ r)
    (hirr : ∀ s : F, s ^ 2 + b * s + c ≠ 0) (hω : ω ^ p = 1) :
    (Fin (r + 1) → Multiplicative (ZMod p)) →* spinGroup (quadMinus (r + 2) F b c) :=
  (SymplecticPilot.peRhoMEquiv (by omega : 4 ≤ r + 2) hirr).symm.toMonoidHom.comp
    (omMinusTorus b c hω (m := r + 1))

theorem spinMinusSplitTorus_spinMatrix (hr : 2 ≤ r) (hirr : ∀ s : F, s ^ 2 + b * s + c ≠ 0)
    (hω : ω ^ p = 1) (u : Fin (r + 1) → Multiplicative (ZMod p)) :
    spinMatrix (quadMinus (r + 2) F b c) (spinMinusSplitTorus hr hirr hω u) =
      omMinusTorusGL hω u :=
  congrArg (fun A : StatedOmega (StatedQuadMinus (r + 2) F b c) =>
    (A : GL (Fin (r + 2 - 1) ⊕ Fin (r + 2 - 1) ⊕ Fin 2) F))
    ((SymplecticPilot.peRhoMEquiv (n := r + 2) (by omega : 4 ≤ r + 2) hirr).apply_symm_apply
      (omMinusTorus b c hω (m := r + 1) u))

theorem spinMinusSplitTorus_injective [NeZero p] (hr : 2 ≤ r)
    (hirr : ∀ s : F, s ^ 2 + b * s + c ≠ 0) (hω : ω ^ p = 1) (hωo : orderOf ω = p) :
    Function.Injective (spinMinusSplitTorus hr hirr hω) := by
  intro u v huv
  have h : omMinusTorusGL (K := F) (m := r + 1) hω u =
      omMinusTorusGL (K := F) (m := r + 1) hω v := by
    rw [← spinMinusSplitTorus_spinMatrix hr hirr hω u,
      ← spinMinusSplitTorus_spinMatrix hr hirr hω v, huv]
  exact omMinusTorusGL_injective (K := F) (m := r + 1) hω hωo h

theorem spinMinusSplitTorus_diagAct (hr : 2 ≤ r) (hirr : ∀ s : F, s ^ 2 + b * s + c ≠ 0)
    (hω : ω ^ p = 1) (u : Fin (r + 1) → Multiplicative (ZMod p)) :
    PsiDiag.SpinM.DiagAct (spinMinusSplitTorus hr hirr hω u)
      (fun k : Fin (r + 1) => TableBSymp.zmodPowHom hω (u k)) := by
  let e := SymplecticPilot.peRhoMEquiv (n := r + 2) (by omega : 4 ≤ r + 2) hirr
  let g := spinMinusSplitTorus hr hirr hω u
  let t : Fin (r + 1) → Fˣ := fun k => TableBSymp.zmodPowHom hω (u k)
  have hg : SymplecticPilot.peRhoM (n := r + 2) (by omega : 4 ≤ r + 2) hirr g =
      omMinusTorus b c hω (m := r + 1) u := e.apply_symm_apply _
  have hact (v : Fin (r + 2 - 1) ⊕ Fin (r + 2 - 1) ⊕ Fin 2 → F) :
      spinAction (quadMinus (r + 2) F b c) g v =
        (SymplecticPilot.kOmMDiag F (r + 1) t :
          Matrix (Fin (r + 2 - 1) ⊕ Fin (r + 2 - 1) ⊕ Fin 2)
            (Fin (r + 2 - 1) ⊕ Fin (r + 2 - 1) ⊕ Fin 2) F) *ᵥ v := by
    rw [← SymplecticPilot.peRhoM_mulVec (n := r + 2) (by omega : 4 ≤ r + 2) hirr g v,
      hg]
    rfl
  refine ⟨fun l => ?_, fun l => ?_, fun p => ?_⟩
  · rw [hact, SymplecticPilot.kOmMDiag_coe]
    simp only [Spin.Twisted.minusVec_true, Spin.Twisted.eVec,
      Matrix.diagonal_mulVec_single, SymplecticPilot.kOmMWeight_inl, ↓reduceIte, mul_one]
    rw [← Pi.single_smul, smul_eq_mul, mul_one]
  · rw [hact, SymplecticPilot.kOmMDiag_coe]
    simp only [Spin.Twisted.minusVec_false, Spin.Twisted.fVec,
      Matrix.diagonal_mulVec_single, SymplecticPilot.kOmMWeight_inr_inl, Bool.false_eq_true,
      ↓reduceIte, mul_one]
    rw [← Pi.single_smul, smul_eq_mul, mul_one]
  · rw [hact, SymplecticPilot.kOmMDiag_coe]
    funext j
    rw [Matrix.mulVec_diagonal]
    rcases j with i | i | j <;>
      simp [Spin.Twisted.planeVec, SymplecticPilot.kOmMWeight]

theorem spinMinusSplitTorus_conj_update (hr : 2 ≤ r) (hirr : ∀ s : F, s ^ 2 + b * s + c ≠ 0)
    (hω : ω ^ p = 1) (l : Fin (r + 1)) :
    ∃ w : spinGroup (quadMinus (r + 2) F b c), ∀ t : Fin (r + 1) → Multiplicative (ZMod p),
      w * spinMinusSplitTorus hr hirr hω t * w⁻¹ =
        spinMinusSplitTorus hr hirr hω (Function.update t l (t l)⁻¹) := by
  obtain ⟨w, hw, hconj⟩ := exists_sgn_mem_omMinusLongBlock (m := r + 1) (p := p) hirr hω l
  have hwΩ : w ∈ StatedOmega (StatedQuadMinus (r + 2) F b c) := omMinusLongBlock_le hirr l hw
  have hmain : ∀ t : Fin (r + 1) → Multiplicative (ZMod p),
      (⟨w, hwΩ⟩ : StatedOmega (StatedQuadMinus (r + 2) F b c)) *
          omMinusTorus b c hω (m := r + 1) t * (⟨w, hwΩ⟩ : StatedOmega _)⁻¹ =
        omMinusTorus b c hω (m := r + 1) (Function.update t l (t l)⁻¹) := by
    intro t
    apply Subtype.ext
    simp only [Subgroup.coe_mul, Subgroup.coe_inv, coe_omMinusTorus]
    rw [hconj t, SpCoord.sgnAut_apply]
  refine ⟨(SymplecticPilot.peRhoMEquiv (n := r + 2) (by omega : 4 ≤ r + 2) hirr).symm
    ⟨w, hwΩ⟩, fun t => ?_⟩
  apply (SymplecticPilot.peRhoMEquiv (n := r + 2) (by omega : 4 ≤ r + 2) hirr).injective
  simpa only [map_mul, map_inv, MulEquiv.apply_symm_apply, spinMinusSplitTorus,
    MulEquiv.coe_toMonoidHom, MonoidHom.comp_apply] using hmain t

private theorem exists_mulAut_of_conj_mem_range {M N : Type*} [Group M] [Finite M] [Group N]
    (D : M →* N) (hD : Function.Injective D) (u : N)
    (h : ∀ f, ∃ f', u * D f * u⁻¹ = D f') : ∃ a : MulAut M, ∀ f, u * D f * u⁻¹ = D (a f) := by
  classical
  choose a ha using h
  have h1 : a 1 = 1 := by
    apply hD
    rw [← ha 1]
    simp
  have hmul : ∀ f f', a (f * f') = a f * a f' := by
    intro f f'
    apply hD
    rw [← ha (f * f'), map_mul, map_mul, ← ha f, ← ha f']
    group
  let A : M →* M := { toFun := a, map_one' := h1, map_mul' := hmul }
  have hinj : Function.Injective A := by
    intro f f' hff'
    have h2 : D (a f) = D (a f') := congrArg D hff'
    apply hD
    calc D f = u⁻¹ * D (a f) * u := by rw [← ha f]; group
      _ = u⁻¹ * D (a f') * u := by rw [h2]
      _ = D f' := by rw [← ha f']; group
  refine ⟨MulEquiv.ofBijective A ⟨hinj, Finite.injective_iff_surjective.mp hinj⟩, fun f => ?_⟩
  exact ha f

theorem spinMinusSplitTorus_signedPerm_of_normalizes [Fact p.Prime] (hr : 2 ≤ r)
    (hirr : ∀ s : F, s ^ 2 + b * s + c ≠ 0) (hω : ω ^ p = 1) (hωo : orderOf ω = p)
    (u : spinGroup (quadMinus (r + 2) F b c))
    (hu : ∀ f, ∃ f', u * spinMinusSplitTorus hr hirr hω f * u⁻¹ =
      spinMinusSplitTorus hr hirr hω f') :
    ∃ (π : Equiv.Perm (Fin (r + 1))) (ε : Fin (r + 1) → ZMod p), (∀ i, ε i = 1 ∨ ε i = -1) ∧
      ∀ f f', u * spinMinusSplitTorus hr hirr hω f * u⁻¹ = spinMinusSplitTorus hr hirr hω f' →
        ∀ i, Multiplicative.toAdd (f' (π i)) = ε i * Multiplicative.toAdd (f i) := by
  have hp : p.Prime := Fact.out
  have hgc : ∀ f, ∃ f',
      spinMatrix (quadMinus (r + 2) F b c) u * omMinusTorusGL (K := F) (m := r + 1) hω f *
          (spinMatrix (quadMinus (r + 2) F b c) u)⁻¹ =
        omMinusTorusGL (K := F) (m := r + 1) hω f' := by
    intro f
    obtain ⟨f', hf'⟩ := hu f
    refine ⟨f', ?_⟩
    have h := congrArg (spinMatrix (quadMinus (r + 2) F b c)) hf'
    simpa only [map_mul, map_inv, spinMinusSplitTorus_spinMatrix hr hirr hω] using h
  obtain ⟨a, ha⟩ := exists_mulAut_of_conj_mem_range
    (D := omMinusTorusGL (K := F) (m := r + 1) hω)
    (omMinusTorusGL_injective (K := F) (m := r + 1) hω hωo)
    (spinMatrix (quadMinus (r + 2) F b c) u) hgc
  have hsp := isSignedPerm_of_conj_omMinusTorusGL hp hω hωo
    (spinMatrix (quadMinus (r + 2) F b c) u) a ha
  obtain ⟨π, ε, hε, hπ⟩ := hsp
  refine ⟨π, ε, hε, fun f f' hff' i => ?_⟩
  have hmat : omMinusTorusGL (K := F) (m := r + 1) hω f' =
      omMinusTorusGL (K := F) (m := r + 1) hω (a f) := by
    rw [← ha f]
    have h := congrArg (spinMatrix (quadMinus (r + 2) F b c)) hff'
    simpa only [map_mul, map_inv, spinMinusSplitTorus_spinMatrix hr hirr hω] using h.symm
  have hff : f' = a f := omMinusTorusGL_injective (K := F) (m := r + 1) hω hωo hmat
  rw [hff]
  exact hπ f i

theorem spinMinusSplitTorus_exists_mulAut [Fact p.Prime] (hp2 : p ≠ 2) (hr : 2 ≤ r)
    (hirr : ∀ s : F, s ^ 2 + b * s + c ≠ 0) (hω : ω ^ p = 1) (hωo : orderOf ω = p)
    (E : Subgroup ↥(spinGroup (quadMinus (r + 2) F b c))) (hE : IsElemAbelian p E)
    (hcard : p ^ (r + 1) ≤ Nat.card E) :
    ∃ β : MulAut ↥(spinGroup (quadMinus (r + 2) F b c)),
      E.map β.toMonoidHom = (spinMinusSplitTorus hr hirr hω).range := by
  let e : ↥(spinGroup (quadMinus (r + 2) F b c)) ≃*
      ↥(StatedOmega (StatedQuadMinus (r + 2) F b c)) :=
    SymplecticPilot.peRhoMEquiv (n := r + 2) (by omega : 4 ≤ r + 2) hirr
  have hEe : IsElemAbelian p (E.map e.toMonoidHom) := IsElemAbelian.map hE e.toMonoidHom
  have hcarde : p ^ (r + 1) ≤ Nat.card (E.map e.toMonoidHom) := by
    calc
      p ^ (r + 1) ≤ Nat.card E := hcard
      _ = Nat.card (E.map e.toMonoidHom) :=
        (Subgroup.card_map_of_injective (K := E) (f := e.toMonoidHom) e.injective).symm
  obtain ⟨α, hα⟩ := exists_mulEquiv_eq_map_omMinusTorus (m := r + 1) hp2 hirr hω hωo hEe hcarde
  have ha : α.symm.toMonoidHom.comp α.toMonoidHom = MonoidHom.id _ := by
    apply MonoidHom.ext
    intro x
    exact α.symm_apply_apply x
  have h2 : ((omMinusTorus b c hω (m := r + 1)).range.map α.toMonoidHom).map
        α.symm.toMonoidHom = (omMinusTorus b c hω (m := r + 1)).range := by
    rw [Subgroup.map_map, ha, Subgroup.map_id]
  refine ⟨(e.trans α.symm).trans e.symm, ?_⟩
  calc
    E.map ((e.trans α.symm).trans e.symm).toMonoidHom =
        ((E.map e.toMonoidHom).map α.symm.toMonoidHom).map e.symm.toMonoidHom := by
      rw [Subgroup.map_map, Subgroup.map_map]
      rfl
    _ = (((omMinusTorus b c hω (m := r + 1)).range.map α.toMonoidHom).map
          α.symm.toMonoidHom).map e.symm.toMonoidHom := by rw [hα]
    _ = (omMinusTorus b c hω (m := r + 1)).range.map e.symm.toMonoidHom := by rw [h2]
    _ = (spinMinusSplitTorus hr hirr hω).range := by
      rw [← MonoidHom.range_comp]
      rfl

end CFSG.StandardType

end
