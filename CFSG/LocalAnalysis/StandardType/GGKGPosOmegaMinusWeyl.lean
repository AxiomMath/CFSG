module

public import CFSG.LocalAnalysis.StandardType.GGOmegaMinusRootGenWeyl
public import CFSG.LocalAnalysis.StandardType.GGTorusWeylFrameSigned
public import CFSG.LocalAnalysis.StandardType.GGTorusWeylFrame
public import CFSG.LocalAnalysis.StandardType.GGTorusWeylBstar
public import CFSG.LocalAnalysis.StandardType.GGSecFivePresTagSpin
public import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotKindOmegaMinusPiecesTwisted
public import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotQ2OmegaPESpinM
import Mathlib.Tactic.Group
public import CFSG.LieType.Ree.LargeReeInvolutionTwoCentralizers
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
public import CFSG.RankThree.PartOne.AUTSL.OmegaFamily
public import CFSG.RankThree.PartOne.AUTSL.Rows
public import CFSG.RankThree.PartOne.AUTSL.SylowTrick
public import CFSG.RankThree.PartOne.S12.Sec1511Y1
public import CFSG.RankThree.PartOne.S12.Sec15Items
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

open CFSG.LieType.Universal CFSG.LieType.Universal.Spin
  CFSG.LieType.Universal.Spin.Twisted CFSG.SeitzReduction CFSG.SeitzReduction.SymplecticPilot
  Multiplicative Matrix
open CFSG.ClassicalGroups.Orthogonal (toLinEquiv toLinEquiv_apply)
open CFSG.Assembly.LowTwoRank CFSG.Open CFSG.LieType.RootSystem


theorem coxeterMatrix_cartanB_eq_B (n : ℕ) :
    coxeterMatrix (isFiniteType_cartanB n) = CoxeterMatrix.B n := by
  have key : ∀ i j : Fin n, i.val < j.val →
      coxeterMatrix (isFiniteType_cartanB n) i j = CoxeterMatrix.B n i j := by
    intro i j hij
    have hijne : i ≠ j := Fin.ne_of_val_ne (by omega)
    by_cases h1 : i.val + 1 = j.val
    · by_cases h2 : j.val + 1 < n
      · rw [Spin.OddCT.coxeterMatrix_of_succ h1 h2]
        simp only [CoxeterMatrix.B, Matrix.of_apply, if_neg hijne]
        split_ifs <;> omega
      · have h2' : j.val + 1 = n := by omega
        rw [Spin.OddCT.coxeterMatrix_of_succ_last h1 h2']
        simp only [CoxeterMatrix.B, Matrix.of_apply, if_neg hijne]
        split_ifs <;> omega
    · have h2 : j.val + 1 ≠ i.val := by omega
      rw [Spin.OddCT.coxeterMatrix_of_far hijne h1 h2]
      simp only [CoxeterMatrix.B, Matrix.of_apply, if_neg hijne]
      split_ifs <;> omega
  ext i j
  rcases lt_trichotomy i.val j.val with h | h | h
  · exact key i j h
  · have hij : i = j := Fin.ext h
    subst hij
    simp
  · rw [(coxeterMatrix (isFiniteType_cartanB n)).symmetric i j,
      (CoxeterMatrix.B n).symmetric i j]
    exact key j i h

theorem spinMatrix_minusWeyl_conj_omMinusTorus
    {F : Type} [Field F] [Finite F] [CharP F 2] {b c : F}
    (hirr : ∀ s : F, s ^ 2 + b * s + c ≠ 0) {p : ℕ} {ζ : Fˣ}
    (hζ : ζ ^ p = 1) (k : Fin 3) (u : Fin 3 → Multiplicative (ZMod p)) :
    spinMatrix (quadMinus 4 F b c) (minusWeyl 4 hirr k) * omMinusTorusGL hζ u *
        (spinMatrix (quadMinus 4 F b c) (minusWeyl 4 hirr k))⁻¹ =
      omMinusTorusGL hζ (SpJoin.spReflPerm 3 p k u) := by
  classical
  let g := spinMatrix (quadMinus 4 F b c) (minusWeyl 4 hirr k)
  let χ := TableBSymp.zmodPowHom hζ
  have hdvec (v : Fin 3 → Multiplicative (ZMod p)) (i : Fin 3) (s : Bool) :
      (omMinusTorusGL hζ v : Matrix (Fin 3 ⊕ Fin 3 ⊕ Fin 2) (Fin 3 ⊕ Fin 3 ⊕ Fin 2) F) *ᵥ minusVec 4 i s =
        (if s then (χ (v i) : F) else ((χ (v i))⁻¹ : F)) • minusVec 4 i s := by
    cases s
    · rw [minusVec_false, fVec, omMinusTorusGL_apply, ← toLinEquiv_apply,
        kOmM_toLinEquiv_diag_single, kOmMWeight_inr_inl]
      simp [χ, omMinusTorusParam_apply]
    · rw [minusVec_true, eVec, omMinusTorusGL_apply, ← toLinEquiv_apply,
        kOmM_toLinEquiv_diag_single, kOmMWeight_inl]
      simp [χ, omMinusTorusParam_apply]
  have hdplane (v : Fin 3 → Multiplicative (ZMod p)) (a : Fin 2 → F) :
      (omMinusTorusGL hζ v : Matrix (Fin 3 ⊕ Fin 3 ⊕ Fin 2) (Fin 3 ⊕ Fin 3 ⊕ Fin 2) F) *ᵥ planeVec 4 a =
        planeVec 4 a := by
    rw [omMinusTorusGL_apply, ← toLinEquiv_apply, kOmM_toLinEquiv_diag_planeVec]
  have hm : g * omMinusTorusGL hζ u = omMinusTorusGL hζ (SpJoin.spReflPerm 3 p k u) * g := by
    apply Units.ext
    simp only [Units.val_mul]
    apply Matrix.ext_of_mulVec_single
    intro a
    rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec]
    by_cases hk : k.val + 1 < 3
    · let j : Fin 3 := ⟨k.val + 1, hk⟩
      have hgvec (i : Fin 3) (s : Bool) :
          (g : Matrix (Fin 3 ⊕ Fin 3 ⊕ Fin 2) (Fin 3 ⊕ Fin 3 ⊕ Fin 2) F) *ᵥ minusVec 4 i s =
            minusVec 4 (Equiv.swap k j i) s := by
        dsimp only [g]
        rw [spinMatrix_mulVec, minusWeyl_of_lt 4 hirr hk]
        have h := (minusFrame 4 b c).spinAction_longWeyl_vec (succ_ne_of_lt 4 hk) true false i s
        simpa only [minusFrame_vec, longWeylBool_true_false, longWeylSign,
          CharTwo.neg_eq, ite_self, one_smul] using h
      have hgplane (a : Fin 2 → F) :
          (g : Matrix (Fin 3 ⊕ Fin 3 ⊕ Fin 2) (Fin 3 ⊕ Fin 3 ⊕ Fin 2) F) *ᵥ planeVec 4 a = planeVec 4 a := by
        dsimp only [g]
        rw [spinMatrix_mulVec, minusWeyl_of_lt 4 hirr hk]
        exact spinAction_longWeyl_planeVec 4 (succ_ne_of_lt 4 hk) true false a
      have hcoord (i : Fin 3) : SpJoin.spReflPerm 3 p k u (Equiv.swap k j i) = u i := by
        rw [SpJoin.spReflPerm_of_lt 3 p k hk, SpJoin.coordPerm_apply]
        simp only [Equiv.symm_swap]
        change u ((Equiv.swap k j) ((Equiv.swap k j) i)) = u i
        rw [Equiv.swap_apply_self]
      rcases a with i | i | a
      · change (g : Matrix (Fin 3 ⊕ Fin 3 ⊕ Fin 2) (Fin 3 ⊕ Fin 3 ⊕ Fin 2) F) *ᵥ ((omMinusTorusGL hζ u : Matrix (Fin 3 ⊕ Fin 3 ⊕ Fin 2) (Fin 3 ⊕ Fin 3 ⊕ Fin 2) F) *ᵥ minusVec 4 i true) =
          (omMinusTorusGL hζ (SpJoin.spReflPerm 3 p k u) : Matrix (Fin 3 ⊕ Fin 3 ⊕ Fin 2) (Fin 3 ⊕ Fin 3 ⊕ Fin 2) F) *ᵥ
            ((g : Matrix (Fin 3 ⊕ Fin 3 ⊕ Fin 2) (Fin 3 ⊕ Fin 3 ⊕ Fin 2) F) *ᵥ minusVec 4 i true)
        simp only [hdvec, Matrix.mulVec_smul, hgvec, hcoord]
      · change (g : Matrix (Fin 3 ⊕ Fin 3 ⊕ Fin 2) (Fin 3 ⊕ Fin 3 ⊕ Fin 2) F) *ᵥ ((omMinusTorusGL hζ u : Matrix (Fin 3 ⊕ Fin 3 ⊕ Fin 2) (Fin 3 ⊕ Fin 3 ⊕ Fin 2) F) *ᵥ minusVec 4 i false) =
          (omMinusTorusGL hζ (SpJoin.spReflPerm 3 p k u) : Matrix (Fin 3 ⊕ Fin 3 ⊕ Fin 2) (Fin 3 ⊕ Fin 3 ⊕ Fin 2) F) *ᵥ
            ((g : Matrix (Fin 3 ⊕ Fin 3 ⊕ Fin 2) (Fin 3 ⊕ Fin 3 ⊕ Fin 2) F) *ᵥ minusVec 4 i false)
        simp only [hdvec, Matrix.mulVec_smul, hgvec, hcoord]
      · have hv : Pi.single (Sum.inr (Sum.inr a)) (1 : F) =
            planeVec 4 (Pi.single a 1) := by
          funext z
          rcases z with i | i | z <;> simp [planeVec, Pi.single_apply]
        simp only [hv, hdplane, hgplane]
    · have hgvec (i : Fin 3) (s : Bool) :
          (g : Matrix (Fin 3 ⊕ Fin 3 ⊕ Fin 2) (Fin 3 ⊕ Fin 3 ⊕ Fin 2) F) *ᵥ minusVec 4 i s =
            minusVec 4 i (shortWeylBool k i s) := by
        dsimp only [g]
        rw [spinMatrix_mulVec, minusWeyl_of_not_lt 4 hirr hk, spinAction_shortWeyl_minusVec]
        simp only [longWeylSign, CharTwo.neg_eq, ite_self, one_smul]
      have hgplane (a : Fin 2 → F) :
          (g : Matrix (Fin 3 ⊕ Fin 3 ⊕ Fin 2) (Fin 3 ⊕ Fin 3 ⊕ Fin 2) F) *ᵥ planeVec 4 a =
            planeVec 4 (planeRefl b c planeOne a) := by
        dsimp only [g]
        rw [spinMatrix_mulVec, minusWeyl_of_not_lt 4 hirr hk, spinAction_shortWeyl_planeVec']
      have hw (i : Fin 3) (s : Bool) :
          (if shortWeylBool k i s then (χ (SpJoin.spReflPerm 3 p k u i) : F)
            else ((χ (SpJoin.spReflPerm 3 p k u i))⁻¹ : F)) =
          (if s then (χ (u i) : F) else ((χ (u i))⁻¹ : F)) := by
        rw [SpJoin.spReflPerm_of_not_lt 3 p k hk, SpJoin.coordInv_apply]
        by_cases hi : i = k
        · subst i
          cases s <;> simp [shortWeylBool, χ, map_inv]
        · cases s <;> simp [shortWeylBool, hi]
      rcases a with i | i | a
      · change (g : Matrix (Fin 3 ⊕ Fin 3 ⊕ Fin 2) (Fin 3 ⊕ Fin 3 ⊕ Fin 2) F) *ᵥ ((omMinusTorusGL hζ u : Matrix (Fin 3 ⊕ Fin 3 ⊕ Fin 2) (Fin 3 ⊕ Fin 3 ⊕ Fin 2) F) *ᵥ minusVec 4 i true) =
          (omMinusTorusGL hζ (SpJoin.spReflPerm 3 p k u) : Matrix (Fin 3 ⊕ Fin 3 ⊕ Fin 2) (Fin 3 ⊕ Fin 3 ⊕ Fin 2) F) *ᵥ
            ((g : Matrix (Fin 3 ⊕ Fin 3 ⊕ Fin 2) (Fin 3 ⊕ Fin 3 ⊕ Fin 2) F) *ᵥ minusVec 4 i true)
        simp only [hdvec, Matrix.mulVec_smul, hgvec, hw]
      · change (g : Matrix (Fin 3 ⊕ Fin 3 ⊕ Fin 2) (Fin 3 ⊕ Fin 3 ⊕ Fin 2) F) *ᵥ ((omMinusTorusGL hζ u : Matrix (Fin 3 ⊕ Fin 3 ⊕ Fin 2) (Fin 3 ⊕ Fin 3 ⊕ Fin 2) F) *ᵥ minusVec 4 i false) =
          (omMinusTorusGL hζ (SpJoin.spReflPerm 3 p k u) : Matrix (Fin 3 ⊕ Fin 3 ⊕ Fin 2) (Fin 3 ⊕ Fin 3 ⊕ Fin 2) F) *ᵥ
            ((g : Matrix (Fin 3 ⊕ Fin 3 ⊕ Fin 2) (Fin 3 ⊕ Fin 3 ⊕ Fin 2) F) *ᵥ minusVec 4 i false)
        simp only [hdvec, Matrix.mulVec_smul, hgvec, hw]
      · have hv : Pi.single (Sum.inr (Sum.inr a)) (1 : F) =
            planeVec 4 (Pi.single a 1) := by
          funext z
          rcases z with i | i | z <;> simp [planeVec, Pi.single_apply]
        simp only [hv, hdplane, hgplane]
  change g * omMinusTorusGL hζ u * g⁻¹ = _
  rw [hm, mul_inv_cancel_right]



theorem minusWeyl_conj_of_torusMatrix
    {F : Type} [Field F] [Finite F] [CharP F 2] {b c : F}
    (hirr : ∀ s : F, s ^ 2 + b * s + c ≠ 0) {p : ℕ} {ζ : Fˣ} (hζ : ζ ^ p = 1)
    (T : (Fin 3 → Multiplicative (ZMod p)) →* spinGroup (quadMinus 4 F b c))
    (hmatT : ∀ u, spinMatrix (quadMinus 4 F b c) (T u) = omMinusTorusGL hζ u)
    (i : Fin 3) (u : Fin 3 → Multiplicative (ZMod p)) :
    minusWeyl 4 hirr i * T u * (minusWeyl 4 hirr i)⁻¹ = T (SpJoin.spReflPerm 3 p i u) := by
  apply (peRhoM_injective (by decide : 4 ≤ 4) hirr)
  apply Subtype.ext
  change spinMatrix (quadMinus 4 F b c) (minusWeyl 4 hirr i * T u * (minusWeyl 4 hirr i)⁻¹) =
    spinMatrix (quadMinus 4 F b c) (T (SpJoin.spReflPerm 3 p i u))
  rw [map_mul, map_mul, map_inv, hmatT, hmatT]
  exact spinMatrix_minusWeyl_conj_omMinusTorus hirr hζ i u

theorem exists_markedWeyl_spinMinus_of_torusMatrix
    {F : Type} [Field F] [Finite F] [CharP F 2] {b c : F}
    (hirr : ∀ s : F, s ^ 2 + b * s + c ≠ 0) {p : ℕ} {ζ : Fˣ}
    (hp : p.Prime) (hp2 : p ≠ 2) (hζ : ζ ^ p = 1) (hζo : orderOf ζ = p)
    (T : (Fin 3 → Multiplicative (ZMod p)) →* spinGroup (quadMinus 4 F b c))
    (hmatT : ∀ u, spinMatrix (quadMinus 4 F b c) (T u) = omMinusTorusGL hζ u) :
    ∃ hnN : ∀ i : Fin 3, minusWeyl 4 hirr i ∈ Subgroup.normalizer (T.range : Set _),
      ∃ ε : (CoxeterMatrix.B 3).Group ≃* ↥(ggAutomizer (⊤ : Subgroup _) T.range),
        ∀ i : Fin 3, (ε ((CoxeterMatrix.B 3).simple i) : MulAut ↥T.range) =
          ggConjAut T.range (hnN i) := by
  have : Fact p.Prime := ⟨hp⟩
  have : NeZero p := ⟨hp.ne_zero⟩
  let Q := quadMinus 4 F b c
  let U : Type := spinGroup Q
  let V := Fin 3 → Multiplicative (ZMod p)
  have hmat (u : V) : spinMatrix Q (T u) = omMinusTorusGL hζ u := hmatT u
  have hT : Function.Injective T := by
    intro u v huv
    apply omMinusTorusGL_injective hζ hζo
    simpa only [hmat] using congrArg (spinMatrix Q) huv
  have hn (i : Fin 3) (u : V) :
      minusWeyl 4 hirr i * T u * (minusWeyl 4 hirr i)⁻¹ =
        T (SpJoin.spReflPerm 3 p i u) := by
    exact minusWeyl_conj_of_torusMatrix hirr hζ T hmatT i u
  have hN (g : U) (hg : g ∈ Subgroup.normalizer (T.range : Set U)) :
      ∃ σ ∈ SpJoin.spSignedGroup 3 p, ∀ u : V, g * T u * g⁻¹ = T (σ u) := by
    let eT : V ≃* T.range := MonoidHom.ofInjective hT
    have heT (u : V) : (eT u : U) = T u := MonoidHom.ofInjective_apply hT
    let a : MulAut V := (eT.trans (ggConjAut T.range hg)).trans eT.symm
    have hTa (u : V) : g * T u * g⁻¹ = T (a u) := by
      have h := eT.apply_symm_apply (ggConjAut T.range hg (eT u))
      have h' := congrArg (fun x : T.range => (x : U)) h
      change (eT (a u) : U) = (ggConjAut T.range hg (eT u) : U) at h'
      rw [heT, ggConjAut_apply, heT] at h'
      exact h'.symm
    have ha : SpCoord.IsSignedPerm a := by
      refine isSignedPerm_of_conj_omMinusTorusGL hp hζ hζo (spinMatrix Q g) a ?_
      intro u
      simpa only [map_mul, map_inv, hmat] using congrArg (spinMatrix Q) (hTa u)
    exact ⟨a.toEquiv, mem_spSignedGroup_of_isSignedPerm ha, hTa⟩
  obtain ⟨hnN, -, ε, hε⟩ := exists_markedWeylB_ggAutomizer hp2 (by decide : 2 ≤ 3)
    T.range T hT rfl (minusWeyl 4 hirr) hn hN
  exact ⟨hnN, ε, hε⟩


theorem exists_markedWeyl_spinMinus_splitPrimeTorus
    {F : Type} [Field F] [Finite F] [CharP F 2] {b c : F}
    (hirr : ∀ s : F, s ^ 2 + b * s + c ≠ 0) {p : ℕ} {ζ : Fˣ}
    (hp : p.Prime) (hp2 : p ≠ 2) (hζ : ζ ^ p = 1) (hζo : orderOf ζ = p) :
    let e := peRhoMEquiv (by decide : 4 ≤ 4) hirr
    let T := e.symm.toMonoidHom.comp (omMinusTorus b c hζ (m := 3))
    ∃ hnN : ∀ i : Fin 3, minusWeyl 4 hirr i ∈ Subgroup.normalizer (T.range : Set _),
      ∃ ε : (CoxeterMatrix.B 3).Group ≃* ↥(ggAutomizer (⊤ : Subgroup _) T.range),
        ∀ i : Fin 3, (ε ((CoxeterMatrix.B 3).simple i) : MulAut ↥T.range) =
          ggConjAut T.range (hnN i) := by
  dsimp only
  let e := peRhoMEquiv (by decide : 4 ≤ 4) hirr
  let T := e.symm.toMonoidHom.comp (omMinusTorus b c hζ (m := 3))
  have hmatT (u : Fin 3 → Multiplicative (ZMod p)) :
      spinMatrix (quadMinus 4 F b c) (T u) = omMinusTorusGL hζ u :=
    congrArg (fun A : StatedOmega (StatedQuadMinus 4 F b c) =>
      (A : GL (Fin 3 ⊕ Fin 3 ⊕ Fin 2) F)) (e.apply_symm_apply (omMinusTorus b c hζ u))
  exact exists_markedWeyl_spinMinus_of_torusMatrix hirr hp hp2 hζ hζo T hmatT

theorem exists_weylLift_automizer_spinMinus_of_torusMatrix
    {F : Type} [Field F] [Finite F] [CharP F 2] {b c : F}
    (hirr : ∀ s : F, s ^ 2 + b * s + c ≠ 0) {p : ℕ} {ζ : Fˣ}
    (hp : p.Prime) (hp2 : p ≠ 2) (hζ : ζ ^ p = 1) (hζo : orderOf ζ = p)
    (T : (Fin 3 → Multiplicative (ZMod p)) →* spinGroup (quadMinus 4 F b c))
    (hmatT : ∀ u, spinMatrix (quadMinus 4 F b c) (T u) = omMinusTorusGL hζ u) :
    let D := minusDatum 4 hirr
    ∃ ν : GGWeyl D →* spinGroup (quadMinus 4 F b c), GGWeylLift D ν ∧
      ∃ ε : GGWeyl D ≃* ↥(ggAutomizer (⊤ : Subgroup _) T.range),
        (∀ (w : GGWeyl D) (a : T.range),
          ((ε w : MulAut ↥T.range) a : spinGroup (quadMinus 4 F b c)) =
            ν w * (a : spinGroup (quadMinus 4 F b c)) * (ν w)⁻¹) ∧
        ∀ i : Fin 3, ν ((coxeterMatrix D.isFiniteType).simple i) = minusWeyl 4 hirr i := by
  dsimp only
  let D := minusDatum 4 hirr
  let U : Type := spinGroup (quadMinus 4 F b c)
  have hM : coxeterMatrix D.isFiniteType = CoxeterMatrix.B 3 :=
    coxeterMatrix_cartanB_eq_B 3
  obtain ⟨ν, hν, hνs⟩ := exists_weylLift_minusDatum (by decide : 4 ≤ 4) hirr
  obtain ⟨hnN, εB, hεB⟩ := exists_markedWeyl_spinMinus_of_torusMatrix hirr hp hp2 hζ hζo T hmatT
  obtain ⟨ε, hε⟩ := markedWeyl_of_eq hM T.range (minusWeyl 4 hirr) hnN εB hεB
  refine ⟨ν, hν, ε, ?_, hνs⟩
  have hnν (i : Fin 3) : ν ((coxeterMatrix D.isFiniteType).simple i) ∈
      Subgroup.normalizer (T.range : Set U) := by
    rw [hνs i]
    exact hnN i
  refine markedWeyl_apply (M := coxeterMatrix (isFiniteType_cartanB 3)) T.range ν ε hnν ?_
  intro i
  calc
    (ε ((coxeterMatrix D.isFiniteType).simple i) : MulAut ↥T.range) =
        ggConjAut T.range (hnN i) := hε i
    _ = ggConjAut T.range (hnν i) := by
      apply MulEquiv.ext
      intro a
      apply Subtype.ext
      simp only [ggConjAut_apply]
      rw [hνs i]

theorem exists_weylLift_automizer_spinMinus_splitPrimeTorus
    {F : Type} [Field F] [Finite F] [CharP F 2] {b c : F}
    (hirr : ∀ s : F, s ^ 2 + b * s + c ≠ 0) {p : ℕ} {ζ : Fˣ}
    (hp : p.Prime) (hp2 : p ≠ 2) (hζ : ζ ^ p = 1) (hζo : orderOf ζ = p) :
    let D := minusDatum 4 hirr
    let e := peRhoMEquiv (by decide : 4 ≤ 4) hirr
    let T := e.symm.toMonoidHom.comp (omMinusTorus b c hζ (m := 3))
    ∃ ν : GGWeyl D →* spinGroup (quadMinus 4 F b c), GGWeylLift D ν ∧
      ∃ ε : GGWeyl D ≃* ↥(ggAutomizer (⊤ : Subgroup _) T.range),
        (∀ (w : GGWeyl D) (a : T.range),
          ((ε w : MulAut ↥T.range) a : spinGroup (quadMinus 4 F b c)) =
            ν w * (a : spinGroup (quadMinus 4 F b c)) * (ν w)⁻¹) ∧
        ∀ i : Fin 3, ν ((coxeterMatrix D.isFiniteType).simple i) = minusWeyl 4 hirr i := by
  dsimp only
  let e := peRhoMEquiv (by decide : 4 ≤ 4) hirr
  let T := e.symm.toMonoidHom.comp (omMinusTorus b c hζ (m := 3))
  have hmatT (u : Fin 3 → Multiplicative (ZMod p)) :
      spinMatrix (quadMinus 4 F b c) (T u) = omMinusTorusGL hζ u :=
    congrArg (fun A : StatedOmega (StatedQuadMinus 4 F b c) =>
      (A : GL (Fin 3 ⊕ Fin 3 ⊕ Fin 2) F)) (e.apply_symm_apply (omMinusTorus b c hζ u))
  exact exists_weylLift_automizer_spinMinus_of_torusMatrix hirr hp hp2 hζ hζo T hmatT

theorem exists_weyl_chart_of_omegaMinus_torusMatrix
    {F G : Type} [Field F] [Finite F] [CharP F 2] [Group G] [Finite G] {b c : F}
    (hirr : ∀ s : F, s ^ 2 + b * s + c ≠ 0) {p : ℕ} {ζ : Fˣ}
    (hp : p.Prime) (hp2 : p ≠ 2) (hζ : ζ ^ p = 1) (hζo : orderOf ζ = p)
    (T : (Fin 3 → Multiplicative (ZMod p)) →* spinGroup (quadMinus 4 F b c))
    (hmatT : ∀ u, spinMatrix (quadMinus 4 F b c) (T u) = omMinusTorusGL hζ u)
    {Bs X : Subgroup G} (ψ : spinGroup (quadMinus 4 F b c) →* G)
    (hker : ψ.ker ≤ Subgroup.center _) (hrange : ψ.range = X) (hBs : IsElemAbelian p Bs)
    (v : Bs →* (Fin 3 → Multiplicative (ZMod p))) (hv : Function.Surjective v)
    (hact : ∀ (a : Bs) (u : spinGroup (quadMinus 4 F b c)),
      (a : G)⁻¹ * ψ u * (a : G) = ψ (T (v a) * u * (T (v a))⁻¹))
    (hT : T.range.map ψ = Bs ⊓ X) :
    let D := minusDatum 4 hirr
    ∃ ν : GGWeyl D →* spinGroup (quadMinus 4 F b c), GGWeylLift D ν ∧
      ∃ ε : GGWeyl D ≃* ↥(ggAutomizer X Bs),
        (∀ (w : GGWeyl D) (b : Bs), ((ε w : MulAut ↥Bs) b : G) =
          ψ (ν w) * (b : G) * (ψ (ν w))⁻¹) ∧
        ∀ i : Fin 3, GGIsReflection p (ε ((coxeterMatrix D.isFiniteType).simple i) : MulAut ↥Bs) := by
  dsimp only
  have : NeZero p := ⟨hp.ne_zero⟩
  let M := coxeterMatrix (isFiniteType_cartanB 3)
  let U : Type := spinGroup (quadMinus 4 F b c)
  change ∃ ν : M.Group →* U, GGWeylLift (minusDatum 4 hirr) ν ∧
    ∃ ε : M.Group ≃* ↥(ggAutomizer X Bs),
      (∀ (w : M.Group) (a : Bs), ((ε w : MulAut ↥Bs) a : G) =
        ψ (ν w) * (a : G) * (ψ (ν w))⁻¹) ∧
      ∀ i : Fin 3, GGIsReflection p (ε (M.simple i) : MulAut ↥Bs)
  have hψ : Function.Injective ψ := by
    rw [← MonoidHom.ker_eq_bot_iff ψ, eq_bot_iff]
    exact hker.trans (CFSG.RankThree.PartOne.CTP.center_spinGroup_quadMinus_eq_bot
      (by decide : 4 ≤ 4) hirr).le
  have hTin : Function.Injective T := by
    intro u u' huu'
    apply omMinusTorusGL_injective hζ hζo
    simpa only [hmatT] using congrArg (spinMatrix (quadMinus 4 F b c)) huu'
  have hsplit := bstar_split_of_torus_action hBs.1 ψ hrange T v hact hT.le
  obtain ⟨ν, hν, εN, hεN, hνs⟩ :
      ∃ ν : M.Group →* U, GGWeylLift (minusDatum 4 hirr) ν ∧
        ∃ εN : M.Group ≃* ↥(ggAutomizer (⊤ : Subgroup U) T.range),
          (∀ (w : M.Group) (a : T.range), ((εN w : MulAut ↥T.range) a : U) =
            ν w * (a : U) * (ν w)⁻¹) ∧
          ∀ i : Fin 3, ν (M.simple i) = minusWeyl 4 hirr i :=
    exists_weylLift_automizer_spinMinus_of_torusMatrix hirr hp hp2 hζ hζo T hmatT
  obtain ⟨ε, hε⟩ := exists_markedWeyl_bstar_of_split
    (M := coxeterMatrix (isFiniteType_cartanB 3)) T.range Bs X ψ hψ hrange hT hsplit ν εN hεN
  have hconj (i : Fin 3) (u : Fin 3 → Multiplicative (ZMod p)) :
      ν (M.simple i) * T u *
          (ν (M.simple i))⁻¹ = T (SpJoin.spReflPerm 3 p i u) := by
    rw [hνs i]
    exact minusWeyl_conj_of_torusMatrix hirr hζ T hmatT i u
  refine ⟨ν, hν, ε, hε, fun i => ⟨?_, ?_⟩⟩
  · have hsq : (M.simple i) ^ 2 = 1 := by
      rw [← CoxeterMatrix.toCoxeterSystem_simple]
      exact CoxeterSystem.simple_sq _ i
    rw [← Subgroup.coe_pow, ← map_pow, hsq, map_one, Subgroup.coe_one]
  · obtain ⟨χ, hχsurj, hχ⟩ := exists_surjective_fixedHom_spReflPerm hp hp2 i
    let β := χ.comp v
    have hβsurj : Function.Surjective β := hχsurj.comp hv
    have hfix (b : Bs) : (ε (M.simple i) : MulAut ↥Bs) b = b ↔
        b ∈ β.ker := by
      rw [MonoidHom.mem_ker, Subtype.ext_iff, hε]
      change ψ (ν (M.simple i)) * (b : G) *
          (ψ (ν (M.simple i)))⁻¹ = (b : G) ↔ χ (v b) = 1
      rw [conj_eq_self_iff_of_innerAction ψ hψ
        (hact b (ν (M.simple i))), hconj, hTin.eq_iff, hχ]
    have hcardfix : Nat.card {b : Bs // (ε (M.simple i) : MulAut ↥Bs) b = b} =
        Nat.card β.ker := Nat.card_congr (Equiv.subtypeEquivRight hfix)
    have hcardβ : Nat.card β.range = p := by
      rw [MonoidHom.range_eq_top.mpr hβsurj]
      simp
    rw [hcardfix]
    calc
      Nat.card β.ker * p = Nat.card β.ker * Nat.card β.range :=
        congrArg (fun n : ℕ => Nat.card β.ker * n) hcardβ.symm
      _ = Nat.card Bs := Subgroup.card_ker_mul_card_range β


end CFSG.StandardType
