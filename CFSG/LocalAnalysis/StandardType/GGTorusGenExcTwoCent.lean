module

public import CFSG.LocalAnalysis.StandardType.GGTorusGenExcTwoBase

import CFSG.HardMathSupport.Timmesfeld.CrossChar.ExcInnerTwE7Model
import CFSG.HardMathSupport.Timmesfeld.CrossChar.ExcInnerTwE8Model
import CFSG.HardMathSupport.Timmesfeld.CrossChar.ExcInnerTwTorus
import CFSG.HardMathSupport.Timmesfeld.Torality.FamilyBruhat
import CFSG.LieType.Chevalley.Canonical
import CFSG.LieType.Chevalley.CoordinateFieldBaseChange
import CFSG.LieType.Chevalley.GraphFixedF4GroupRestriction
import CFSG.LieType.Steinberg.Adjoint.Datum
import CFSG.LieType.Steinberg.Adjoint.Pairs
import CFSG.LocalAnalysis.StandardType.GGSixBstarE8FiveFrameCentralizer
import CFSG.LocalAnalysis.StandardType.GGSixBstarExcFramesCore
import CFSG.LocalAnalysis.StandardType.GGSixBstarNoOffenderExcWeyl
import CFSG.LocalAnalysis.StandardType.GGTableBExcThreeAct
import CFSG.RankThree.CentralCover.SteinbergBNLinearTorus
import CFSG.RankThree.PartOne.KE.CTLang
public import CFSG.Quasithin.Vol2.KGFactC31RuRef

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly TableB CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley

open CFSG.HardMathSupport.Timmesfeld.CrossChar CFSG.HardMathSupport.Timmesfeld.Torality
  CFSG.LieType.Steinberg.Adjoint CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  CFSG.RankThree.CentralCover CFSG.RankThree.PartOne.KE CFSG.StandardType.ExcFrames
  CFSG.StandardType.NoOffE8Five CFSG.StandardType.NoOffExc

namespace ExcTwoGen

private theorem rootChar_zetaVec_frameCoord_single
    {τ : Tag} {L : Type} [Field L] {p : ℕ} [NeZero p]
    {ζ : Lˣ} (hζ : ζ ^ p = 1) (i : Fin τ.rank) (γ : Fin τ.rank → ℤ) :
    rootChar (TableBExc.E6Three.zetaVec ζ hζ
      (frameCoord τ p (Pi.single i 1))) γ =
      zmodPowHom ζ hζ (.ofAdd (frameCoord τ p
        (TableBExc.redMod τ p γ) i)) := by
  rw [NoOffE8Five.rootChar_zetaVec]
  congr 1
  have h1 : (∑ j, ((γ j : ZMod p) *
        frameCoord τ p (Pi.single i 1) j))
      = ∑ j, ((γ j : ZMod p) * ((τ.symmetrizedCartan j i : ℤ) : ZMod p)) := by
    refine Finset.sum_congr rfl fun j _ => ?_
    congr 1
    rw [frameCoord]
    rw [Finset.sum_eq_single i]
    · simp
    · intro k _ hk
      rw [Pi.single_eq_of_ne hk, mul_zero]
    · intro h
      exact absurd (Finset.mem_univ i) h
  have h2 : (∑ j, ((γ j : ZMod p) *
        ((τ.symmetrizedCartan j i : ℤ) : ZMod p)))
      = frameCoord τ p (TableBExc.redMod τ p γ) i := by
    rw [frameCoord]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [TableBExc.redMod, symmetrizedCartan_symm τ j i]
    ring
  rw [h1, h2]

private theorem familyKernel_frameCoord_eq_empty
    {τ : Tag} {L : Type} [Field L]
    {p : ℕ} [Fact p.Prime]
    [NeZero p] (hdet : IsUnit ((τ.symmetrizedCartan.det : ℤ) : ZMod p)) {ζ : Lˣ}
    (hζo : orderOf ζ = p) (hζ : ζ ^ p = 1) :
    familyKernel (fun i : Fin τ.rank => TableBExc.E6Three.zetaVec ζ hζ
      (frameCoord τ p (Pi.single i 1))) = ∅ := by
  refine Set.eq_empty_iff_forall_notMem.2 fun γ hγ => ?_
  have hzero : ∀ i, frameCoord τ p (TableBExc.redMod τ p γ) i = 0 := by
    intro i
    have h1 : rootChar (TableBExc.E6Three.zetaVec ζ hζ
        (frameCoord τ p (Pi.single i 1))) γ = 1 := hγ.2 i
    rw [rootChar_zetaVec_frameCoord_single hζ i γ] at h1
    have h2 : (Multiplicative.ofAdd (frameCoord τ p
        (TableBExc.redMod τ p γ) i) : Multiplicative (ZMod p)) = 1 :=
      zmodPowHom_injective hζo hζ (h1.trans (map_one (zmodPowHom ζ hζ)).symm)
    exact Multiplicative.ofAdd.injective (by simpa using h2)
  have hfc : frameCoord τ p (TableBExc.redMod τ p γ) = 0 := funext hzero
  have hred : TableBExc.redMod τ p γ = 0 :=
    frameCoord_injective hdet (by rw [hfc, frameCoord_zero])
  have hdvd : ∀ j, (p : ℤ) ∣ γ j := fun j =>
    (ZMod.intCast_zmod_eq_zero_iff_dvd (γ j) p).mp (by
      simpa [TableBExc.redMod] using congrFun hred j)
  let γ' : Fin τ.rank → ℤ := fun j => γ j / (p : ℤ)
  have hgamma : γ = p • γ' := by
    funext j
    rw [Pi.smul_apply, nsmul_eq_mul]
    exact (Int.mul_ediv_cancel' (hdvd j)).symm
  have hroot : IsRoot τ (p • γ') := by rw [← hgamma]; exact hγ.1
  exact (Fact.out : p.Prime).ne_one (eq_one_of_isRoot_nsmul (τ := τ) hroot)

private theorem familyStabilizer_frameCoord_eq_one
    {τ : Tag} {L : Type} [Field L] {p : ℕ} [Fact p.Prime]
    [NeZero p] (hp2 : p ≠ 2) (hdet : IsUnit ((τ.symmetrizedCartan.det : ℤ) : ZMod p))
    {ζ : Lˣ} (hζo : orderOf ζ = p) (hζ : ζ ^ p = 1) {w : WeylGroup τ}
    (hw : w ∈ familyStabilizer (fun i : Fin τ.rank => TableBExc.E6Three.zetaVec ζ hζ
      (frameCoord τ p (Pi.single i 1)))) : w = 1 := by
  refine NoOffExc.eq_one_of_torusAct (p := p) hp2 fun x => ?_
  have hfixv : ∀ i, frameCoord τ p (TableBExc.redMod τ p
      (w • TableBExc.liftMod τ p x)) i =
      frameCoord τ p (TableBExc.redMod τ p
        (TableBExc.liftMod τ p x)) i := by
    intro i
    have h1 := hw i (TableBExc.liftMod τ p x)
    rw [rootChar_zetaVec_frameCoord_single hζ i
        (w • TableBExc.liftMod τ p x),
      rootChar_zetaVec_frameCoord_single hζ i (TableBExc.liftMod τ p x)] at h1
    have h2 := zmodPowHom_injective hζo hζ h1
    exact Multiplicative.ofAdd.injective (by simpa using h2)
  have hred : TableBExc.redMod τ p
      (w • TableBExc.liftMod τ p x) =
      TableBExc.redMod τ p (TableBExc.liftMod τ p x) :=
    frameCoord_injective hdet (funext hfixv)
  rw [TableBExc.torusAct]
  change TableBExc.redMod τ p
    (w • TableBExc.liftMod τ p x) = x
  rw [hred, TableBExc.redMod_liftMod]

theorem mem_torusGroup_of_commute_frameDiag
    {τ : Tag} {L : Type} [Field L] {p : ℕ} [Fact p.Prime] [NeZero p]
    (hp2 : p ≠ 2) (hdet : IsUnit ((τ.symmetrizedCartan.det : ℤ) : ZMod p)) {ζ : Lˣ}
    (hζo : orderOf ζ = p) (hζ : ζ ^ p = 1) {z : ModGL τ L} (hz : z ∈ adjointGroup τ L)
    (hcomm : ∀ s : Fin τ.rank → ZMod p,
      z * ExcFrames.frameDiag ζ hζ s = ExcFrames.frameDiag ζ hζ s * z) :
    z ∈ torusGroup τ L := by
  let a : Fin τ.rank → Fin τ.rank → Lˣ :=
    fun i => TableBExc.E6Three.zetaVec ζ hζ
      (frameCoord τ p (Pi.single i 1))
  have hfam : z ∈ familyCentralizer τ L a := by
    rw [mem_familyCentralizer]
    refine ⟨hz, fun i => ?_⟩
    change rootDiagUnit τ (a i) * z *
      (rootDiagUnit τ (a i))⁻¹ = z
    have hfd : frameDiag (τ := τ) ζ hζ (Pi.single i 1) =
        rootDiagUnit τ (a i) := rfl
    rw [← hfd, ← hcomm]
    group
  obtain ⟨w, hw, m, hm, rfl⟩ := familyCentralizer_le_mul τ L a hfam
  have hker : familyKernel a = ∅ := familyKernel_frameCoord_eq_empty hdet hζo hζ
  have hstab : w = 1 := familyStabilizer_frameCoord_eq_one hp2 hdet hζo hζ hw
  have hmT : m ∈ torusGroup τ L := by
    have hm' : m ∈ torusGroup τ L ⊔
        rootSpan τ L (familyKernel a) := hm
    rw [hker] at hm'
    have hbot : rootSpan τ L
        (∅ : Set (Fin τ.rank → ℤ)) = ⊥ := by simp [rootSpan]
    rwa [hbot, sup_bot_eq] at hm'
  rw [hstab, canonicalRep_one, mul_one]
  exact hmT

private theorem exists_adjoint_commute_frameDiag_of_langFrame_two
    {τ : Tag} {K : Type} [Field K] {E : Subgroup (adjointGroup τ K)}
    {g0 : ModGL τ (AlgebraicClosure K)} {ζ : (AlgebraicClosure K)ˣ} {hζ : ζ ^ 3 = 1}
    {ι₀ : Multiplicative (Fin τ.rank → ZMod 3) →* adjointGroup τ K}
    (hg0C : g0 ∈ adjointGroup τ (AlgebraicClosure K))
    (hbase : ∀ s : Fin τ.rank → ZMod 3,
      baseChangeGL (algebraMap K (AlgebraicClosure K))
          ((ι₀ (Multiplicative.ofAdd s) : adjointGroup τ K) : ModGL τ K) =
        g0 * ExcFrames.frameDiag ζ hζ s * g0⁻¹)
    (hrange : ι₀.range = E) {c : adjointGroup τ K}
    (hc : ∀ e ∈ E, c * e = e * c) :
    ∃ z : ModGL τ (AlgebraicClosure K),
      z = g0⁻¹ * baseChangeGL (algebraMap K (AlgebraicClosure K)) (c : ModGL τ K) * g0 ∧
      z ∈ adjointGroup τ (AlgebraicClosure K) ∧
      ∀ s : Fin τ.rank → ZMod 3,
        z * ExcFrames.frameDiag ζ hζ s = ExcFrames.frameDiag ζ hζ s * z := by
  refine ⟨_, rfl, ?_, ?_⟩
  · exact mul_mem (mul_mem (inv_mem hg0C)
      (baseChangeGL_mem_adjointGroup (algebraMap K (AlgebraicClosure K)) c.2)) hg0C
  · intro s
    have hmem : ι₀ (Multiplicative.ofAdd s) ∈ E := by
      rw [← hrange]
      exact ⟨Multiplicative.ofAdd s, rfl⟩
    have hcE : (c : ModGL τ K) *
        ((ι₀ (Multiplicative.ofAdd s) : adjointGroup τ K) : ModGL τ K) =
        ((ι₀ (Multiplicative.ofAdd s) : adjointGroup τ K) : ModGL τ K) *
          (c : ModGL τ K) :=
      congrArg Subtype.val (hc _ hmem)
    have hbc : baseChangeGL (algebraMap K (AlgebraicClosure K)) (c : ModGL τ K) *
        baseChangeGL (algebraMap K (AlgebraicClosure K))
          ((ι₀ (Multiplicative.ofAdd s) : adjointGroup τ K) : ModGL τ K) =
        baseChangeGL (algebraMap K (AlgebraicClosure K))
          ((ι₀ (Multiplicative.ofAdd s) : adjointGroup τ K) : ModGL τ K) *
          baseChangeGL (algebraMap K (AlgebraicClosure K)) (c : ModGL τ K) := by
      rw [← map_mul, ← map_mul, hcE]
    rw [hbase s] at hbc
    calc g0⁻¹ * baseChangeGL (algebraMap K (AlgebraicClosure K)) (c : ModGL τ K) * g0 *
          ExcFrames.frameDiag ζ hζ s
        = g0⁻¹ * (baseChangeGL (algebraMap K (AlgebraicClosure K)) (c : ModGL τ K) *
            (g0 * ExcFrames.frameDiag ζ hζ s * g0⁻¹)) * g0 := by group
      _ = g0⁻¹ * ((g0 * ExcFrames.frameDiag ζ hζ s * g0⁻¹) *
            baseChangeGL (algebraMap K (AlgebraicClosure K)) (c : ModGL τ K)) * g0 := by
            rw [hbc]
      _ = ExcFrames.frameDiag ζ hζ s *
            (g0⁻¹ * baseChangeGL (algebraMap K (AlgebraicClosure K)) (c : ModGL τ K) * g0) := by
            group

private theorem exists_rootDiagUnit_pow_three_of_langFrame_two
    {τ : Tag} (hτ : τ = .E7 ∨ τ = .E8) {K : Type} [Field K] [Finite K]
    (hK : Nat.card K = 2) {w : WeylGroup τ}
    {Fr : AlgebraicClosure K →+* AlgebraicClosure K} (hFr : ∀ c, Fr c = c ^ Nat.card K)
    {g0 : ModGL τ (AlgebraicClosure K)}
    (hg0 : Units.map (entrywiseHom Fr) g0 =
      g0 * canonicalRep (coxeterSystem τ) (AlgebraicClosure K) w)
    {ζ : (AlgebraicClosure K)ˣ} (hζo : orderOf ζ = 3) (hζ : ζ ^ 3 = 1)
    {ι₀ : Multiplicative (Fin τ.rank → ZMod 3) →* adjointGroup τ K}
    (hbase : ∀ s : Fin τ.rank → ZMod 3,
      baseChangeGL (algebraMap K (AlgebraicClosure K))
          ((ι₀ (Multiplicative.ofAdd s) : adjointGroup τ K) : ModGL τ K) =
        g0 * ExcFrames.frameDiag ζ hζ s * g0⁻¹)
    {c : adjointGroup τ K} {z : ModGL τ (AlgebraicClosure K)}
    (hzdef : z = g0⁻¹ * baseChangeGL (algebraMap K (AlgebraicClosure K))
      (c : ModGL τ K) * g0)
    (hzAdj : z ∈ adjointGroup τ (AlgebraicClosure K))
    (hzcomm : ∀ s : Fin τ.rank → ZMod 3,
      z * ExcFrames.frameDiag ζ hζ s = ExcFrames.frameDiag ζ hζ s * z) :
    ∃ a : Fin τ.rank → (AlgebraicClosure K)ˣ,
      z = rootDiagUnit τ a ∧ ∀ i, a i ^ 3 = 1 := by
  haveI : IsAlgClosed (AlgebraicClosure K) := AlgebraicClosure.isAlgClosed K
  have hzT : z ∈ torusGroup τ (AlgebraicClosure K) :=
    mem_torusGroup_of_commute_frameDiag (p := 3) (by decide)
      (isUnit_det_symmetrizedCartan_three hτ) hζo hζ hzAdj hzcomm
  have hfix : canonicalRep (coxeterSystem τ) (AlgebraicClosure K) w *
      Units.map (entrywiseHom Fr) z *
      (canonicalRep (coxeterSystem τ) (AlgebraicClosure K) w)⁻¹ = z := by
    rw [hzdef]
    exact frob_conj_baseChange_two hFr hg0 (c : ModGL τ K)
  have hzTw : z ∈ twistedTorus
      (canonicalRep (coxeterSystem τ) (AlgebraicClosure K) w) Fr := by
    rw [mem_twistedTorus]
    exact ⟨hzT, hfix⟩
  have hw : ∀ u : Fin τ.rank → ℤ, w • u = -u :=
    smul_eq_neg_of_langFrame_two hτ hK hFr hg0 hζo hζ hbase
  have htorL : ∀ a : Fin τ.rank → (AlgebraicClosure K)ˣ,
      rootDiagUnit τ a ∈ torusGroup τ (AlgebraicClosure K) := by
    rcases hτ with rfl | rfl
    · exact fun a => rootDiagUnit_mem_torusGroup_E7 a
    · exact fun a => rootDiagUnit_mem_torusGroup_E8 a
  obtain ⟨a, hza, ha⟩ := (mem_twistedTorus_of_neg htorL hw hFr).1 hzTw
  refine ⟨a, hza, fun i => ?_⟩
  have h := ha i
  rw [hK] at h
  simpa using h

theorem mem_of_commute_of_langFrame_two
    {τ : Tag} (hτ : τ = .E7 ∨ τ = .E8) {K : Type} [Field K]
    [Finite K] (hK : Nat.card K = 2) {E : Subgroup (adjointGroup τ K)}
    (hSC : ∀ g : adjointGroup τ K, (∀ e ∈ E, g * e = e * g) → g ^ 3 = 1 → g ∈ E)
    (hF : Irred937.LangFrameData τ 3 K E) {c : adjointGroup τ K}
    (hc : ∀ e ∈ E, c * e = e * c) : c ∈ E := by
  obtain ⟨w, Fr, g0, ζ, hζ, ι₀, hFr, hg0C, hg0, _, hζo, _, hrange, hbase⟩ := hF
  obtain ⟨z, hzdef, hzAdj, hzcomm⟩ :=
    exists_adjoint_commute_frameDiag_of_langFrame_two hg0C hbase hrange hc
  obtain ⟨a, hza, ha3⟩ :=
    exists_rootDiagUnit_pow_three_of_langFrame_two hτ hK hFr hg0 hζo hζ hbase
      hzdef hzAdj hzcomm
  have hz3 : z ^ 3 = 1 := by
    rw [hza]
    change (rootDiagUnitHom τ (AlgebraicClosure K)) a ^ 3 = 1
    have ha' : a ^ 3 = 1 := funext ha3
    rw [← map_pow, ha', map_one]
  have hv3 : (c : ModGL τ K) ^ 3 = 1 := by
    have hconj : baseChangeGL (algebraMap K (AlgebraicClosure K)) (c : ModGL τ K) =
        g0 * z * g0⁻¹ := by
      rw [hzdef]
      group
    have hbc3 : baseChangeGL (algebraMap K (AlgebraicClosure K))
        ((c : ModGL τ K) ^ 3) = 1 := by
      rw [map_pow, hconj]
      calc (g0 * z * g0⁻¹) ^ 3 = g0 * z ^ 3 * g0⁻¹ :=
            conj_pow (a := g0) (b := z) (i := 3)
        _ = 1 := by rw [hz3]; group
    exact baseChangeGL_injective (algebraMap K (AlgebraicClosure K))
      (by simpa using hbc3)
  have hc3 : c ^ 3 = 1 := by
    apply Subtype.ext
    change (c : ModGL τ K) ^ 3 = ((1 : adjointGroup τ K) : ModGL τ K)
    rw [hv3]
    rfl
  exact hSC c hc hc3

end ExcTwoGen

end CFSG.StandardType
