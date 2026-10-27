module

public import CFSG.HardMathSupport.Timmesfeld.CrossChar.SmallQThreeE6FourCore
public import CFSG.LocalAnalysis.StandardType.GGSixBstarExcFramesTwE6ThreeTorus
public import CFSG.LocalAnalysis.StandardType.GGSixBstarE6ThreeWeylDiagGen
public import CFSG.GH74.GLS.Stage2.Bender.Thm1.P67D4TorusCent
public import CFSG.HardMathSupport.Timmesfeld.CrossChar.ExcInnerResiduals
public import CFSG.HardMathSupport.Timmesfeld.CrossChar.ExcInnerTwE6
public import CFSG.HardMathSupport.Timmesfeld.CrossChar.ExcInnerTwF4
public import CFSG.HardMathSupport.Timmesfeld.CrossChar.Reduction
public import CFSG.LieType.Chevalley.EvenTrialityOuterInvolutions
public import CFSG.LieType.Chevalley.OddTrialityCosetInvolutions
public import CFSG.LieType.SeitzGeneration.ExtSeitzReeF4Cyclic
public import CFSG.LocalAnalysis.ComponentClassification.AutL2FactsCentModel
public import CFSG.LocalAnalysis.ComponentClassification.AutL2FactsFieldAut
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueUStatement
public import CFSG.LocalAnalysis.ComponentClassification.GSLitType
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCorrCentralSylowMaximality
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedGSAContainedSource
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedLayerOddCoreUnbalancingTriple
public import CFSG.LocalAnalysis.QuasithinUnique.SQTK.TypeB2
public import CFSG.LocalAnalysis.QuasithinUnique.SQTK.Unitary
public import CFSG.RankThree.CentralLiftSO.SplitTorusWeyl
public import CFSG.RankThree.Chevalley.SteinbergBTTwistedCosetDescent
public import CFSG.RankThree.PartOne.BRANCH.RankRee
public import CFSG.RankThree.PartOne.CTP.StrongPBridgeRest
public import CFSG.RankThree.PartOne.KC.LinearCommutatorOdd
public import CFSG.RankThree.PartOne.KC.LinearDegreeFive
public import CFSG.RankThree.PartOne.KC.OrthogonalD4WitnessEven
public import CFSG.RankThree.PartOne.KC.OrthogonalD4WitnessOdd
public import CFSG.RankThree.PartOne.KC.UnitaryHigherCrossPrimeTorus
public import CFSG.RankThree.PartOne.KC.UnitaryPlaneEndpoints
public import CFSG.RankThree.PartOne.N143.Weyl613Defs
public import CFSG.RankThree.PartOne.N143X.KF64WSimple
public import CFSG.RankThree.PartOne.S11d.OutExceptional
public import CFSG.RankThree.PartOne.S11d.OutLinear
public import CFSG.RankThree.PartTwo.KFacts.KS14SzLie
public import CFSG.RankThree.PartTwo.Sec4.Census.Interface
public import CFSG.SignalizerFunctorTheorem.Nonsolvable.SolComponent
public import Certificates.Certificate1
public import Certificates.Certificate2

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LieType.Steinberg.Exceptional CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley CFSG.RankThree.CentralCover
  CFSG.HardMathSupport.Timmesfeld.CrossChar.SmallQ3 CFSG.HardMathSupport.Timmesfeld.Torality
  CFSG.HardMathSupport.Timmesfeld.SporadicBalance.Co1T
  CFSG.GH74.GLS.Stage2.Bender.Thm1 CFSG.StandardType.NoOffE6Three

namespace ExcFrames

section FrameFamily

private def frameDecode (k : Fin 81) : Fin Tag.F4.rank → ZMod 3 :=
  fun i => ((k.val / 3 ^ i.val) % 3 : ℕ)

private noncomputable abbrev frameKB : List (List ℕ) :=
  List.ofFn fun k : Fin 81 => vecList (twE6ThreeFrame (frameDecode k))

private theorem frameKB_length : frameKB.length = 81 := by
  simp [frameKB]

private theorem frameDecode_surjective : Function.Surjective frameDecode := by
  decide +kernel

private noncomputable def frameIdx : Fin frameKB.length ≃ Fin 81 := finCongr frameKB_length

private theorem frame_famOK0W :
    Native.famOK0W (Native.gramL .E6) (Native.rootsN .E6) (Native.simpleL .E6)
      ((Native.simpleL .E6).map fun e => Native.formB (Native.gramL .E6) e e) frameKB = true := by
  decide +kernel

private theorem frameKB_length_each : ∀ b ∈ frameKB, b.length = Tag.E6.rank := by
  intro b hb
  simp only [frameKB, List.mem_ofFn] at hb
  obtain ⟨k, rfl⟩ := hb
  simp [vecList_length]

private theorem frameKB_lt : ∀ b ∈ frameKB, ∀ x ∈ b, x < 3 := by
  intro b hb x hx
  simp only [frameKB, List.mem_ofFn] at hb
  obtain ⟨k, rfl⟩ := hb
  simp only [vecList, List.mem_map, List.mem_finRange] at hx
  obtain ⟨i, -, rfl⟩ := hx
  exact ZMod.val_lt _

private theorem famV_frameKB {K : Type} [Field K] {ζ : Kˣ} (hζ : ζ ^ 3 = 1)
    (j : Fin frameKB.length) :
    famV (τ := .E6) ζ frameKB j =
      TableBExc.E6Three.zetaVec ζ hζ (twE6ThreeFrame (frameDecode (frameIdx j))) := by
  have hget : frameKB.get j = vecList (twE6ThreeFrame (frameDecode (frameIdx j))) := by
    rw [List.get_ofFn]
    rfl
  funext i
  simp only [famV, torV, TableBExc.E6Three.zetaVec, listVec]
  rw [hget, vecList_getD]
  rw [CFSG.RankThree.CentralCover.zmodPowHom_apply]
  simp [ZMod.val_natCast, ZMod.val_lt]

private theorem familyStabilizer_frame_eq {K : Type} [Field K] {ζ : Kˣ}
    (hζo : orderOf ζ = 3) (hζ : ζ ^ 3 = 1) :
    familyStabilizer (fun s : Fin Tag.F4.rank → ZMod 3 =>
        TableBExc.E6Three.zetaVec ζ hζ (twE6ThreeFrame s)) =
      familyStabilizer (famV (τ := .E6) ζ frameKB) := by
  ext w
  simp only [familyStabilizer, Set.mem_setOf_eq]
  constructor
  · intro h j
    rw [famV_frameKB hζ j]
    exact h _
  · intro h s
    obtain ⟨j, hj⟩ := frameDecode_surjective s
    let j' : Fin frameKB.length := frameIdx.symm j
    have hjj : frameDecode (frameIdx j') = s := by
      rw [show frameIdx j' = j from Equiv.apply_symm_apply _ _]; exact hj
    have h1 := h j'
    rw [famV_frameKB hζ j', hjj] at h1
    exact h1

private theorem familyKernel_frame_eq {K : Type} [Field K] {ζ : Kˣ}
    (hζo : orderOf ζ = 3) (hζ : ζ ^ 3 = 1) :
    familyKernel (fun s : Fin Tag.F4.rank → ZMod 3 =>
        TableBExc.E6Three.zetaVec ζ hζ (twE6ThreeFrame s)) =
      familyKernel (famV (τ := .E6) ζ frameKB) := by
  ext α
  simp only [familyKernel, Set.mem_ofPred_eq]
  constructor
  · rintro ⟨hroot, h⟩
    refine ⟨hroot, fun j => ?_⟩
    rw [famV_frameKB hζ j]
    exact h _
  · rintro ⟨hroot, h⟩
    refine ⟨hroot, fun s => ?_⟩
    obtain ⟨j, hj⟩ := frameDecode_surjective s
    let j' : Fin frameKB.length := frameIdx.symm j
    have hjj : frameDecode (frameIdx j') = s := by
      rw [show frameIdx j' = j from Equiv.apply_symm_apply _ _]; exact hj
    have h1 := h j'
    rw [famV_frameKB hζ j', hjj] at h1
    exact h1

private theorem frame_familyKernel_eq_empty {K : Type} [Field K] {ζ : Kˣ}
    (hζo : orderOf ζ = 3) (hζ : ζ ^ 3 = 1) :
    familyKernel (fun s : Fin Tag.F4.rank → ZMod 3 =>
      TableBExc.E6Three.zetaVec ζ hζ (twE6ThreeFrame s)) = ∅ := by
  rw [familyKernel_frame_eq hζo hζ]
  exact (famData0_of_famOK0W hζo frameKB_length_each frameKB_lt frame_famOK0W).1

private theorem frame_familyStabilizer_eq_one {K : Type} [Field K] {ζ : Kˣ}
    (hζo : orderOf ζ = 3) (hζ : ζ ^ 3 = 1) {w : WeylGroup Tag.E6}
    (hw : w ∈ familyStabilizer (fun s : Fin Tag.F4.rank → ZMod 3 =>
      TableBExc.E6Three.zetaVec ζ hζ (twE6ThreeFrame s))) : w = 1 := by
  rw [familyStabilizer_frame_eq hζo hζ] at hw
  exact (famData0_of_famOK0W hζo frameKB_length_each frameKB_lt frame_famOK0W).2 w hw

end FrameFamily

section Main


theorem graphFixedRootWeylHom_mem_relWeylTwist
    {f : ℕ}
    (x : ↥(graphFixedRootGroup TwistTag.E6 (GaloisField 2 (2 * f)) (frobQ 2 f)))
    (hx : (x : ModGL TwistTag.E6.tag (GaloisField 2 (2 * f))) ∈
      graphFixedRootMonomial TwistTag.E6 (GaloisField 2 (2 * f)) (frobQ 2 f)) :
    graphFixedRootWeylHom TwistTag.E6 (GaloisField 2 (2 * f)) (frobQ 2 f)
      ⟨(x : ModGL TwistTag.E6.tag (GaloisField 2 (2 * f))), hx⟩ ∈
        relWeylTwist TwistTag.E6 :=
  (graphFixedRootWeylHom_range TwistTag.E6 (GaloisField 2 (2 * f)) (frobQ 2 f)).le
    ⟨⟨(x : ModGL TwistTag.E6.tag (GaloisField 2 (2 * f))), hx⟩, rfl⟩

theorem mem_graphFixedRootTorus_of_centralizes_twE6ThreeFrame
    {f : ℕ} (hf : 1 ≤ f) (h3 : ¬ 3 ∣ 2 ^ f + 1)
    {ζ : (GaloisField 2 (2 * f))ˣ} (hζo : orderOf ζ = 3) (hζ : ζ ^ 3 = 1)
    {x : ↥(graphFixedRootGroup TwistTag.E6 (GaloisField 2 (2 * f)) (frobQ 2 f))}
    (hx : ∀ s : Multiplicative (Fin Tag.F4.rank → ZMod 3),
      x * twE6ThreeFrameHom hf h3 ζ hζ s = twE6ThreeFrameHom hf h3 ζ hζ s * x) :
    (x : ModGL TwistTag.E6.tag (GaloisField 2 (2 * f))) ∈
      graphFixedRootTorus TwistTag.E6 (GaloisField 2 (2 * f)) (frobQ 2 f) := by
  let xE : ModGL Tag.E6 (GaloisField 2 (2 * f)) :=
    (x : ModGL TwistTag.E6.tag (GaloisField 2 (2 * f)))
  let a : (Fin Tag.F4.rank → ZMod 3) → Fin Tag.E6.rank →
      (GaloisField 2 (2 * f))ˣ :=
    fun s => TableBExc.E6Three.zetaVec ζ hζ (twE6ThreeFrame s)
  have hxC : xE ∈ adjointGroup Tag.E6 (GaloisField 2 (2 * f)) := by
    have h := ((mem_twistedFixedGroup_iff_twistHom (t := TwistTag.E6)
      (K := GaloisField 2 (2 * f)) (σ := frobQ 2 f)).1
      (graphFixedRootGroup_le TwistTag.E6 (GaloisField 2 (2 * f)) (frobQ 2 f) x.2)).1
    exact h
  have hxcent : xE ∈ familyCentralizer Tag.E6 (GaloisField 2 (2 * f)) a := by
    rw [mem_familyCentralizer]
    refine ⟨hxC, fun s => ?_⟩
    have hι : ((twE6ThreeFrameHom hf h3 ζ hζ (Multiplicative.ofAdd s) :
        ↥(graphFixedRootGroup TwistTag.E6 (GaloisField 2 (2 * f)) (frobQ 2 f))) :
        ModGL TwistTag.E6.tag (GaloisField 2 (2 * f))) =
        rootDiagUnit TwistTag.E6.tag (a s) :=
      twE6ThreeFrameHom_apply hf h3 hζ s
    have hιE : xE * (show ModGL Tag.E6 (GaloisField 2 (2 * f)) from
        (twE6ThreeFrameHom hf h3 ζ hζ (Multiplicative.ofAdd s) :
          ModGL TwistTag.E6.tag (GaloisField 2 (2 * f)))) =
        (show ModGL Tag.E6 (GaloisField 2 (2 * f)) from
          (twE6ThreeFrameHom hf h3 ζ hζ (Multiplicative.ofAdd s) :
            ModGL TwistTag.E6.tag (GaloisField 2 (2 * f)))) * xE := by
      have h := hx (Multiplicative.ofAdd s)
      have h' := congrArg
        (fun z : ↥(graphFixedRootGroup TwistTag.E6 (GaloisField 2 (2 * f)) (frobQ 2 f)) =>
          (z : ModGL TwistTag.E6.tag (GaloisField 2 (2 * f)))) h
      simp only [Subgroup.coe_mul] at h'
      exact h'
    have hιr : (show ModGL Tag.E6 (GaloisField 2 (2 * f)) from
        (twE6ThreeFrameHom hf h3 ζ hζ (Multiplicative.ofAdd s) :
          ModGL TwistTag.E6.tag (GaloisField 2 (2 * f)))) =
        rootDiagUnit Tag.E6 (a s) := hι
    rw [hιr] at hιE
    have h1 : rootDiagUnit Tag.E6 (a s) * xE =
        xE * rootDiagUnit Tag.E6 (a s) := hιE.symm
    rw [h1]
    group
  obtain ⟨w, hw, m, hm, hxm⟩ := familyCentralizer_le_mul Tag.E6
    (GaloisField 2 (2 * f)) a hxcent
  have hw1 : w = 1 := frame_familyStabilizer_eq_one (K := GaloisField 2 (2 * f)) hζo hζ hw
  have hmT : m ∈ torusGroup Tag.E6 (GaloisField 2 (2 * f)) := by
    have hm' : m ∈ familyGroup (K := GaloisField 2 (2 * f)) a := hm
    rw [familyGroup, frame_familyKernel_eq_empty (K := GaloisField 2 (2 * f)) hζo hζ] at hm'
    have hbot : rootSpan Tag.E6 (GaloisField 2 (2 * f))
        (∅ : Set (Fin Tag.E6.rank → ℤ)) = ⊥ := by simp [rootSpan]
    rwa [hbot, sup_bot_eq] at hm'
  have hxT : xE ∈ torusGroup Tag.E6 (GaloisField 2 (2 * f)) := by
    rw [show xE = m * canonicalRep (coxeterSystem Tag.E6)
      (GaloisField 2 (2 * f)) w from hxm, hw1, canonicalRep_one, mul_one]
    exact hmT
  change xE ∈ graphFixedRootTorus TwistTag.E6 (GaloisField 2 (2 * f)) (frobQ 2 f)
  exact Subgroup.mem_inf.2
    ⟨Subgroup.mem_inf.2 ⟨hxT,
      graphFixedRootGroup_le TwistTag.E6 (GaloisField 2 (2 * f)) (frobQ 2 f) x.2⟩, x.2⟩


theorem mem_graphFixedRootMonomial_of_normalizes_twE6ThreeFrame
    {f : ℕ} (hf : 1 ≤ f) (h3 : ¬ 3 ∣ 2 ^ f + 1)
    {ζ : (GaloisField 2 (2 * f))ˣ} (hζo : orderOf ζ = 3) (hζ : ζ ^ 3 = 1)
    {x : ↥(graphFixedRootGroup TwistTag.E6 (GaloisField 2 (2 * f)) (frobQ 2 f))}
    (hx : ∀ s : Multiplicative (Fin Tag.F4.rank → ZMod 3),
      x * twE6ThreeFrameHom hf h3 ζ hζ s * x⁻¹ ∈
        (twE6ThreeFrameHom hf h3 ζ hζ).range) :
    (x : ModGL TwistTag.E6.tag (GaloisField 2 (2 * f))) ∈
      graphFixedRootMonomial TwistTag.E6 (GaloisField 2 (2 * f)) (frobQ 2 f) := by
  let xE : ModGL Tag.E6 (GaloisField 2 (2 * f)) :=
    (x : ModGL TwistTag.E6.tag (GaloisField 2 (2 * f)))
  let a : (Fin Tag.F4.rank → ZMod 3) → Fin Tag.E6.rank →
      (GaloisField 2 (2 * f))ˣ :=
    fun s => TableBExc.E6Three.zetaVec ζ hζ (twE6ThreeFrame s)
  have hxC : xE ∈ adjointGroup Tag.E6 (GaloisField 2 (2 * f)) :=
    ((mem_twistedFixedGroup_iff_twistHom (t := TwistTag.E6)
      (K := GaloisField 2 (2 * f)) (σ := frobQ 2 f)).1
      (graphFixedRootGroup_le TwistTag.E6 (GaloisField 2 (2 * f)) (frobQ 2 f) x.2)).1
  let V : Set (ModGL Tag.E6 (GaloisField 2 (2 * f))) :=
    {y | ∃ s : Multiplicative (Fin Tag.F4.rank → ZMod 3),
      y = (show ModGL Tag.E6 (GaloisField 2 (2 * f)) from
        (twE6ThreeFrameHom hf h3 ζ hζ s :
          ModGL TwistTag.E6.tag (GaloisField 2 (2 * f))))}
  have hVD : ∀ y ∈ V, ∃ b : Fin Tag.E6.rank → (GaloisField 2 (2 * f))ˣ,
      y = rootDiagUnit Tag.E6 b := by
    rintro y ⟨s, rfl⟩
    refine ⟨a (Multiplicative.toAdd s), ?_⟩
    rw [show (show ModGL Tag.E6 (GaloisField 2 (2 * f)) from
        (twE6ThreeFrameHom hf h3 ζ hζ s :
          ModGL TwistTag.E6.tag (GaloisField 2 (2 * f)))) = rootDiagUnit Tag.E6 (a _) from
      twE6ThreeFrameHom_apply hf h3 hζ (Multiplicative.toAdd s)]
  have hgV : ∀ y ∈ V, xE * y * xE⁻¹ ∈ V := by
    rintro y ⟨s, rfl⟩
    obtain ⟨t, ht⟩ := hx s
    refine ⟨t, ?_⟩
    have h' := congrArg
      (fun z : ↥(graphFixedRootGroup TwistTag.E6 (GaloisField 2 (2 * f)) (frobQ 2 f)) =>
        (z : ModGL TwistTag.E6.tag (GaloisField 2 (2 * f)))) ht
    simp only [Subgroup.coe_mul, Subgroup.coe_inv] at h'
    show xE * (show ModGL Tag.E6 (GaloisField 2 (2 * f)) from
        (twE6ThreeFrameHom hf h3 ζ hζ s :
          ModGL TwistTag.E6.tag (GaloisField 2 (2 * f)))) * xE⁻¹ =
      (show ModGL Tag.E6 (GaloisField 2 (2 * f)) from
        (twE6ThreeFrameHom hf h3 ζ hζ t :
          ModGL TwistTag.E6.tag (GaloisField 2 (2 * f))))
    exact h'.symm
  obtain ⟨w, hwconj⟩ := exists_conj_eq_canonicalRep_of_mem_normalizer_rootDiag
    (τ := Tag.E6) (k := GaloisField 2 (2 * f)) hVD hxC hgV
  let n : ModGL Tag.E6 (GaloisField 2 (2 * f)) :=
    canonicalRep (coxeterSystem Tag.E6) (GaloisField 2 (2 * f)) w
  let y' : ModGL Tag.E6 (GaloisField 2 (2 * f)) := n⁻¹ * xE
  have hy'C : y' ∈ adjointGroup Tag.E6 (GaloisField 2 (2 * f)) :=
    mul_mem (inv_mem (canonicalRep_mem_adjointGroup (coxeterSystem Tag.E6)
      (GaloisField 2 (2 * f)) w)) hxC
  have hy'cent : y' ∈ familyCentralizer Tag.E6 (GaloisField 2 (2 * f)) a := by
    rw [mem_familyCentralizer]
    refine ⟨hy'C, fun s => ?_⟩
    have hιE : (show ModGL Tag.E6 (GaloisField 2 (2 * f)) from
        (twE6ThreeFrameHom hf h3 ζ hζ (Multiplicative.ofAdd s) :
          ModGL TwistTag.E6.tag (GaloisField 2 (2 * f)))) = rootDiagUnit Tag.E6 (a s) :=
      twE6ThreeFrameHom_apply hf h3 hζ s
    have hmem : (show ModGL Tag.E6 (GaloisField 2 (2 * f)) from
        (twE6ThreeFrameHom hf h3 ζ hζ (Multiplicative.ofAdd s) :
          ModGL TwistTag.E6.tag (GaloisField 2 (2 * f)))) ∈ V := ⟨Multiplicative.ofAdd s, rfl⟩
    have hconj := hwconj _ hmem
    rw [hιE] at hconj
    have h2 : xE * rootDiagUnit Tag.E6 (a s) =
        n * rootDiagUnit Tag.E6 (a s) * n⁻¹ * xE := by
      rw [mul_inv_eq_iff_eq_mul] at hconj
      exact hconj
    have hcomm : y' * rootDiagUnit Tag.E6 (a s) =
        rootDiagUnit Tag.E6 (a s) * y' := by
      change n⁻¹ * xE * rootDiagUnit Tag.E6 (a s) =
        rootDiagUnit Tag.E6 (a s) * (n⁻¹ * xE)
      have h3 := congrArg (fun z => n⁻¹ * z) h2
      simpa only [mul_assoc, inv_mul_cancel_left] using h3
    rw [← hcomm]
    group
  obtain ⟨w', hw', m, hm, hy'm⟩ := familyCentralizer_le_mul Tag.E6
    (GaloisField 2 (2 * f)) a hy'cent
  have hw'1 : w' = 1 := frame_familyStabilizer_eq_one (K := GaloisField 2 (2 * f)) hζo hζ hw'
  have hmT : m ∈ torusGroup Tag.E6 (GaloisField 2 (2 * f)) := by
    have hm' : m ∈ familyGroup (K := GaloisField 2 (2 * f)) a := hm
    rw [familyGroup, frame_familyKernel_eq_empty (K := GaloisField 2 (2 * f)) hζo hζ] at hm'
    have hbot : rootSpan Tag.E6 (GaloisField 2 (2 * f))
        (∅ : Set (Fin Tag.E6.rank → ℤ)) = ⊥ := by simp [rootSpan]
    rwa [hbot, sup_bot_eq] at hm'
  have hy'T : y' ∈ torusGroup Tag.E6 (GaloisField 2 (2 * f)) := by
    rw [hy'm, hw'1, canonicalRep_one, mul_one]
    exact hmT
  have hmonoE : xE ∈ monomialSubgroup Tag.E6 (GaloisField 2 (2 * f)) := by
    have hxeq : xE = n * y' := by
      rw [show y' = n⁻¹ * xE from rfl]
      group
    rw [hxeq]
    exact mul_mem (canonicalRep_mem_monomialSubgroup (GaloisField 2 (2 * f)) w)
      (torusGroup_le_monomialSubgroup hy'T)
  have hmonoT : (x : ModGL TwistTag.E6.tag (GaloisField 2 (2 * f))) ∈
      monomialSubgroup TwistTag.E6.tag (GaloisField 2 (2 * f)) := hmonoE
  exact Subgroup.mem_inf.2
    ⟨Subgroup.mem_inf.2 ⟨hmonoT,
      graphFixedRootGroup_le TwistTag.E6 (GaloisField 2 (2 * f)) (frobQ 2 f) x.2⟩, x.2⟩


private theorem canonicalRep_conj_frameDiag_twE6Three {K : Type} [Field K] {ζ : Kˣ}
    (hζ : ζ ^ 3 = 1) (w : WeylGroup TwistTag.E6.tag)
    (hw : w ∈ relWeylTwist TwistTag.E6) (s : Fin Tag.F4.rank → ZMod 3) :
    canonicalRep (coxeterSystem TwistTag.E6.tag) K w *
        frameDiag (τ := TwistTag.E6.tag) ζ hζ (twE6ThreeTheta s) *
        (canonicalRep (coxeterSystem TwistTag.E6.tag) K w)⁻¹ =
      frameDiag (τ := TwistTag.E6.tag) ζ hζ
        (twE6ThreeTheta (TableBExc.torusAct .F4 3
          (foldedWeylEquiv TwistTag.E6 ⟨w, hw⟩) s)) := by
  rw [canonicalRep_conj_frameDiag (τ := TwistTag.E6.tag) ζ hζ w (twE6ThreeTheta s)]
  unfold frameDiag
  congr 1
  congr 1
  change frameCoord Tag.E6 3
      (TableBExc.torusAct Tag.E6 3 w (twE6ThreeTheta s)) =
      twE6ThreeFrame (TableBExc.torusAct .F4 3
        (foldedWeylEquiv TwistTag.E6 ⟨w, hw⟩) s)
  rw [← adAct_frameCoord (τ := Tag.E6) (p := 3) w (twE6ThreeTheta s)]
  rw [show frameCoord Tag.E6 3 (twE6ThreeTheta s) = twE6ThreeFrame s from rfl]
  rw [adAct_twE6ThreeFrame ⟨w, hw⟩]

theorem twE6ThreeFrameHom_conj
    {f : ℕ} (hf : 1 ≤ f) (h3 : ¬ 3 ∣ 2 ^ f + 1)
    {ζ : (GaloisField 2 (2 * f))ˣ} (hζo : orderOf ζ = 3) (hζ : ζ ^ 3 = 1)
    {x : ↥(graphFixedRootGroup TwistTag.E6 (GaloisField 2 (2 * f)) (frobQ 2 f))}
    (hx : (x : ModGL TwistTag.E6.tag (GaloisField 2 (2 * f))) ∈
      graphFixedRootMonomial TwistTag.E6 (GaloisField 2 (2 * f)) (frobQ 2 f))
    (s : Fin Tag.F4.rank → ZMod 3) :
    (x : ModGL TwistTag.E6.tag (GaloisField 2 (2 * f))) *
        (twE6ThreeFrameHom hf h3 ζ hζ (Multiplicative.ofAdd s) :
          ModGL TwistTag.E6.tag (GaloisField 2 (2 * f))) *
        (x : ModGL TwistTag.E6.tag (GaloisField 2 (2 * f)))⁻¹ =
      (twE6ThreeFrameHom hf h3 ζ hζ (Multiplicative.ofAdd
        (TableBExc.torusAct .F4 3
          (foldedWeylEquiv TwistTag.E6
            ⟨graphFixedRootWeylHom TwistTag.E6 (GaloisField 2 (2 * f)) (frobQ 2 f)
              ⟨(x : ModGL TwistTag.E6.tag (GaloisField 2 (2 * f))), hx⟩,
              (graphFixedRootWeylHom_range TwistTag.E6 (GaloisField 2 (2 * f))
                (frobQ 2 f)).le ⟨⟨(x : ModGL TwistTag.E6.tag (GaloisField 2 (2 * f))), hx⟩,
                  rfl⟩⟩) s)) :
        ModGL TwistTag.E6.tag (GaloisField 2 (2 * f))) := by
  let n : ↥(graphFixedRootMonomial TwistTag.E6 (GaloisField 2 (2 * f)) (frobQ 2 f)) :=
    ⟨(x : ModGL TwistTag.E6.tag (GaloisField 2 (2 * f))), hx⟩
  obtain ⟨t, htT, ht_eq⟩ :=
    graphFixedRootMonomial_eq_canonicalRep_mul_torus TwistTag.E6 (frobQ 2 f) n
  let w : WeylGroup TwistTag.E6.tag :=
    graphFixedRootWeylHom TwistTag.E6 (GaloisField 2 (2 * f)) (frobQ 2 f) n
  have hwmem : w ∈ relWeylTwist TwistTag.E6 :=
    (graphFixedRootWeylHom_range TwistTag.E6 (GaloisField 2 (2 * f))
      (frobQ 2 f)).le ⟨n, rfl⟩
  let wbar : WeylGroup Tag.F4 := foldedWeylEquiv TwistTag.E6 ⟨w, hwmem⟩
  let d : ModGL TwistTag.E6.tag (GaloisField 2 (2 * f)) :=
    frameDiag (τ := TwistTag.E6.tag) ζ hζ (twE6ThreeTheta s)
  obtain ⟨b, hb⟩ := exists_rootDiagUnit_eq_of_mem_torusGroup htT
  have hcomm : t * d = d * t := by
    rw [show t = rootDiagUnit TwistTag.E6.tag b from hb]
    exact rootDiagUnit_mul_comm _ _
  have hmul : (canonicalRep (coxeterSystem TwistTag.E6.tag)
        (GaloisField 2 (2 * f)) w * t) * d *
        (canonicalRep (coxeterSystem TwistTag.E6.tag)
          (GaloisField 2 (2 * f)) w * t)⁻¹ =
      canonicalRep (coxeterSystem TwistTag.E6.tag) (GaloisField 2 (2 * f)) w * d *
        (canonicalRep (coxeterSystem TwistTag.E6.tag)
          (GaloisField 2 (2 * f)) w)⁻¹ := by
    calc (canonicalRep (coxeterSystem TwistTag.E6.tag)
          (GaloisField 2 (2 * f)) w * t) * d *
          (canonicalRep (coxeterSystem TwistTag.E6.tag)
            (GaloisField 2 (2 * f)) w * t)⁻¹
        = canonicalRep (coxeterSystem TwistTag.E6.tag) (GaloisField 2 (2 * f)) w *
            (t * d * t⁻¹) *
            (canonicalRep (coxeterSystem TwistTag.E6.tag)
              (GaloisField 2 (2 * f)) w)⁻¹ := by group
      _ = canonicalRep (coxeterSystem TwistTag.E6.tag) (GaloisField 2 (2 * f)) w *
            (d * t * t⁻¹) *
            (canonicalRep (coxeterSystem TwistTag.E6.tag)
              (GaloisField 2 (2 * f)) w)⁻¹ := by rw [hcomm]
      _ = canonicalRep (coxeterSystem TwistTag.E6.tag) (GaloisField 2 (2 * f)) w * d *
            (canonicalRep (coxeterSystem TwistTag.E6.tag)
              (GaloisField 2 (2 * f)) w)⁻¹ := by group
  have hι : (twE6ThreeFrameHom hf h3 ζ hζ (Multiplicative.ofAdd s) :
        ModGL TwistTag.E6.tag (GaloisField 2 (2 * f))) = d := rfl
  have ht_eq' : (x : ModGL TwistTag.E6.tag (GaloisField 2 (2 * f))) =
      canonicalRep (coxeterSystem TwistTag.E6.tag) (GaloisField 2 (2 * f)) w * t := ht_eq
  have hconj := canonicalRep_conj_frameDiag_twE6Three (ζ := ζ) hζ w hwmem s
  conv_lhs =>
    rw [hι]
    rw [ht_eq']
    rw [hmul]
    rw [hconj]
  exact (twE6ThreeFrameHom_apply hf h3 hζ (TableBExc.torusAct .F4 3 wbar s)).symm

end Main

end ExcFrames

end CFSG.StandardType
