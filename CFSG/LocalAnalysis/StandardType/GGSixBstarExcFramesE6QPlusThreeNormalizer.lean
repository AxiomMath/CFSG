module

public import CFSG.LocalAnalysis.StandardType.GGSixBstarExcFramesE6QPlusThreeDiag
public import CFSG.HardMathSupport.Timmesfeld.CrossChar.SmallQThreeE6FourCore
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
public import CFSG.RankThree.PartOne.KD4T.Certs
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

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.RankThree.Lattice
  CFSG.RankThree.PartOne.KE6 CFSG.HardMathSupport.Curtis.NaturalModuleCensus.ExcCross
  CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley

namespace CFSG.StandardType.ExcFrames.E6QPlusThree

section FrameFamily

open CFSG.Assembly CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LieType.Steinberg.Exceptional CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley CFSG.RankThree.CentralCover
  CFSG.HardMathSupport.Timmesfeld.CrossChar.SmallQ3 CFSG.HardMathSupport.Timmesfeld.Torality
  CFSG.HardMathSupport.Timmesfeld.SporadicBalance.Co1T
  CFSG.GH74.GLS.Stage2.Bender.Thm1 CFSG.StandardType.NoOffE6Three

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

section Certs

variable {L : Type} [Field L]

theorem mem_torusGroup_of_commute_e6ThreeDiag
    {ζ : Lˣ} (hζo : orderOf ζ = 3) (hζ : ζ ^ 3 = 1)
    {z : ModGL .E6 L} (hzC : z ∈ adjointGroup .E6 L)
    (hz : ∀ s, z * e6ThreeDiag ζ hζ s = e6ThreeDiag ζ hζ s * z) :
    z ∈ torusGroup .E6 L := by
  let a : (Fin Tag.F4.rank → ZMod 3) → Fin Tag.E6.rank → Lˣ :=
    fun s => TableBExc.E6Three.zetaVec ζ hζ (twE6ThreeFrame s)
  have hzcent : z ∈ CFSG.HardMathSupport.Timmesfeld.Torality.familyCentralizer Tag.E6 L a := by
    rw [CFSG.HardMathSupport.Timmesfeld.Torality.mem_familyCentralizer]
    refine ⟨hzC, fun s => ?_⟩
    have h := hz (Multiplicative.ofAdd s)
    rw [e6ThreeDiag_apply] at h
    dsimp only [a]
    rw [← h]
    group
  obtain ⟨w, hw, m, hm, hzm⟩ :=
    CFSG.HardMathSupport.Timmesfeld.Torality.familyCentralizer_le_mul Tag.E6 L a hzcent
  have hw1 : w = 1 := frame_familyStabilizer_eq_one (K := L) hζo hζ hw
  have hmT : m ∈ torusGroup Tag.E6 L := by
    have hm' : m ∈ CFSG.HardMathSupport.Timmesfeld.Torality.familyGroup (K := L) a := hm
    rw [CFSG.HardMathSupport.Timmesfeld.Torality.familyGroup,
      frame_familyKernel_eq_empty (K := L) hζo hζ] at hm'
    have hbot : rootSpan Tag.E6 L (∅ : Set (Fin Tag.E6.rank → ℤ)) = ⊥ := by
      simp [rootSpan]
    rwa [hbot, sup_bot_eq] at hm'
  rw [hzm, hw1, canonicalRep_one, mul_one]
  exact hmT

theorem mem_monomialSubgroup_of_conj_e6ThreeDiag
    {ζ : Lˣ} (hζo : orderOf ζ = 3)
    (hζ : ζ ^ 3 = 1) {z : ModGL .E6 L} (hzC : z ∈ adjointGroup .E6 L)
    (hz : ∀ s, z * e6ThreeDiag ζ hζ s * z⁻¹ ∈ (e6ThreeDiag ζ hζ).range) :
    z ∈ monomialSubgroup .E6 L := by
  let a : (Fin Tag.F4.rank → ZMod 3) → Fin Tag.E6.rank → Lˣ :=
    fun s => TableBExc.E6Three.zetaVec ζ hζ (twE6ThreeFrame s)
  let V : Set (ModGL .E6 L) := Set.range (e6ThreeDiag ζ hζ)
  have hVD : ∀ x ∈ V, ∃ b : Fin Tag.E6.rank → Lˣ, x = rootDiagUnit .E6 b := by
    rintro x ⟨s, rfl⟩
    refine ⟨a (Multiplicative.toAdd s), ?_⟩
    simpa using e6ThreeDiag_apply (L := L) ζ hζ (Multiplicative.toAdd s)
  have hgV : ∀ x ∈ V, z * x * z⁻¹ ∈ V := by
    rintro x ⟨s, rfl⟩
    simpa [V] using hz s
  obtain ⟨w, hwconj⟩ :=
    CFSG.StandardType.NoOffE6Three.exists_conj_eq_canonicalRep_of_mem_normalizer_rootDiag
      (τ := Tag.E6) (k := L) hVD hzC hgV
  let n : ModGL .E6 L := canonicalRep (coxeterSystem Tag.E6) L w
  let y' : ModGL .E6 L := n⁻¹ * z
  have hy'C : y' ∈ adjointGroup .E6 L :=
    mul_mem (inv_mem (canonicalRep_mem_adjointGroup (coxeterSystem Tag.E6) L w)) hzC
  have hy'cent : ∀ s, y' * e6ThreeDiag ζ hζ s = e6ThreeDiag ζ hζ s * y' := by
    intro s
    let e := e6ThreeDiag ζ hζ s
    have hmem : e ∈ V := ⟨s, rfl⟩
    have h := hwconj e hmem
    have h2 : n⁻¹ * z * e * (n⁻¹ * z)⁻¹ = e := by
      rw [show (n⁻¹ * z)⁻¹ = z⁻¹ * n by group]
      calc
        n⁻¹ * z * e * (z⁻¹ * n) = n⁻¹ * (z * e * z⁻¹) * n := by group
        _ = n⁻¹ * (n * e * n⁻¹) * n := by rw [h]
        _ = e := by group
    change n⁻¹ * z * e6ThreeDiag ζ hζ s = e6ThreeDiag ζ hζ s * (n⁻¹ * z)
    calc
      n⁻¹ * z * e6ThreeDiag ζ hζ s
          = (n⁻¹ * z * e6ThreeDiag ζ hζ s * (n⁻¹ * z)⁻¹) * (n⁻¹ * z) := by group
      _ = e6ThreeDiag ζ hζ s * (n⁻¹ * z) := by rw [h2]
  have hy'T : y' ∈ torusGroup .E6 L :=
    mem_torusGroup_of_commute_e6ThreeDiag hζo hζ hy'C hy'cent
  have hz_eq : z = n * y' := by
    rw [show y' = n⁻¹ * z from rfl]
    group
  rw [hz_eq]
  exact mul_mem (canonicalRep_mem_monomialSubgroup L w)
    (torusGroup_le_monomialSubgroup hy'T)

end Certs

end CFSG.StandardType.ExcFrames.E6QPlusThree
