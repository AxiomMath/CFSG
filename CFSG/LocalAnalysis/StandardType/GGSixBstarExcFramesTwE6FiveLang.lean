module

public import CFSG.LocalAnalysis.StandardType.GGSixBstarE8FiveFrameCentralizer
public import CFSG.LocalAnalysis.StandardType.GGSixStepTwoToralExcAdj
public import CFSG.HardMathSupport.Timmesfeld.CrossChar.ExcInnerFiveTw
public import CFSG.LocalAnalysis.RankThreeTheoremC.KFacts.WeakClosureThree.LieCrossLin
public import CFSG.Certificates.CentralKernel
public import CFSG.Certificates.CosetTableWalkC
public import CFSG.Certificates.FusionF2
public import CFSG.Certificates.WordSubgroupHom
public import CFSG.HardMathSupport.Timmesfeld.CrossChar.ExcInnerResiduals
public import CFSG.HardMathSupport.Timmesfeld.CrossChar.ExcInnerTwE6
public import CFSG.HardMathSupport.Timmesfeld.CrossChar.Reduction
public import CFSG.LieType.SeitzGeneration.ExtSeitzReeF4Cyclic
public import CFSG.LocalAnalysis.ComponentClassification.AutL2FactsCentModel
public import CFSG.LocalAnalysis.ComponentClassification.AutL2FactsFieldAut
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
public import CFSG.RankThree.PartTwo.KFacts.KS14SzLie
public import CFSG.SignalizerFunctorTheorem.Nonsolvable.SolComponent
public import CFSG.Sporadic.Bridge.Catalogue
public import CFSG.Sporadic.Presentation.Co2Base
public import CFSG.Sporadic.Presentation.Co2Cover
public import CFSG.Sporadic.Presentation.Co2Fusion
public import CFSG.Sporadic.Presentation.Co2FusionInputs
public import CFSG.Sporadic.Presentation.McLExactData
public import CFSG.Sporadic.Presentation.McLExactInputs
public import CFSG.YGroups.DCE.B433Check
public import Certificates.Certificate9124

public section

namespace CFSG.StandardType

open scoped Matrix Pointwise

open CFSG.Assembly CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LieType.SeitzGeneration CFSG.LieType.Steinberg.Adjoint CFSG.RankThree.PartOne.KE
  CFSG.RankThree.Classical2 CFSG.RankThree.Lattice CFSG.LieType.Steinberg.Exceptional CFSG.RankThree.Chevalley
  CFSG.RankThree.CentralCover CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  CFSG.HardMathSupport.Timmesfeld.CrossChar CFSG.HardMathSupport.Timmesfeld.Torality
  CFSG.LocalAnalysis.RankThreeTheoremC.WeakClosureThree

namespace ExcFrames

local instance fiveFact : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
local instance fiveNeZero : NeZero (5 : ℕ) := ⟨by norm_num⟩

section FiveLang


private theorem rootChar_zetaVec_frameCoord_single {L : Type} [Field L] {ζ : Lˣ}
    (hζ : ζ ^ 5 = 1) (i : Fin TwistTag.E6.tag.rank) (γ : Fin TwistTag.E6.tag.rank → ℤ) :
    rootChar (TableBExc.E6Three.zetaVec ζ hζ
      (frameCoord TwistTag.E6.tag 5 (Pi.single i 1))) γ =
      zmodPowHom ζ hζ (.ofAdd (frameCoord TwistTag.E6.tag 5
        (TableBExc.redMod TwistTag.E6.tag 5 γ) i)) := by
  rw [NoOffE8Five.rootChar_zetaVec]
  congr 1
  have h1 : (∑ j, ((γ j : ZMod 5) *
        frameCoord TwistTag.E6.tag 5 (Pi.single i 1) j))
      = ∑ j, ((γ j : ZMod 5) * ((TwistTag.E6.tag.symmetrizedCartan j i : ℤ) : ZMod 5)) := by
    refine Finset.sum_congr rfl fun j _ => ?_
    congr 1
    rw [frameCoord]
    rw [Finset.sum_eq_single i]
    · simp
    · intro k _ hk
      rw [Pi.single_eq_of_ne hk, mul_zero]
    · intro h
      exact absurd (Finset.mem_univ i) h
  have h2 : (∑ j, ((γ j : ZMod 5) *
        ((TwistTag.E6.tag.symmetrizedCartan j i : ℤ) : ZMod 5)))
      = frameCoord TwistTag.E6.tag 5 (TableBExc.redMod TwistTag.E6.tag 5 γ) i := by
    rw [frameCoord]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [TableBExc.redMod, symmetrizedCartan_symm TwistTag.E6.tag j i]
    ring
  rw [h1, h2]

private theorem familyKernel_frameCoord_eq_empty {L : Type} [Field L] {ζ : Lˣ}
    (hζo : orderOf ζ = 5) (hζ : ζ ^ 5 = 1) :
    familyKernel (fun i : Fin TwistTag.E6.tag.rank => TableBExc.E6Three.zetaVec ζ hζ
      (frameCoord TwistTag.E6.tag 5 (Pi.single i 1))) = ∅ := by
  refine Set.eq_empty_iff_forall_notMem.2 fun γ hγ => ?_
  have hzero : ∀ i, frameCoord TwistTag.E6.tag 5
      (TableBExc.redMod TwistTag.E6.tag 5 γ) i = 0 := by
    intro i
    have h1 : rootChar (TableBExc.E6Three.zetaVec ζ hζ
        (frameCoord TwistTag.E6.tag 5 (Pi.single i 1))) γ = 1 := hγ.2 i
    rw [rootChar_zetaVec_frameCoord_single hζ i γ] at h1
    have h2 : (Multiplicative.ofAdd (frameCoord TwistTag.E6.tag 5
        (TableBExc.redMod TwistTag.E6.tag 5 γ) i) : Multiplicative (ZMod 5)) = 1 :=
      zmodPowHom_injective hζo hζ (h1.trans (map_one (zmodPowHom ζ hζ)).symm)
    exact Multiplicative.ofAdd.injective (by simpa using h2)
  have hfc : frameCoord TwistTag.E6.tag 5
      (TableBExc.redMod TwistTag.E6.tag 5 γ) = 0 := funext hzero
  have hdet : IsUnit (((TwistTag.E6.tag).symmetrizedCartan.det : ℤ) : ZMod 5) :=
    CFSG.StandardType.StepTwoToralExc.isUnit_det_symmetrizedCartan_E6 (p := 5) (by norm_num)
  have hred : TableBExc.redMod TwistTag.E6.tag 5 γ = 0 :=
    frameCoord_injective hdet (by rw [hfc, frameCoord_zero])
  have hdvd : ∀ j, (5 : ℤ) ∣ γ j := fun j =>
    (ZMod.intCast_zmod_eq_zero_iff_dvd (γ j) 5).mp (by
      simpa [TableBExc.redMod] using congrFun hred j)
  let γ' : Fin TwistTag.E6.tag.rank → ℤ := fun j => γ j / 5
  have hgamma : γ = 5 • γ' := by
    funext j
    rw [Pi.smul_apply, nsmul_eq_mul]
    norm_num
    exact (Int.mul_ediv_cancel' (hdvd j)).symm
  have hroot : IsRoot TwistTag.E6.tag (5 • γ') := by rw [← hgamma]; exact hγ.1
  have := CFSG.LieType.Steinberg.Adjoint.eq_one_of_isRoot_nsmul
    (τ := TwistTag.E6.tag) hroot
  omega

private theorem familyStabilizer_frameCoord_eq_one {L : Type} [Field L] {ζ : Lˣ}
    (hζo : orderOf ζ = 5) (hζ : ζ ^ 5 = 1) {w : WeylGroup TwistTag.E6.tag}
    (hw : w ∈ familyStabilizer (fun i : Fin TwistTag.E6.tag.rank =>
      TableBExc.E6Three.zetaVec ζ hζ
        (frameCoord TwistTag.E6.tag 5 (Pi.single i 1)))) : w = 1 := by
  have hdet : IsUnit (((TwistTag.E6.tag).symmetrizedCartan.det : ℤ) : ZMod 5) :=
    CFSG.StandardType.StepTwoToralExc.isUnit_det_symmetrizedCartan_E6 (p := 5) (by norm_num)
  refine CFSG.StandardType.NoOffExc.eq_one_of_torusAct (p := 5) (by norm_num) fun x => ?_
  have hfixv : ∀ i, frameCoord TwistTag.E6.tag 5 (TableBExc.redMod TwistTag.E6.tag 5
      (w • TableBExc.liftMod TwistTag.E6.tag 5 x)) i =
      frameCoord TwistTag.E6.tag 5 (TableBExc.redMod TwistTag.E6.tag 5
        (TableBExc.liftMod TwistTag.E6.tag 5 x)) i := by
    intro i
    have h1 := hw i (TableBExc.liftMod TwistTag.E6.tag 5 x)
    rw [rootChar_zetaVec_frameCoord_single hζ i
        (w • TableBExc.liftMod TwistTag.E6.tag 5 x),
      rootChar_zetaVec_frameCoord_single hζ i (TableBExc.liftMod TwistTag.E6.tag 5 x)] at h1
    have h2 := zmodPowHom_injective hζo hζ h1
    exact Multiplicative.ofAdd.injective (by simpa using h2)
  have hred : TableBExc.redMod TwistTag.E6.tag 5
      (w • TableBExc.liftMod TwistTag.E6.tag 5 x) =
      TableBExc.redMod TwistTag.E6.tag 5 (TableBExc.liftMod TwistTag.E6.tag 5 x) :=
    frameCoord_injective hdet (funext hfixv)
  rw [TableBExc.torusAct]
  change TableBExc.redMod TwistTag.E6.tag 5
    (w • TableBExc.liftMod TwistTag.E6.tag 5 x) = x
  rw [hred, TableBExc.redMod_liftMod]

private theorem mem_torusGroup_of_commute_fiveFrameDiag {L : Type} [Field L] {ζ : Lˣ}
    (hζo : orderOf ζ = 5) (hζ : ζ ^ 5 = 1) {z : ModGL TwistTag.E6.tag L}
    (hz : z ∈ adjointGroup TwistTag.E6.tag L)
    (hcomm : ∀ s : Fin TwistTag.E6.tag.rank → ZMod 5,
      z * frameDiag (τ := TwistTag.E6.tag) ζ hζ s =
        frameDiag (τ := TwistTag.E6.tag) ζ hζ s * z) :
    z ∈ torusGroup TwistTag.E6.tag L := by
  let a : Fin TwistTag.E6.tag.rank → Fin TwistTag.E6.tag.rank → Lˣ :=
    fun i => TableBExc.E6Three.zetaVec ζ hζ
      (frameCoord TwistTag.E6.tag 5 (Pi.single i 1))
  have hfam : z ∈ familyCentralizer TwistTag.E6.tag L a := by
    rw [mem_familyCentralizer]
    refine ⟨hz, fun i => ?_⟩
    change rootDiagUnit TwistTag.E6.tag (a i) * z *
      (rootDiagUnit TwistTag.E6.tag (a i))⁻¹ = z
    have hfd : frameDiag (τ := TwistTag.E6.tag) ζ hζ (Pi.single i 1) =
        rootDiagUnit TwistTag.E6.tag (a i) := rfl
    rw [← hfd, ← hcomm]
    group
  obtain ⟨w, hw, m, hm, rfl⟩ := familyCentralizer_le_mul TwistTag.E6.tag L a hfam
  have hker : familyKernel a = ∅ := familyKernel_frameCoord_eq_empty hζo hζ
  have hstab : w = 1 := familyStabilizer_frameCoord_eq_one hζo hζ hw
  have hmT : m ∈ torusGroup TwistTag.E6.tag L := by
    have hm' : m ∈ torusGroup TwistTag.E6.tag L ⊔
        rootSpan TwistTag.E6.tag L (familyKernel a) := hm
    rw [hker] at hm'
    have hbot : rootSpan TwistTag.E6.tag L
        (∅ : Set (Fin TwistTag.E6.tag.rank → ℤ)) = ⊥ := by simp [rootSpan]
    rwa [hbot, sup_bot_eq] at hm'
  rw [hstab, canonicalRep_one, mul_one]
  exact hmT

private theorem frameDiag_mem_twistedTorus_five {L : Type} [Field L] [IsAlgClosed L]
    (Fr : L →+* L) {q : ℕ} (hFr : ∀ c, Fr c = c ^ q) (h5 : 5 ∣ q + 1)
    {ζ : Lˣ} (hζo : orderOf ζ = 5) (hζ : ζ ^ 5 = 1)
    (s : Fin TwistTag.E6.tag.rank → ZMod 5) :
    frameDiag (τ := TwistTag.E6.tag) ζ hζ s ∈
      twistedTorusOf (canonicalRep (coxeterSystem TwistTag.E6.tag) L twE6PhiTwoWeyl)
        (twistHom TwistTag.E6 L Fr) := by
  have htomat : toMat TwistTag.E6.tag.rank twE6TwoMat =
      (-1 : Matrix (Fin TwistTag.E6.tag.rank) (Fin TwistTag.E6.tag.rank) ℤ) := by
    ext i j
    fin_cases i <;> fin_cases j <;> rfl
  have hv : ∀ x : Fin TwistTag.E6.tag.rank → ℤ, twE6PhiTwoWeyl • x =
      (-1 : Matrix (Fin TwistTag.E6.tag.rank) (Fin TwistTag.E6.tag.rank) ℤ) *ᵥ
        permLattice TwistTag.E6.perm x := by
    intro x
    rw [twE6PhiTwoWeyl_smul, htomat, Matrix.neg_mulVec, Matrix.one_mulVec]
  rw [twistedTorus_E6_eq_map (L := L) Fr twE6PhiTwoWeyl
    (-1 : Matrix (Fin TwistTag.E6.tag.rank) (Fin TwistTag.E6.tag.rank) ℤ) hv]
  refine ⟨TableBExc.E6Three.zetaVec ζ hζ (frameCoord TwistTag.E6.tag 5 s), ?_, rfl⟩
  change TableBExc.E6Three.zetaVec ζ hζ (frameCoord TwistTag.E6.tag 5 s) ∈
    fixedCharTuples (-1) Fr
  rw [mem_fixedCharTuples_iff]
  intro u
  have hMu : (-1 : Matrix (Fin TwistTag.E6.tag.rank) (Fin TwistTag.E6.tag.rank) ℤ) *ᵥ u
      = -u := by
    rw [Matrix.neg_mulVec, Matrix.one_mulVec]
  have hroot : rootChar (TableBExc.E6Three.zetaVec ζ hζ
        (frameCoord TwistTag.E6.tag 5 s)) u =
      zmodPowHom ζ hζ (.ofAdd (∑ j, ((u j : ZMod 5) *
        frameCoord TwistTag.E6.tag 5 s j))) :=
    NoOffE8Five.rootChar_zetaVec hζ (frameCoord TwistTag.E6.tag 5 s) u
  have hu5 : (rootChar (TableBExc.E6Three.zetaVec ζ hζ
      (frameCoord TwistTag.E6.tag 5 s)) u) ^ 5 = 1 := by
    rw [hroot, zmodPowHom_apply, ← pow_mul,
      show (∑ j, ((u j : ZMod 5) * frameCoord TwistTag.E6.tag 5 s j)).val * 5 =
        5 * (∑ j, ((u j : ZMod 5) * frameCoord TwistTag.E6.tag 5 s j)).val by omega,
      pow_mul, hζ, one_pow]
  have huq : (rootChar (TableBExc.E6Three.zetaVec ζ hζ
      (frameCoord TwistTag.E6.tag 5 s)) u) ^ q =
      (rootChar (TableBExc.E6Three.zetaVec ζ hζ
        (frameCoord TwistTag.E6.tag 5 s)) u)⁻¹ := by
    obtain ⟨k, hk⟩ := h5
    have hsucc : (rootChar (TableBExc.E6Three.zetaVec ζ hζ
        (frameCoord TwistTag.E6.tag 5 s)) u) ^ (q + 1) = 1 := by
      rw [hk, pow_mul, hu5, one_pow]
    have hmul : (rootChar (TableBExc.E6Three.zetaVec ζ hζ
        (frameCoord TwistTag.E6.tag 5 s)) u) ^ q *
        (rootChar (TableBExc.E6Three.zetaVec ζ hζ
          (frameCoord TwistTag.E6.tag 5 s)) u) = 1 := by
      rw [← pow_succ, hsucc]
    exact eq_inv_of_mul_eq_one_left hmul
  rw [hMu, show -u = (-1 : ℤ) • u by simp, rootChar_zsmul,
    CFSG.RankThree.PartOne.KE.CTTorus.map_units_eq_pow hFr, huq]
  simp

private theorem natAbs_det_neg_one_sub_smul_one (q : ℕ) :
    (((-1 : Matrix (Fin TwistTag.E6.tag.rank) (Fin TwistTag.E6.tag.rank) ℤ) -
      (q : ℤ) • 1).det).natAbs = (q + 1) ^ 6 := by
  have hneg : (-1 : Matrix (Fin TwistTag.E6.tag.rank)
      (Fin TwistTag.E6.tag.rank) ℤ) = (-1 : ℤ) • 1 := by simp
  have hmat : ((-1 : Matrix (Fin TwistTag.E6.tag.rank)
        (Fin TwistTag.E6.tag.rank) ℤ) - (q : ℤ) • 1) =
      (-(q + 1 : ℤ)) • (1 : Matrix (Fin TwistTag.E6.tag.rank)
        (Fin TwistTag.E6.tag.rank) ℤ) := by
    rw [hneg, ← sub_smul]
    congr 1
    ring
  rw [hmat, Matrix.det_smul, Matrix.det_one, mul_one,
    show Fintype.card (Fin TwistTag.E6.tag.rank) = 6 from rfl]
  have h1 : (-(q + 1 : ℤ)) ^ 6 = (((q + 1 : ℕ)) : ℤ) ^ 6 := by
    push_cast
    ring
  rw [h1, Int.natAbs_pow, Int.natAbs_natCast]

theorem not_three_dvd_two_pow_add_one_of_five_dvd {f : ℕ} (hf : 1 ≤ f)
    (h5 : 5 ∣ 2 ^ f + 1) : ¬ 3 ∣ 2 ^ f + 1 := by
  have hord : orderOf (2 : ZMod 5) = 4 := by
    rw [orderOf_eq_iff (by norm_num)]
    refine ⟨by decide, fun m hm hm0 => ?_⟩
    interval_cases m <;> decide
  have h2f : ((2 : ZMod 5) ^ f) = -1 := by
    have h0 : (((2 ^ f + 1 : ℕ)) : ZMod 5) = 0 := (ZMod.natCast_eq_zero_iff _ _).2 h5
    rw [Nat.cast_add, Nat.cast_pow, Nat.cast_ofNat, Nat.cast_one] at h0
    exact eq_neg_of_add_eq_zero_left h0
  have hpow : ((2 : ZMod 5)) ^ (f * 2) = 1 := by
    rw [pow_mul, h2f]
    decide
  have h4 : 4 ∣ f * 2 := by
    rw [← hord]
    exact orderOf_dvd_iff_pow_eq_one.mpr hpow
  obtain ⟨k, hk⟩ := h4
  have hfeven : Even f := ⟨k, by omega⟩
  obtain ⟨m, rfl⟩ := hfeven
  intro h3
  have h3' : 3 ∣ 2 ^ (2 * m) + 1 := by simpa [two_mul] using h3
  have h : (((2 ^ (2 * m) + 1 : ℕ)) : ZMod 3) = 0 :=
    (ZMod.natCast_eq_zero_iff _ _).2 h3'
  rw [Nat.cast_add, Nat.cast_pow, Nat.cast_ofNat, Nat.cast_one] at h
  have h2m : ((2 : ZMod 3) ^ (2 * m)) = 1 := by
    rw [pow_mul]
    have h22 : (2 : ZMod 3) ^ 2 = 1 := by decide
    rw [h22, one_pow]
  rw [h2m] at h
  exact (by decide : (2 : ZMod 3) ≠ 0) h

theorem exists_fiveLangFrame {f : ℕ} (hf : 1 ≤ f) (h5 : 5 ∣ 2 ^ f + 1) :
    ∃ (ζK : (GaloisField 2 (2 * f))ˣ)
      (hζ : (Units.map (algebraMap (GaloisField 2 (2 * f))
        (AlgebraicClosure (GaloisField 2 (2 * f)))).toMonoidHom ζK) ^ 5 = 1)
      (g₀ : ModGL Tag.E6 (AlgebraicClosure (GaloisField 2 (2 * f))))
      (T : Subgroup ↥(graphFixedRootGroup TwistTag.E6 (GaloisField 2 (2 * f)) (frobQ 2 f)))
      (ι₀ : Multiplicative (Fin 6 → ZMod 5) →*
        ↥(graphFixedRootGroup TwistTag.E6 (GaloisField 2 (2 * f)) (frobQ 2 f))),
      orderOf ζK = 5 ∧
      g₀ ∈ adjointGroup Tag.E6 (AlgebraicClosure (GaloisField 2 (2 * f))) ∧
      Function.Injective ι₀ ∧
      (∀ s : Fin 6 → ZMod 5,
        baseChangeGL (algebraMap (GaloisField 2 (2 * f))
          (AlgebraicClosure (GaloisField 2 (2 * f))))
          (((ι₀ (Multiplicative.ofAdd s)) : _) :
            ModGL TwistTag.E6.tag (GaloisField 2 (2 * f))) =
        g₀ * frameDiag (τ := Tag.E6)
          (Units.map (algebraMap (GaloisField 2 (2 * f))
            (AlgebraicClosure (GaloisField 2 (2 * f)))).toMonoidHom ζK) hζ s * g₀⁻¹) ∧
      (∀ x ∈ T, ∀ y ∈ T, x * y = y * x) ∧
      ι₀.range ≤ T ∧
      (∀ t ∈ T, t ^ 5 = 1 → t ∈ ι₀.range) ∧
      Nat.card T = (2 ^ f + 1) ^ 6 ∧
      ∀ c : ↥(graphFixedRootGroup TwistTag.E6
          (GaloisField 2 (2 * f)) (frobQ 2 f)),
        (∀ x ∈ ι₀.range, c * x = x * c) → c ∈ T := by
  classical
  let K := GaloisField 2 (2 * f)
  let L := AlgebraicClosure K
  have hK : Nat.card K = (2 ^ f) ^ 2 := by
    rw [GaloisField.card 2 (2 * f) (by omega), ← pow_mul, mul_comm]
  haveI : Finite K := Nat.finite_of_card_ne_zero (by
    rw [hK]
    exact pow_ne_zero _ (by norm_num))
  haveI : Fintype K := Fintype.ofFinite K
  have h5dvd : 5 ∣ Nat.card K - 1 := by
    rw [hK]
    have hsq : (2 ^ f) ^ 2 - 1 = (2 ^ f - 1) * (2 ^ f + 1) := by
      simpa [mul_comm] using Nat.sq_sub_sq (2 ^ f) 1
    rw [hsq]
    exact dvd_mul_of_dvd_right h5 _
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : CharP K 2 := charP_of_card_eq_prime_pow (f := f * 2)
    (by rw [← Nat.card_eq_fintype_card, hK, ← pow_mul])
  haveI : CharP L 2 := charP_of_injective_algebraMap (algebraMap K L).injective 2
  haveI : IsAlgClosed L := IsAlgClosure.isAlgClosed K
  let Fr : L →+* L := iterateFrobenius L 2 f
  have hFr : ∀ c, Fr c = c ^ (2 ^ f) := fun c => iterateFrobenius_def 2 f c
  obtain ⟨ζK, hζKord⟩ := exists_orderOf_eq_of_dvd_card_sub_one (F := K) h5dvd
  let ζ : Lˣ := Units.map (algebraMap K L).toMonoidHom ζK
  have hmapinj : Function.Injective (Units.map (algebraMap K L).toMonoidHom) := by
    intro a b h
    exact Units.ext ((algebraMap K L).injective (congrArg (fun u : Lˣ => (u : L)) h))
  have hζo : orderOf ζ = 5 := by
    rw [show ζ = Units.map (algebraMap K L).toMonoidHom ζK from rfl,
      orderOf_injective (Units.map (algebraMap K L).toMonoidHom) hmapinj ζK, hζKord]
  have hζ : ζ ^ 5 = 1 := by
    rw [← hζo, pow_orderOf_eq_one]
  obtain ⟨g₀, hg₀C, hg₀⟩ :=
    lang_conjugator_twisted K (ℓ := 2) (f := f) hf L twE6PhiTwoWeyl
  let M : Matrix (Fin TwistTag.E6.tag.rank) (Fin TwistTag.E6.tag.rank) ℤ := -1
  have htomat : toMat TwistTag.E6.tag.rank twE6TwoMat = M := by
    ext i j
    fin_cases i <;> fin_cases j <;> rfl
  have hv : ∀ x : Fin TwistTag.E6.tag.rank → ℤ, twE6PhiTwoWeyl • x =
      M *ᵥ permLattice TwistTag.E6.perm x := by
    intro x
    rw [twE6PhiTwoWeyl_smul, htomat, Matrix.neg_mulVec, Matrix.one_mulVec]
  let n : ModGL TwistTag.E6.tag L :=
    canonicalRep (coxeterSystem TwistTag.E6.tag) L twE6PhiTwoWeyl
  let T₀ : Subgroup (ModGL TwistTag.E6.tag L) :=
    twistedTorusOf n (twistHom TwistTag.E6 L Fr)
  let X : Subgroup (ModGL TwistTag.E6.tag L) :=
    T₀.map (MulAut.conj g₀).toMonoidHom
  have hT0eq : T₀ = (fixedCharTuples M Fr).map
      (rootDiagUnitHom TwistTag.E6.tag L) :=
    twistedTorus_E6_eq_map (L := L) Fr twE6PhiTwoWeyl M hv
  have hdetnat : (M - ((2 ^ f : ℕ) : ℤ) • 1).det.natAbs = (2 ^ f + 1) ^ 6 := by
    simpa [M] using natAbs_det_neg_one_sub_smul_one (2 ^ f)
  have hBne : (M - ((2 ^ f : ℕ) : ℤ) • 1).det ≠ 0 := by
    intro h
    have h0 : (M - ((2 ^ f : ℕ) : ℤ) • 1).det.natAbs = 0 := by rw [h]; rfl
    rw [hdetnat] at h0
    have hpos : 0 < (2 ^ f + 1) ^ 6 := pow_pos (Nat.succ_pos (2 ^ f)) 6
    omega
  have hodd2f : Odd (2 ^ f + 1) := by
    obtain ⟨k, hk⟩ := dvd_pow_self 2 (by omega : f ≠ 0)
    exact ⟨k, by omega⟩
  have hcop2 : ¬ 2 ∣ (M - ((2 ^ f : ℕ) : ℤ) • 1).det.natAbs := by
    rw [hdetnat]
    intro hd
    exact (Nat.not_even_iff_odd.mpr (hodd2f.pow)) (even_iff_two_dvd.mpr hd)
  have hcardT0 : Nat.card T₀ = (2 ^ f + 1) ^ 6 := by
    rw [hT0eq, Subgroup.card_map_of_injective
      (CFSG.LieType.Chevalley.rootDiagUnit_injective (τ := TwistTag.E6.tag) (K := L)),
      natCard_fixedCharTuples M Fr hFr hBne hcop2, hdetnat]
  have hframeT0 : ∀ s : Fin TwistTag.E6.tag.rank → ZMod 5,
      frameDiag (τ := TwistTag.E6.tag) ζ hζ s ∈ T₀ :=
    fun s => frameDiag_mem_twistedTorus_five Fr hFr h5 hζo hζ s
  have hframeX : ∀ s : Fin TwistTag.E6.tag.rank → ZMod 5,
      g₀ * frameDiag (τ := TwistTag.E6.tag) ζ hζ s * g₀⁻¹ ∈ X :=
    fun s => ⟨_, hframeT0 s, rfl⟩
  have hcardX : Nat.card X = (2 ^ f + 1) ^ 6 := by
    rw [show Nat.card X = Nat.card T₀ from
      Subgroup.card_map_of_injective (MulAut.conj g₀).injective, hcardT0]
  have hnot3X : ¬ 3 ∣ Nat.card X := by
    rw [hcardX]
    intro h
    exact not_three_dvd_two_pow_add_one_of_five_dvd hf h5
      (Nat.Prime.dvd_of_dvd_pow Nat.prime_three h)
  obtain ⟨hfinR, -, hder, ⟨k, hk⟩, -, -, -⟩ :=
    CFSG.RankThree.Classical2.twisted_E6_full_rational_fixed_group_order
      (ℓ := 2) (f := f) Nat.prime_two hf K hK (frobQ 2 f)
      (fun c => iterateFrobenius_def 2 f c) L Fr hFr
  set R' : Subgroup (ModGL TwistTag.E6.tag L) := twistedFixedGroup TwistTag.E6 L Fr with hR'
  set C' : Subgroup (ModGL TwistTag.E6.tag L) :=
    (graphFixedRootGroup TwistTag.E6 K (frobQ 2 f)).map (baseChangeGL (algebraMap K L))
    with hC'
  haveI : Finite R' := hfinR
  have hle : C' ≤ R' := by
    rw [← hder]
    refine Subgroup.commutator_le.2 fun a ha b hb => ?_
    rw [commutatorElement_def]
    exact mul_mem (mul_mem (mul_mem ha hb) (inv_mem ha)) (inv_mem hb)
  have hnormal : (C'.subgroupOf R').Normal := by
    have e : C'.subgroupOf R' = ⁅(⊤ : Subgroup R'), ⊤⁆ := by
      have h1 : ⁅R', R'⁆ = Subgroup.map R'.subtype ⁅(⊤ : Subgroup R'), ⊤⁆ := by
        rw [Subgroup.map_commutator, ← MonoidHom.range_eq_map R'.subtype, Subgroup.range_subtype]
      rw [← hder, h1]
      exact Subgroup.comap_map_eq_self_of_injective (Subgroup.subtype_injective _) _
    rw [e]
    infer_instance
  haveI : (C'.subgroupOf R').Normal := hnormal
  have hXR : X ≤ R' := by
    rintro _ ⟨y, hy, rfl⟩
    rw [mem_twistedFixedGroup_iff_twistHom]
    refine ⟨?_, ?_⟩
    · exact mul_mem (mul_mem hg₀C (twistedTorusOf_le_adjointGroup n _ hy)) (inv_mem hg₀C)
    · have hyfix := (mem_twistedTorusOf.1 hy).2
      change twistHom TwistTag.E6 L Fr (g₀ * y * g₀⁻¹) = g₀ * y * g₀⁻¹
      rw [map_mul, map_mul, map_inv, hg₀]
      calc g₀ * n * twistHom TwistTag.E6 L Fr y * (g₀ * n)⁻¹
          = g₀ * (n * twistHom TwistTag.E6 L Fr y * n⁻¹) * g₀⁻¹ := by group
        _ = g₀ * y * g₀⁻¹ := by rw [hyfix]
  have hcop3 : Nat.Coprime (2 ^ f + 1) 3 :=
    ((Nat.Prime.coprime_iff_not_dvd Nat.prime_three).2
      (not_three_dvd_two_pow_add_one_of_five_dvd hf h5)).symm
  have hcop3k : Nat.Coprime (Nat.card X) (3 ^ k) := by
    rw [hcardX]
    exact (hcop3.pow_left 6).pow_right k
  let π : R' →* R' ⧸ (C'.subgroupOf R') := QuotientGroup.mk' _
  let Q : Subgroup (R' ⧸ (C'.subgroupOf R')) := (X.subgroupOf R').map π
  have hQ3 : Nat.card Q ∣ 3 ^ k := by
    have hcardquot : Nat.card (R' ⧸ (C'.subgroupOf R')) = 3 ^ k := by
      rw [← Subgroup.index_eq_card]
      exact hk
    rw [← hcardquot]
    simpa using Subgroup.card_dvd_of_le (show Q ≤ ⊤ from le_top)
  have hQX : Nat.card Q ∣ Nat.card X := by
    have h1 : Nat.card Q ∣ Nat.card (X.subgroupOf R') :=
      Subgroup.card_map_dvd (X.subgroupOf R') π
    have h2 : Nat.card (X.subgroupOf R') = Nat.card X :=
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hXR)
    rwa [h2] at h1
  have hQ1 : Nat.card Q = 1 := by
    have hgcd : Nat.card Q ∣ Nat.gcd (Nat.card X) (3 ^ k) := Nat.dvd_gcd hQX hQ3
    rw [hcop3k.gcd_eq_one] at hgcd
    exact Nat.dvd_one.mp hgcd
  have hQbot : Q = ⊥ := Subgroup.card_eq_one.mp hQ1
  have hleSub : X.subgroupOf R' ≤ C'.subgroupOf R' := by
    have hmapbot : (X.subgroupOf R').map π = ⊥ := hQbot
    have hker := (Subgroup.map_eq_bot_iff (X.subgroupOf R') (f := π)).1 hmapbot
    simpa [π, QuotientGroup.ker_mk'] using hker
  have hXC' : X ≤ C' := by
    intro x hx
    have hx' : (⟨x, hXR hx⟩ : R') ∈ X.subgroupOf R' := hx
    exact hleSub hx'
  let β : (↥(graphFixedRootGroup TwistTag.E6 K (frobQ 2 f))) →*
      ModGL TwistTag.E6.tag L :=
    (baseChangeGL (algebraMap K L)).comp
      (graphFixedRootGroup TwistTag.E6 K (frobQ 2 f)).subtype
  have hβinj : Function.Injective β :=
    (baseChangeGL_injective (algebraMap K L)).comp
      (Subgroup.subtype_injective (graphFixedRootGroup TwistTag.E6 K (frobQ 2 f)))
  have hβrange : β.range = C' := by
    change ((baseChangeGL (algebraMap K L)).comp
      (graphFixedRootGroup TwistTag.E6 K (frobQ 2 f)).subtype).range = _
    rw [MonoidHom.range_comp, Subgroup.range_subtype]
  have hXrange : X ≤ β.range := by
    rw [hβrange]
    exact hXC'
  let T : Subgroup ↥(graphFixedRootGroup TwistTag.E6 K (frobQ 2 f)) := X.comap β
  let ψ : Multiplicative (Fin TwistTag.E6.tag.rank → ZMod 5) →* β.range :=
    { toFun := fun s => ⟨g₀ * frameDiag (τ := TwistTag.E6.tag) ζ hζ
        (Multiplicative.toAdd s) * g₀⁻¹, hXrange (hframeX (Multiplicative.toAdd s))⟩
      map_one' := by
        apply Subtype.ext
        change g₀ * frameDiag (τ := TwistTag.E6.tag) ζ hζ
          (Multiplicative.toAdd (1 : Multiplicative (Fin TwistTag.E6.tag.rank → ZMod 5))) *
          g₀⁻¹ = 1
        rw [toAdd_one, frameDiag_zero]
        group
      map_mul' := fun s t => by
        apply Subtype.ext
        change g₀ * frameDiag (τ := TwistTag.E6.tag) ζ hζ
          (Multiplicative.toAdd (s * t)) * g₀⁻¹ =
          (g₀ * frameDiag (τ := TwistTag.E6.tag) ζ hζ (Multiplicative.toAdd s) * g₀⁻¹) *
            (g₀ * frameDiag (τ := TwistTag.E6.tag) ζ hζ (Multiplicative.toAdd t) * g₀⁻¹)
        rw [toAdd_mul, frameDiag_add]
        group }
  have hψinj : Function.Injective ψ := by
    intro s t hst
    have hfd : frameDiag (τ := TwistTag.E6.tag) ζ hζ (Multiplicative.toAdd s) =
        frameDiag (τ := TwistTag.E6.tag) ζ hζ (Multiplicative.toAdd t) := by
      have h := congrArg Subtype.val hst
      exact mul_left_cancel (mul_right_cancel h)
    exact Multiplicative.toAdd.injective
      (frameDiag_injective hζo hζ
        (CFSG.StandardType.StepTwoToralExc.isUnit_det_symmetrizedCartan_E6 (p := 5)
          (by norm_num)) hfd)
  let e : (↥(graphFixedRootGroup TwistTag.E6 K (frobQ 2 f))) ≃* β.range :=
    MonoidHom.ofInjective hβinj
  let ι₀ : Multiplicative (Fin TwistTag.E6.tag.rank → ZMod 5) →*
      ↥(graphFixedRootGroup TwistTag.E6 K (frobQ 2 f)) := e.symm.toMonoidHom.comp ψ
  have hι₀val : ∀ s : Multiplicative (Fin TwistTag.E6.tag.rank → ZMod 5),
      β (ι₀ s) = g₀ * frameDiag (τ := TwistTag.E6.tag) ζ hζ
        (Multiplicative.toAdd s) * g₀⁻¹ := by
    intro s
    have h := MonoidHom.apply_ofInjective_symm hβinj (ψ s)
    simpa [ι₀, e, ψ] using h
  have hι₀inj : Function.Injective ι₀ := by
    intro s t hst
    exact hψinj (e.symm.injective hst)
  have hmapT : T.map β = X := Subgroup.map_comap_eq_self hXrange
  have hcardT : Nat.card T = (2 ^ f + 1) ^ 6 := by
    rw [← Subgroup.card_map_of_injective hβinj, hmapT, hcardX]
  have hcommT : ∀ x ∈ T, ∀ y ∈ T, x * y = y * x := by
    intro x hx y hy
    apply hβinj
    rw [map_mul, map_mul]
    obtain ⟨a, ha, hxa⟩ := hx
    obtain ⟨b, hb, hyb⟩ := hy
    have hab : a * b = b * a := torusGroup_comm (mem_twistedTorusOf.1 ha).1
      (mem_twistedTorusOf.1 hb).1
    calc β x * β y = (g₀ * a * g₀⁻¹) * (g₀ * b * g₀⁻¹) := by
          rw [← hxa, ← hyb]
          rfl
      _ = g₀ * (a * b) * g₀⁻¹ := by group
      _ = g₀ * (b * a) * g₀⁻¹ := by rw [hab]
      _ = (g₀ * b * g₀⁻¹) * (g₀ * a * g₀⁻¹) := by group
      _ = β y * β x := by
          rw [← hyb, ← hxa]
          rfl
  have hrangeT : ι₀.range ≤ T := by
    rintro _ ⟨s, rfl⟩
    change β (ι₀ s) ∈ X
    rw [hι₀val s]
    exact hframeX (Multiplicative.toAdd s)
  have htors : ∀ t ∈ T, t ^ 5 = 1 → t ∈ ι₀.range := by
    intro t ht ht5
    obtain ⟨y, hyT0, hxy⟩ := ht
    have hy5 : y ^ 5 = 1 := by
      have hβt : β t = g₀ * y * g₀⁻¹ := hxy.symm
      have h1 : (g₀ * y * g₀⁻¹) ^ 5 = 1 := by
        rw [← hβt, ← map_pow, ht5, map_one]
      apply (MulAut.conj g₀).injective
      rw [map_pow, map_one]
      simpa only [MulAut.conj_apply] using h1
    have hyT : y ∈ torusGroup TwistTag.E6.tag L := (mem_twistedTorusOf.1 hyT0).1
    obtain ⟨s, hs⟩ := exists_frameDiag_of_mem (τ := TwistTag.E6.tag) (p := 5)
      hζo hζ (CFSG.StandardType.StepTwoToralExc.isUnit_det_symmetrizedCartan_E6
        (p := 5) (by norm_num)) ⟨hyT, hy5⟩
    refine ⟨Multiplicative.ofAdd s, ?_⟩
    apply hβinj
    rw [hι₀val (Multiplicative.ofAdd s), toAdd_ofAdd, hs]
    exact hxy
  have hcent : ∀ c : ↥(graphFixedRootGroup TwistTag.E6 K (frobQ 2 f)),
      (∀ x ∈ ι₀.range, c * x = x * c) → c ∈ T := by
    intro c hc
    change β c ∈ X
    have hc' : ∀ s, c * ι₀ s = ι₀ s * c := fun s => hc _ ⟨s, rfl⟩
    have hzcomm : ∀ s : Fin TwistTag.E6.tag.rank → ZMod 5,
        β c * (g₀ * frameDiag (τ := TwistTag.E6.tag) ζ hζ s * g₀⁻¹) =
          (g₀ * frameDiag (τ := TwistTag.E6.tag) ζ hζ s * g₀⁻¹) * β c := by
      intro s
      have h := congrArg β (hc' (Multiplicative.ofAdd s))
      simpa [map_mul, hι₀val] using h
    let y : ModGL TwistTag.E6.tag L := g₀⁻¹ * β c * g₀
    have hzC' : β c ∈ C' := by
      rw [← hβrange]
      exact ⟨c, rfl⟩
    have hzR : β c ∈ R' := hle hzC'
    have hzAdj : β c ∈ adjointGroup TwistTag.E6.tag L :=
      ((mem_twistedFixedGroup_iff_twistHom TwistTag.E6 L Fr).1 hzR).1
    have hyC : y ∈ adjointGroup TwistTag.E6.tag L :=
      mul_mem (mul_mem (inv_mem hg₀C) hzAdj) hg₀C
    have hycomm : ∀ s, y * frameDiag (τ := TwistTag.E6.tag) ζ hζ s =
        frameDiag (τ := TwistTag.E6.tag) ζ hζ s * y := by
      intro s
      have h := hzcomm s
      change (g₀⁻¹ * β c * g₀) * frameDiag (τ := TwistTag.E6.tag) ζ hζ s =
        frameDiag (τ := TwistTag.E6.tag) ζ hζ s * (g₀⁻¹ * β c * g₀)
      calc (g₀⁻¹ * β c * g₀) * frameDiag (τ := TwistTag.E6.tag) ζ hζ s
          = g₀⁻¹ * (β c * (g₀ * frameDiag (τ := TwistTag.E6.tag) ζ hζ s * g₀⁻¹)) * g₀ := by
            group
        _ = g₀⁻¹ * ((g₀ * frameDiag (τ := TwistTag.E6.tag) ζ hζ s * g₀⁻¹) * β c) * g₀ := by
            rw [h]
        _ = frameDiag (τ := TwistTag.E6.tag) ζ hζ s * (g₀⁻¹ * β c * g₀) := by group
    have hyT : y ∈ torusGroup TwistTag.E6.tag L :=
      mem_torusGroup_of_commute_fiveFrameDiag hζo hζ hyC hycomm
    have hzfix : twistHom TwistTag.E6 L Fr (β c) = β c :=
      ((mem_twistedFixedGroup_iff_twistHom TwistTag.E6 L Fr).1 hzR).2
    have hyT0 : y ∈ T₀ := by
      rw [mem_twistedTorusOf]
      refine ⟨hyT, ?_⟩
      have hconj : twistHom TwistTag.E6 L Fr y = n⁻¹ * y * n := by
        change twistHom TwistTag.E6 L Fr (g₀⁻¹ * β c * g₀) = n⁻¹ * y * n
        rw [map_mul, map_mul, map_inv, hg₀, hzfix]
        simp only [y, n]
        group
      rw [hconj]
      group
    exact ⟨y, hyT0, by
      change g₀ * (g₀⁻¹ * β c * g₀) * g₀⁻¹ = β c
      group⟩
  exact ⟨ζK, hζ, g₀, T, ι₀, hζKord, hg₀C, hι₀inj,
    fun s => hι₀val (Multiplicative.ofAdd s), hcommT, hrangeT, htors, hcardT, hcent⟩

end FiveLang

end ExcFrames

end CFSG.StandardType
