module

public import CFSG.HardMathSupport.Solomon.Coordinator.LieComp.Exc.RecogF4
public import CFSG.LocalAnalysis.ComponentClassification.CatLeafProofF4C3
public import CFSG.LieType.Chevalley.ParabolicRootFactorData
public import CFSG.LocalAnalysis.SeitzReduction.F4PilotCentralizerTUStd
import CFSG.LieType.Chevalley.GraphFixedD4TorusWords
import CFSG.LieType.Chevalley.RootCharacterConjugation
import CFSG.LieType.Chevalley.BruhatCellFactorization
public import CFSG.CharacterTheory.BrauerThirdMainTheorem.CentralResidueMaps
public import CFSG.CharacterTheory.BrauerThirdMainTheorem.NormalizerClassLifting
public import CFSG.CharacterTheory.BrauerThirdMainTheorem.PrincipalClassDefects
public import CFSG.ClassicalInvolution.ModelFacts.StandardPairChevalley
public import CFSG.ClassicalInvolution.Models.LinearFrames
public import CFSG.ClassicalInvolution.Models.LinearPairs
public import CFSG.ClassicalInvolution.Models.SymplecticPairs.Quadruple
public import CFSG.ClassicalInvolution.WeakCT.Main
public import CFSG.HardMathSupport.Solomon.Coordinator.LieComp.Exc.Basic
public import CFSG.HardMathSupport.Solomon.Coordinator.LieComp.Exc.Certs
public import CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple.ExcInnerLang
public import CFSG.HardMathSupport.Timmesfeld.CrossChar.ExcInnerTwRigid
public import CFSG.HardMathSupport.Timmesfeld.LangTorus.CentralizerTrivialPoly
public import CFSG.HardMathSupport.Timmesfeld.LangTorus.OuterField
public import CFSG.HardMathSupport.Timmesfeld.LangTorus.RigidField
public import CFSG.HardMathSupport.Timmesfeld.LangTorus.RigidNorm
public import CFSG.HardMathSupport.Timmesfeld.LocalTwo.CrossLin
public import CFSG.HardMathSupport.Timmesfeld.LocalTwo.LangFrame
public import CFSG.LieType.Chevalley.C2E6StandardFixedData
public import CFSG.LieType.Chevalley.C2E6UnitaryFourImages
public import CFSG.LieType.Chevalley.E6SecondGraphFullCentralizer
public import CFSG.LieType.Chevalley.SimplyLacedFieldTwoCover
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitHeMax
public import CFSG.LocalAnalysis.ComponentClassification.OutcomeLocalOddCentralizer
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCorrCriticalStandard
public import CFSG.LocalAnalysis.SeitzReduction.F4PilotToralCentralizer
public import CFSG.RankThree.PartOne.KE.SLnShape
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
public import CFSG.Walter.JRFacts
public import Certificates.Certificate10
public import Certificates.Certificate10050
public import Certificates.Certificate11
public import Certificates.Certificate12
public import Certificates.Certificate13659
public import Certificates.Certificate13660
public import Certificates.Certificate1952
public import Certificates.Certificate3
public import Certificates.Certificate4
public import Certificates.Certificate42
public import Certificates.Certificate44
public import Certificates.Certificate5
public import Certificates.Certificate6
public import Certificates.Certificate7
public import Certificates.Certificate8
public import Certificates.Certificate8117
public import Certificates.Certificate9

public section

namespace CFSG.StandardType.RCKRP

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.HardMathSupport.Solomon.Coordinator.LieComp CFSG.ComponentClassification.CatLeafProof
  CFSG.SeitzReduction.F4Pilot CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley

theorem rootDiagUnit_conj_eq_of_eqOn
    {τ : Tag} {K : Type} [Field K] {J : Set (Fin τ.rank)}
    {l l' : Fin τ.rank → Kˣ} (hl : ∀ j ∈ J, l j = l' j) {g : ModGL τ K}
    (hg : g ∈ rootSpan τ K (parabolicRoots τ J)) :
    rootDiagUnit τ l * g * (rootDiagUnit τ l)⁻¹ =
      rootDiagUnit τ l' * g * (rootDiagUnit τ l')⁻¹ := by
  let f : ModGL τ K →* ModGL τ K := (MulAut.conj (rootDiagUnit τ l)).toMonoidHom
  let f' : ModGL τ K →* ModGL τ K := (MulAut.conj (rootDiagUnit τ l')).toMonoidHom
  have hle : rootSpan τ K (parabolicRoots τ J) ≤ MonoidHom.eqLocus f f' := by
    refine iSup₂_le fun α hα => ?_
    refine (Subgroup.closure_le _).2 ?_
    rintro x ⟨c, rfl⟩
    change f (pinnedX τ K α c) = f' (pinnedX τ K α c)
    have hχ : rootChar l α = rootChar l' α := by
      simp only [rootChar]
      refine Finset.prod_congr rfl fun j _ => ?_
      by_cases hj : j ∈ J
      · rw [hl j hj]
      · rw [hα.2 j hj, zpow_zero, zpow_zero]
    simp only [f, f', MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    rw [rootDiagUnit_conj_pinnedX l hα.1 c, rootDiagUnit_conj_pinnedX l' hα.1 c, hχ]
  have hmem : f g = f' g := hle hg
  simpa only [f, f', MulEquiv.coe_toMonoidHom, MulAut.conj_apply] using hmem

private theorem single_mem_parabolicRoots_of_mem {τ : Tag} {J : Set (Fin τ.rank)} {k : Fin τ.rank}
    (hk : k ∈ J) : (Pi.single k 1 : Fin τ.rank → ℤ) ∈ parabolicRoots τ J := by
  refine ⟨isRoot_single τ k, fun i hi => ?_⟩
  have hne : i ≠ k := fun h => hi (by simpa [h] using hk)
  exact Pi.single_eq_of_ne (i := k) (i' := i) hne 1

private theorem neg_single_mem_parabolicRoots_of_mem {τ : Tag} {J : Set (Fin τ.rank)}
    {k : Fin τ.rank} (hk : k ∈ J) :
    (-Pi.single k 1 : Fin τ.rank → ℤ) ∈ parabolicRoots τ J := by
  refine ⟨isRoot_neg_single τ k, fun i hi => ?_⟩
  have hne : i ≠ k := fun h => hi (by simpa [h] using hk)
  simp [Pi.single_eq_of_ne (i := k) (i' := i) hne]

private theorem torusElt_mem_rootSpan_of_single
    {τ : Tag} {K : Type} [Field K]
    {S : Set (Fin τ.rank → ℤ)} {k : Fin τ.rank}
    (h1 : (Pi.single k 1 : Fin τ.rank → ℤ) ∈ S)
    (h2 : (-Pi.single k 1 : Fin τ.rank → ℤ) ∈ S) (t : Kˣ) :
    torusElt τ K k t ∈ rootSpan τ K S := by
  have hx : ∀ c, xUnit τ K k c ∈ rootSpan τ K S := fun c => by
    rw [← pinnedX_single]
    exact pinnedX_mem_rootSpan h1 c
  have hy : ∀ c, yUnit τ K k c ∈ rootSpan τ K S := fun c => by
    rw [← pinnedX_neg_single]
    exact pinnedX_mem_rootSpan h2 c
  have hw : ∀ s : Kˣ, weylElt τ K k s ∈ rootSpan τ K S := fun s => by
    rw [CFSG.LieType.Chevalley.weylElt_eq_xUnit_mul]
    exact mul_mem (mul_mem (hx _) (hy _)) (hx _)
  exact mul_mem (hw t) (hw (-1))

private theorem exists_rootDiagUnit_eq_on_f4LeviB3
    {L : Type} [Field L] [IsAlgClosed L]
    (l : Fin Tag.F4.rank → Lˣ) :
    ∃ (t₁ : ModGL Tag.F4 L) (l' : Fin Tag.F4.rank → Lˣ),
      t₁ ∈ rootSpan Tag.F4 L (parabolicRoots Tag.F4 f4LeviB3) ∧
        t₁ = rootDiagUnit Tag.F4 l' ∧ ∀ j ∈ f4LeviB3, l j = l' j := by
  obtain ⟨s, hs⟩ := IsAlgClosed.exists_eq_mul_self (((l 0 * l 2 : Lˣ) : L))
  have hs0 : s ≠ 0 := by
    rintro h
    have hzero : (((l 0 * l 2 : Lˣ) : L)) = 0 := by rw [hs, h, mul_zero]
    exact (l 0 * l 2).ne_zero hzero
  let s' : Lˣ := Units.mk0 s hs0
  have hs' : s' * s' = l 0 * l 2 := by
    refine Units.ext ?_
    change s * s = ((l 0 * l 2 : Lˣ) : L)
    simpa only [Units.val_mul] using hs.symm
  let u0 : Lˣ := l 0 * l 1 * l 2
  let u1 : Lˣ := l 0 * l 1 ^ 2 * l 2 ^ 2
  let u2 : Lˣ := l 1 * l 2 * s'
  let l' : Fin Tag.F4.rank → Lˣ := fun j =>
    u0 ^ Tag.cartan Tag.F4 0 j * u1 ^ Tag.cartan Tag.F4 1 j * u2 ^ Tag.cartan Tag.F4 2 j
  let t₁ : ModGL Tag.F4 L :=
    torusElt Tag.F4 L 0 u0 * torusElt Tag.F4 L 1 u1 * torusElt Tag.F4 L 2 u2
  have hJ0 : (0 : Fin Tag.F4.rank) ∈ f4LeviB3 := ⟨0, by decide⟩
  have hJ1 : (1 : Fin Tag.F4.rank) ∈ f4LeviB3 := ⟨1, by decide⟩
  have hJ2 : (2 : Fin Tag.F4.rank) ∈ f4LeviB3 := ⟨2, by decide⟩
  refine ⟨t₁, l', ?_, ?_, ?_⟩
  · change torusElt Tag.F4 L 0 u0 * torusElt Tag.F4 L 1 u1 * torusElt Tag.F4 L 2 u2 ∈
      rootSpan Tag.F4 L (parabolicRoots Tag.F4 f4LeviB3)
    exact mul_mem (mul_mem
      (torusElt_mem_rootSpan_of_single (single_mem_parabolicRoots_of_mem hJ0)
        (neg_single_mem_parabolicRoots_of_mem hJ0) u0)
      (torusElt_mem_rootSpan_of_single (single_mem_parabolicRoots_of_mem hJ1)
        (neg_single_mem_parabolicRoots_of_mem hJ1) u1))
      (torusElt_mem_rootSpan_of_single (single_mem_parabolicRoots_of_mem hJ2)
        (neg_single_mem_parabolicRoots_of_mem hJ2) u2)
  · change torusElt Tag.F4 L 0 u0 * torusElt Tag.F4 L 1 u1 * torusElt Tag.F4 L 2 u2 =
      rootDiagUnit Tag.F4 l'
    rw [torusElt_eq_rootDiagUnit, torusElt_eq_rootDiagUnit, torusElt_eq_rootDiagUnit,
      ← rootDiagUnit_mul, ← rootDiagUnit_mul]
    rfl
  · intro j hj
    have hcases : j = 0 ∨ j = 1 ∨ j = 2 := by
      obtain ⟨k, rfl⟩ := hj
      fin_cases k <;> decide
    rcases hcases with rfl | rfl | rfl
    · change l 0 = u0 ^ Tag.cartan Tag.F4 0 0 * u1 ^ Tag.cartan Tag.F4 1 0 *
        u2 ^ Tag.cartan Tag.F4 2 0
      rw [show Tag.cartan Tag.F4 (0 : Fin Tag.F4.rank) 0 = 2 from by decide,
        show Tag.cartan Tag.F4 (1 : Fin Tag.F4.rank) 0 = -1 from by decide,
        show Tag.cartan Tag.F4 (2 : Fin Tag.F4.rank) 0 = 0 from by decide]
      refine Units.ext ?_
      simp only [Units.val_mul, Units.val_pow_eq_pow_val, Units.val_zpow_eq_zpow_val,
        u0, u1, u2, zpow_zero, mul_one]
      field_simp
    · change l 1 = u0 ^ Tag.cartan Tag.F4 0 1 * u1 ^ Tag.cartan Tag.F4 1 1 *
        u2 ^ Tag.cartan Tag.F4 2 1
      rw [show Tag.cartan Tag.F4 (0 : Fin Tag.F4.rank) 1 = -1 from by decide,
        show Tag.cartan Tag.F4 (1 : Fin Tag.F4.rank) 1 = 2 from by decide,
        show Tag.cartan Tag.F4 (2 : Fin Tag.F4.rank) 1 = -2 from by decide]
      refine Units.ext ?_
      simp only [Units.val_mul, Units.val_pow_eq_pow_val, Units.val_zpow_eq_zpow_val, u0, u1, u2]
      field_simp
      rw [pow_two]
      simpa only [Units.val_mul] using congrArg Units.val hs'
    · change l 2 = u0 ^ Tag.cartan Tag.F4 0 2 * u1 ^ Tag.cartan Tag.F4 1 2 *
        u2 ^ Tag.cartan Tag.F4 2 2
      rw [show Tag.cartan Tag.F4 (0 : Fin Tag.F4.rank) 2 = 0 from by decide,
        show Tag.cartan Tag.F4 (1 : Fin Tag.F4.rank) 2 = -1 from by decide,
        show Tag.cartan Tag.F4 (2 : Fin Tag.F4.rank) 2 = 2 from by decide]
      refine Units.ext ?_
      simp only [Units.val_mul, Units.val_pow_eq_pow_val, Units.val_zpow_eq_zpow_val,
        u0, u1, u2, zpow_zero]
      field_simp
      rw [pow_two]
      simp only [Units.val_one, one_mul, mul_comm (l 2 : L) (l 0)]
      simpa only [Units.val_mul] using (congrArg Units.val hs').symm

private theorem exists_rootDiagUnit_eq_on_f4LeviC3
    {L : Type} [Field L] [IsAlgClosed L]
    (l : Fin Tag.F4.rank → Lˣ) :
    ∃ (t₁ : ModGL Tag.F4 L) (l' : Fin Tag.F4.rank → Lˣ),
      t₁ ∈ rootSpan Tag.F4 L (parabolicRoots Tag.F4 f4LeviC3) ∧
        t₁ = rootDiagUnit Tag.F4 l' ∧ ∀ j ∈ f4LeviC3, l j = l' j := by
  obtain ⟨s, hs⟩ := IsAlgClosed.exists_eq_mul_self (((l 1 : Lˣ) : L))
  have hs0 : s ≠ 0 := by
    rintro h
    have hzero : (((l 1 : Lˣ) : L)) = 0 := by rw [hs, h, mul_zero]
    exact (l 1).ne_zero hzero
  let s' : Lˣ := Units.mk0 s hs0
  have hs' : s' * s' = l 1 := by
    refine Units.ext ?_
    change s * s = ((l 1 : Lˣ) : L)
    simpa only [Units.val_mul] using hs.symm
  let u2 : Lˣ := l 1 * l 2 ^ 2 * l 3
  let u1 : Lˣ := s' * u2
  let u3 : Lˣ := s' * l 2 * l 3
  let l' : Fin Tag.F4.rank → Lˣ := fun j =>
    u1 ^ Tag.cartan Tag.F4 1 j * u2 ^ Tag.cartan Tag.F4 2 j * u3 ^ Tag.cartan Tag.F4 3 j
  let t₁ : ModGL Tag.F4 L :=
    torusElt Tag.F4 L 1 u1 * torusElt Tag.F4 L 2 u2 * torusElt Tag.F4 L 3 u3
  have hJ3 : (3 : Fin Tag.F4.rank) ∈ f4LeviC3 := ⟨0, by decide⟩
  have hJ2 : (2 : Fin Tag.F4.rank) ∈ f4LeviC3 := ⟨1, by decide⟩
  have hJ1 : (1 : Fin Tag.F4.rank) ∈ f4LeviC3 := ⟨2, by decide⟩
  refine ⟨t₁, l', ?_, ?_, ?_⟩
  · change torusElt Tag.F4 L 1 u1 * torusElt Tag.F4 L 2 u2 * torusElt Tag.F4 L 3 u3 ∈
      rootSpan Tag.F4 L (parabolicRoots Tag.F4 f4LeviC3)
    exact mul_mem (mul_mem
      (torusElt_mem_rootSpan_of_single (single_mem_parabolicRoots_of_mem hJ1)
        (neg_single_mem_parabolicRoots_of_mem hJ1) u1)
      (torusElt_mem_rootSpan_of_single (single_mem_parabolicRoots_of_mem hJ2)
        (neg_single_mem_parabolicRoots_of_mem hJ2) u2))
      (torusElt_mem_rootSpan_of_single (single_mem_parabolicRoots_of_mem hJ3)
        (neg_single_mem_parabolicRoots_of_mem hJ3) u3)
  · change torusElt Tag.F4 L 1 u1 * torusElt Tag.F4 L 2 u2 * torusElt Tag.F4 L 3 u3 =
      rootDiagUnit Tag.F4 l'
    rw [torusElt_eq_rootDiagUnit, torusElt_eq_rootDiagUnit, torusElt_eq_rootDiagUnit,
      ← rootDiagUnit_mul, ← rootDiagUnit_mul]
    rfl
  · intro j hj
    have hcases : j = 3 ∨ j = 2 ∨ j = 1 := by
      obtain ⟨k, rfl⟩ := hj
      fin_cases k <;> decide
    rcases hcases with rfl | rfl | rfl
    · change l 3 = u1 ^ Tag.cartan Tag.F4 1 3 * u2 ^ Tag.cartan Tag.F4 2 3 *
        u3 ^ Tag.cartan Tag.F4 3 3
      rw [show Tag.cartan Tag.F4 (1 : Fin Tag.F4.rank) 3 = 0 from by decide,
        show Tag.cartan Tag.F4 (2 : Fin Tag.F4.rank) 3 = -1 from by decide,
        show Tag.cartan Tag.F4 (3 : Fin Tag.F4.rank) 3 = 2 from by decide]
      refine Units.ext ?_
      simp only [Units.val_mul, Units.val_pow_eq_pow_val, Units.val_zpow_eq_zpow_val,
        u1, u2, u3, zpow_zero]
      field_simp
      rw [pow_two]
      simp only [Units.val_one, one_mul]
      simpa only [Units.val_mul] using (congrArg Units.val hs').symm
    · change l 2 = u1 ^ Tag.cartan Tag.F4 1 2 * u2 ^ Tag.cartan Tag.F4 2 2 *
        u3 ^ Tag.cartan Tag.F4 3 2
      rw [show Tag.cartan Tag.F4 (1 : Fin Tag.F4.rank) 2 = -1 from by decide,
        show Tag.cartan Tag.F4 (2 : Fin Tag.F4.rank) 2 = 2 from by decide,
        show Tag.cartan Tag.F4 (3 : Fin Tag.F4.rank) 2 = -1 from by decide]
      refine Units.ext ?_
      simp only [Units.val_mul, Units.val_pow_eq_pow_val, Units.val_zpow_eq_zpow_val, u1, u2, u3]
      field_simp
      rw [pow_two]
      simpa only [Units.val_mul] using congrArg Units.val hs'
    · change l 1 = u1 ^ Tag.cartan Tag.F4 1 1 * u2 ^ Tag.cartan Tag.F4 2 1 *
        u3 ^ Tag.cartan Tag.F4 3 1
      rw [show Tag.cartan Tag.F4 (1 : Fin Tag.F4.rank) 1 = 2 from by decide,
        show Tag.cartan Tag.F4 (2 : Fin Tag.F4.rank) 1 = -2 from by decide,
        show Tag.cartan Tag.F4 (3 : Fin Tag.F4.rank) 1 = 0 from by decide]
      refine Units.ext ?_
      simp only [Units.val_mul, Units.val_pow_eq_pow_val, Units.val_zpow_eq_zpow_val,
        u1, u2, u3, zpow_zero, mul_one]
      field_simp
      rw [pow_two]
      simpa only [Units.val_mul] using (congrArg Units.val hs').symm

private theorem exists_rootDiagUnit_eq_on_b2Levi
    {L : Type} [Field L] [IsAlgClosed L]
    (l : Fin Tag.F4.rank → Lˣ) :
    ∃ (t₁ : ModGL Tag.F4 L) (l' : Fin Tag.F4.rank → Lˣ),
      t₁ ∈ rootSpan Tag.F4 L b2LeviRoots ∧
        t₁ = rootDiagUnit Tag.F4 l' ∧ ∀ j ∈ nodesTU, l j = l' j := by
  obtain ⟨s, hs⟩ := IsAlgClosed.exists_eq_mul_self (((l 1 : Lˣ) : L))
  have hs0 : s ≠ 0 := by
    rintro h
    have hzero : (((l 1 : Lˣ) : L)) = 0 := by rw [hs, h, mul_zero]
    exact (l 1).ne_zero hzero
  let s' : Lˣ := Units.mk0 s hs0
  have hs' : s' * s' = l 1 := by
    refine Units.ext ?_
    change s * s = ((l 1 : Lˣ) : L)
    simpa only [Units.val_mul] using hs.symm
  let u1 : Lˣ := l 1 * l 2
  let u2 : Lˣ := s' * l 2
  let l' : Fin Tag.F4.rank → Lˣ := fun j =>
    u1 ^ Tag.cartan Tag.F4 1 j * u2 ^ Tag.cartan Tag.F4 2 j
  let t₁ : ModGL Tag.F4 L := torusElt Tag.F4 L 1 u1 * torusElt Tag.F4 L 2 u2
  have hS1 : (Pi.single (1 : Fin Tag.F4.rank) 1 : Fin Tag.F4.rank → ℤ) ∈ b2LeviRoots := by
    rw [mem_b2LeviRoots]
    exact ⟨isRoot_single Tag.F4 1, by decide, by decide⟩
  have hS1' : (-Pi.single (1 : Fin Tag.F4.rank) 1 : Fin Tag.F4.rank → ℤ) ∈ b2LeviRoots := by
    rw [mem_b2LeviRoots]
    exact ⟨isRoot_neg_single Tag.F4 1, by decide, by decide⟩
  have hS2 : (Pi.single (2 : Fin Tag.F4.rank) 1 : Fin Tag.F4.rank → ℤ) ∈ b2LeviRoots := by
    rw [mem_b2LeviRoots]
    exact ⟨isRoot_single Tag.F4 2, by decide, by decide⟩
  have hS2' : (-Pi.single (2 : Fin Tag.F4.rank) 1 : Fin Tag.F4.rank → ℤ) ∈ b2LeviRoots := by
    rw [mem_b2LeviRoots]
    exact ⟨isRoot_neg_single Tag.F4 2, by decide, by decide⟩
  refine ⟨t₁, l', ?_, ?_, ?_⟩
  · change torusElt Tag.F4 L 1 u1 * torusElt Tag.F4 L 2 u2 ∈ rootSpan Tag.F4 L b2LeviRoots
    exact mul_mem
      (torusElt_mem_rootSpan_of_single hS1 hS1' u1)
      (torusElt_mem_rootSpan_of_single hS2 hS2' u2)
  · change torusElt Tag.F4 L 1 u1 * torusElt Tag.F4 L 2 u2 = rootDiagUnit Tag.F4 l'
    rw [torusElt_eq_rootDiagUnit, torusElt_eq_rootDiagUnit, ← rootDiagUnit_mul]
    rfl
  · intro j hj
    have hcases : j = 1 ∨ j = 2 := by
      fin_cases j
      · exact absurd rfl hj.1
      · exact Or.inl rfl
      · exact Or.inr rfl
      · exact absurd rfl hj.2
    rcases hcases with rfl | rfl
    · change l 1 = u1 ^ Tag.cartan Tag.F4 1 1 * u2 ^ Tag.cartan Tag.F4 2 1
      rw [show Tag.cartan Tag.F4 (1 : Fin Tag.F4.rank) 1 = 2 from by decide,
        show Tag.cartan Tag.F4 (2 : Fin Tag.F4.rank) 1 = -2 from by decide]
      refine Units.ext ?_
      simp only [Units.val_mul, Units.val_zpow_eq_zpow_val, u1, u2]
      field_simp
      rw [pow_two]
      simpa only [Units.val_mul] using congrArg Units.val hs'
    · change l 2 = u1 ^ Tag.cartan Tag.F4 1 2 * u2 ^ Tag.cartan Tag.F4 2 2
      rw [show Tag.cartan Tag.F4 (1 : Fin Tag.F4.rank) 2 = -1 from by decide,
        show Tag.cartan Tag.F4 (2 : Fin Tag.F4.rank) 2 = 2 from by decide]
      refine Units.ext ?_
      simp only [Units.val_mul, Units.val_zpow_eq_zpow_val, u1, u2]
      field_simp
      rw [pow_two]
      simpa only [Units.val_mul] using (congrArg Units.val hs').symm

theorem exists_mem_rootSpan_conj_eq_f4Levi
    {L : Type} [Field L] [IsAlgClosed L]
    {J : Set (Fin Tag.F4.rank)} (hJ : J = f4LeviB3 ∨ J = f4LeviC3) {t : ModGL Tag.F4 L}
    (ht : t ∈ torusGroup Tag.F4 L) :
    ∃ t₁ ∈ rootSpan Tag.F4 L (parabolicRoots Tag.F4 J),
      ∀ g ∈ rootSpan Tag.F4 L (parabolicRoots Tag.F4 J), t * g * t⁻¹ = t₁ * g * t₁⁻¹ := by
  obtain ⟨l, rfl⟩ := exists_rootDiagUnit_eq_of_mem_torusGroup ht
  rcases hJ with rfl | rfl
  · obtain ⟨t₁, l', ht₁mem, ht₁eq, hl⟩ := exists_rootDiagUnit_eq_on_f4LeviB3 l
    exact ⟨t₁, ht₁mem, fun g hg => by
      rw [ht₁eq]
      exact rootDiagUnit_conj_eq_of_eqOn hl hg⟩
  · obtain ⟨t₁, l', ht₁mem, ht₁eq, hl⟩ := exists_rootDiagUnit_eq_on_f4LeviC3 l
    exact ⟨t₁, ht₁mem, fun g hg => by
      rw [ht₁eq]
      exact rootDiagUnit_conj_eq_of_eqOn hl hg⟩

theorem exists_mem_rootSpan_conj_eq_b2Levi
    {L : Type} [Field L] [IsAlgClosed L] {t : ModGL Tag.F4 L}
    (ht : t ∈ torusGroup Tag.F4 L) :
    ∃ t₁ ∈ rootSpan Tag.F4 L b2LeviRoots,
      ∀ g ∈ rootSpan Tag.F4 L b2LeviRoots, t * g * t⁻¹ = t₁ * g * t₁⁻¹ := by
  obtain ⟨l, rfl⟩ := exists_rootDiagUnit_eq_of_mem_torusGroup ht
  obtain ⟨t₁, l', ht₁mem, ht₁eq, hl⟩ := exists_rootDiagUnit_eq_on_b2Levi l
  exact ⟨t₁, ht₁mem, fun g hg => by
    rw [ht₁eq]
    exact rootDiagUnit_conj_eq_of_eqOn hl hg⟩

end CFSG.StandardType.RCKRP

end
