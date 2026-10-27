module

public import CFSG.LocalAnalysis.StandardType.GGUSixTwoTransvection
public import CFSG.Open.LocalVocabulary
public import CFSG.LocalAnalysis.SeitzReduction.UnitaryPilotTransvectionCore
public import CFSG.ClassicalInvolution.Asc77.AscSCH19
public import CFSG.RankThree.GF2n.Smith81.S81U6Iso
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalPointDataReindex
public import CFSG.ClassicalInvolution.Asc77.AscSCH03
public import CFSG.LieType.Steinberg.Classical.SpinFrame
public import CFSG.LieType.Steinberg.Exceptional.E6E7
public import CFSG.LieType.Steinberg.Families
public import CFSG.LieType.Steinberg.G2
public import CFSG.LieType.Universal.Spin.Generation
public import CFSG.LieType.Universal.Spin.OddCT
public import CFSG.LieType.Universal.Spin.PlusCT
public import CFSG.LieType.Universal.Spin.Structure
public import CFSG.LieType.Universal.SpinOmega
public import CFSG.LieType.Universal.Unitary
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBDerivedNormalSectionBound
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalPointDataGeometry
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalSemilinearDataCompatibility
public import CFSG.Open.QuasithinDefs
public import CFSG.RankThree.CentralLift.ClassicalScalarCover
public import CFSG.RankThree.CentralLiftSO.SplitTorusWeyl
public import TauCeti.LinearAlgebra.CliffordAlgebra.Monomials

public section

namespace CFSG.StandardType.USixTwo

open CFSG.Assembly CFSG.Open Matrix
open scoped commutatorElement
open CFSG.ComponentClassification.CatalogueBOrthogonalPointData
open CFSG.ComponentClassification.CatalogueBOrthogonalSemilinear

variable {K : Type} [Field K]

@[expose] noncomputable def blockFourU (hK : Nat.card K = 4) :
    Subgroup (LargeEvenProj (LargeEvenSUGroup (Fin 6) K (2 ^ 1))) :=
  (CFSG.SeitzReduction.UnitaryPilot.unitaryBlock (fieldDataFour hK)
    ({0, 1}ᶜ : Finset (Fin 6))).map (LargeEvenProjMk _)

abbrev tvRadicalSix (hK : Nat.card K = 4) :
    Subgroup (LargeEvenSUGroup (Fin 6) K (2 ^ 1)) :=
  CFSG.SeitzReduction.UnitaryPilot.tvRadical (fieldDataFour hK)
    (by decide : (0 : Fin 6) ≠ 1)

abbrev tvBlockSix (hK : Nat.card K = 4) :
    Subgroup (LargeEvenSUGroup (Fin 6) K (2 ^ 1)) :=
  CFSG.SeitzReduction.UnitaryPilot.unitaryBlock (fieldDataFour hK) ({0, 1}ᶜ : Finset (Fin 6))

@[expose] noncomputable def largeEvenProjEquiv (hK : Nat.card K = 4) :
    CFSG.ClassicalGroups.UnitaryFlag.unitaryPSU (fieldDataFour hK) 6 ≃*
      LargeEvenProj (LargeEvenSUGroup (Fin 6) K (2 ^ 1)) :=
  CFSG.ClassicalGroups.UnitaryFlag.unitaryPSUEquiv (fieldDataFour hK) (by norm_num)

theorem largeEvenProjEquiv_unitaryProj (hK : Nat.card K = 4)
    (g : CFSG.ClassicalGroups.UnitaryFlag.unitarySU 2 1 K 6) :
    largeEvenProjEquiv hK
        (CFSG.ClassicalGroups.UnitaryFlag.unitaryProj (fieldDataFour hK) 6 g) =
      LargeEvenProjMk _ g := by
  show (CFSG.ClassicalGroups.UnitaryFlag.unitaryPSUEquiv (fieldDataFour hK) (by norm_num)
      (CFSG.ClassicalGroups.UnitaryFlag.unitaryProj (fieldDataFour hK) 6 g)) = _
  rw [CFSG.ClassicalGroups.UnitaryFlag.unitaryPSUEquiv_unitaryProj]
  rfl

theorem largeEvenProjEquiv_comp_unitaryProj (hK : Nat.card K = 4) :
    (largeEvenProjEquiv hK).toMonoidHom.comp
      (CFSG.ClassicalGroups.UnitaryFlag.unitaryProj (fieldDataFour hK) 6) =
      LargeEvenProjMk (LargeEvenSUGroup (Fin 6) K (2 ^ 1)) := by
  ext g
  exact largeEvenProjEquiv_unitaryProj hK g

theorem tZeroSU_eq_tvTransSU (hK : Nat.card K = 4) :
    tZeroSU hK = CFSG.SeitzReduction.UnitaryPilot.tvTransSU (fieldDataFour hK)
      (by decide : (0 : Fin 6) ≠ 1) := by
  haveI := charP_two_of_card_four hK
  refine Subtype.ext (Units.ext (Matrix.ext fun a b => ?_))
  rw [tZeroSU, CFSG.SeitzReduction.UnitaryPilot.coe_permSU,
    CFSG.SeitzReduction.UnitaryPilot.coe_tvTransSU]
  fin_cases a <;> fin_cases b <;>
    simp [Equiv.Perm.permMatrix, PEquiv.toMatrix_apply, Equiv.toPEquiv_apply,
      Equiv.swap_apply_def, CFSG.SeitzReduction.UnitaryPilot.tvE,
      CFSG.SeitzReduction.UnitaryPilot.tvNil,
      CFSG.SeitzReduction.UnitaryPilot.tvVec, Matrix.one_apply, Matrix.vecMulVec_apply,
      CharTwo.add_self_eq_zero, Pi.single_apply] <;> decide

theorem tZero_eq_largeEvenProjEquiv_stdTransvection (hK : Nat.card K = 4) :
    tZero hK = largeEvenProjEquiv hK
      (CFSG.SeitzReduction.UnitaryPilot.stdTransvection (fieldDataFour hK)
        (by decide : (0 : Fin 6) ≠ 1)) := by
  rw [tZero, CFSG.SeitzReduction.UnitaryPilot.stdTransvection,
    tZeroSU_eq_tvTransSU]
  exact (largeEvenProjEquiv_unitaryProj hK _).symm

theorem blockFourU_eq_map_blockSU (hK : Nat.card K = 4) :
    blockFourU hK = (CFSG.SeitzReduction.UnitaryPilot.blockSU (fieldDataFour hK)
      ({0, 1}ᶜ : Finset (Fin 6))).map (largeEvenProjEquiv hK).toMonoidHom := by
  rw [blockFourU]
  show Subgroup.map (LargeEvenProjMk (LargeEvenSUGroup (Fin 6) K (2 ^ 1))) (tvBlockSix hK) =
    Subgroup.map (largeEvenProjEquiv hK).toMonoidHom
      (Subgroup.map (CFSG.ClassicalGroups.UnitaryFlag.unitaryProj (fieldDataFour hK) 6)
        (tvBlockSix hK))
  rw [Subgroup.map_map, largeEvenProjEquiv_comp_unitaryProj]
  rfl

theorem isSimpleGroup_of_center_eq_bot {G : Type*} [Group G]
    (hZ : Subgroup.center G = ⊥)
    (h : IsSimpleGroup (G ⧸ Subgroup.center G)) : IsSimpleGroup G := by
  haveI : Nontrivial G :=
    Function.Surjective.nontrivial (QuotientGroup.mk'_surjective (Subgroup.center G))
  refine IsSimpleGroup.mk ?_
  intro H hH
  have hmapNormal : (H.map (QuotientGroup.mk' (Subgroup.center G))).Normal :=
    hH.map _ (QuotientGroup.mk'_surjective _)
  rcases Subgroup.Normal.eq_bot_or_eq_top (H.map (QuotientGroup.mk' (Subgroup.center G)))
    with hbot | htop
  · left
    rw [eq_bot_iff]
    intro x hx
    have hx' : QuotientGroup.mk' (Subgroup.center G) x ∈
        H.map (QuotientGroup.mk' (Subgroup.center G)) :=
      Subgroup.mem_map_of_mem _ hx
    rw [hbot, Subgroup.mem_bot] at hx'
    rw [← MonoidHom.mem_ker, QuotientGroup.ker_mk', hZ, Subgroup.mem_bot] at hx'
    exact hx'
  · right
    rw [eq_top_iff]
    intro x _
    have hx' : QuotientGroup.mk' (Subgroup.center G) x ∈
        H.map (QuotientGroup.mk' (Subgroup.center G)) := by
      rw [htop]; exact Subgroup.mem_top _
    rw [Subgroup.mem_map] at hx'
    obtain ⟨y, hy, hxy⟩ := hx'
    have hker : x * y⁻¹ ∈ (QuotientGroup.mk' (Subgroup.center G)).ker := by
      rw [MonoidHom.mem_ker, map_mul, map_inv, hxy, mul_inv_cancel]
    rw [QuotientGroup.ker_mk', hZ, Subgroup.mem_bot] at hker
    have : x = y := mul_inv_eq_one.mp hker
    rwa [this]

theorem card_unitarySU_four (hK : Nat.card K = 4) :
    Nat.card (CFSG.ClassicalGroups.UnitaryFlag.unitarySU 2 1 K 4) = 25920 := by
  have h := CFSG.ClassicalInvolution.Asc77.SCH.card_statedSU_four (K := K) (ℓ := 2) (f := 1)
    (fieldDataFour hK)
  norm_num at h ⊢
  exact h

theorem center_unitarySU_four_card (hK : Nat.card K = 4) :
    Nat.card (Subgroup.center (CFSG.ClassicalGroups.UnitaryFlag.unitarySU 2 1 K 4)) = 1 := by
  rw [CFSG.SeitzReduction.UnitaryPilot.center_unitarySU_eq_unitaryScalars (fieldDataFour hK) 4,
    CFSG.ClassicalGroups.UnitaryFlag.card_unitaryScalars (fieldDataFour hK) (by norm_num)]
  norm_num

theorem center_blockSU_eq_bot (hK : Nat.card K = 4) :
    Subgroup.center (CFSG.SeitzReduction.UnitaryPilot.blockSU (fieldDataFour hK)
      ({0, 1}ᶜ : Finset (Fin 6))) = ⊥ := by
  have hJ : ({0, 1}ᶜ : Finset (Fin 6)).card < 6 := by decide
  have hJ4 : ({0, 1}ᶜ : Finset (Fin 6)).card = 4 := by decide
  obtain ⟨e⟩ := CFSG.SeitzReduction.UnitaryPilot.blockSU_mulEquiv (fieldDataFour hK)
    ({0, 1}ᶜ : Finset (Fin 6)) hJ
  have hcard : Nat.card (Subgroup.center (CFSG.SeitzReduction.UnitaryPilot.blockSU
      (fieldDataFour hK) ({0, 1}ᶜ : Finset (Fin 6)))) = 1 := by
    have h := Nat.card_congr (Subgroup.centerCongr e).toEquiv
    rw [hJ4] at h
    rw [h, center_unitarySU_four_card hK]
  exact (Subgroup.card_eq_one).mp hcard

theorem isSimpleGroup_blockSU (hK : Nat.card K = 4) :
    IsSimpleGroup (CFSG.SeitzReduction.UnitaryPilot.blockSU (fieldDataFour hK)
      ({0, 1}ᶜ : Finset (Fin 6))) := by
  have hq := CFSG.SeitzReduction.UnitaryPilot.isQuasisimple_unitarySU (fieldDataFour hK)
    (m := 4) (by norm_num) (by decide)
  obtain ⟨e⟩ := CFSG.SeitzReduction.UnitaryPilot.blockSU_mulEquiv (fieldDataFour hK)
    ({0, 1}ᶜ : Finset (Fin 6)) (by decide : ({0, 1}ᶜ : Finset (Fin 6)).card < 6)
  have hq' : CFSG.IsQuasisimple (CFSG.SeitzReduction.UnitaryPilot.blockSU (fieldDataFour hK)
      ({0, 1}ᶜ : Finset (Fin 6))) :=
    CFSG.LieType.Universal.Unitary.isQuasisimple_of_mulEquiv e.symm hq
  exact isSimpleGroup_of_center_eq_bot (center_blockSU_eq_bot hK) hq'.2.1

noncomputable abbrev TvCore.sZ (hK : Nat.card K = 4) :
    CFSG.ClassicalGroups.UnitaryFlag.unitarySU 2 1 K 6 :=
  CFSG.SeitzReduction.UnitaryPilot.tvTransSU (fieldDataFour hK) (by decide : (0 : Fin 6) ≠ 1)

noncomputable abbrev TvCore.uZ (hK : Nat.card K = 4) :
    CFSG.ClassicalGroups.UnitaryFlag.unitaryPSU (fieldDataFour hK) 6 :=
  CFSG.SeitzReduction.UnitaryPilot.stdTransvection (fieldDataFour hK)
    (by decide : (0 : Fin 6) ≠ 1)

abbrev TvCore.Q (hK : Nat.card K = 4) :
    Subgroup (CFSG.ClassicalGroups.UnitaryFlag.unitaryPSU (fieldDataFour hK) 6) :=
  CFSG.SeitzReduction.UnitaryPilot.stdTransvectionRadical (fieldDataFour hK)
    (by decide : (0 : Fin 6) ≠ 1)

abbrev TvCore.B (hK : Nat.card K = 4) :
    Subgroup (CFSG.ClassicalGroups.UnitaryFlag.unitaryPSU (fieldDataFour hK) 6) :=
  CFSG.SeitzReduction.UnitaryPilot.blockSU (fieldDataFour hK) ({0, 1}ᶜ : Finset (Fin 6))

abbrev TvCore.C (hK : Nat.card K = 4) :
    Subgroup (CFSG.ClassicalGroups.UnitaryFlag.unitaryPSU (fieldDataFour hK) 6) :=
  Subgroup.centralizer {TvCore.uZ hK}

theorem TvCore.scalar_mul_eq_smul (c : K) (M : Matrix (Fin 6) (Fin 6) K) :
    Matrix.scalar (Fin 6) c * M = c • M := by
  ext i j
  simp [Matrix.scalar, Matrix.diagonal_mul, Matrix.smul_apply]

theorem TvCore.tvBlock_smul (c : K) (M : Matrix (Fin 6) (Fin 6) K) :
    CFSG.SeitzReduction.UnitaryPilot.tvBlock 0 1 (c • M) =
      c • CFSG.SeitzReduction.UnitaryPilot.tvBlock 0 1 M := by
  ext i j
  simp [CFSG.SeitzReduction.UnitaryPilot.tvBlock_apply, Matrix.smul_apply]

theorem TvCore.exists_scalar_mul_mem_sup (hK : Nat.card K = 4)
    {g : CFSG.ClassicalGroups.UnitaryFlag.unitarySU 2 1 K 6}
    (hg : g ∈ Subgroup.centralizer {TvCore.sZ hK}) :
    ∃ z : CFSG.ClassicalGroups.UnitaryFlag.unitarySU 2 1 K 6,
      z ∈ CFSG.ClassicalGroups.UnitaryFlag.unitaryScalars (fieldDataFour hK) 6 ∧
        z * g ∈ CFSG.SeitzReduction.UnitaryPilot.unitaryBlock (fieldDataFour hK)
            ({0, 1}ᶜ : Finset (Fin 6)) ⊔
          CFSG.SeitzReduction.UnitaryPilot.tvRadical (fieldDataFour hK)
            (by decide : (0 : Fin 6) ≠ 1) := by
  haveI : Finite K := (fieldDataFour hK).finite
  set h := fieldDataFour hK with hh
  set hij : (0 : Fin 6) ≠ 1 := by decide
  have hsZ : TvCore.sZ hK = CFSG.SeitzReduction.UnitaryPilot.tvTransSU h hij := rfl
  rw [hsZ] at hg
  set J : Finset (Fin 6) := {0, 1}ᶜ with hJ
  set M : Matrix (Fin 6) (Fin 6) K := ((g : GL (Fin 6) K) : Matrix (Fin 6) (Fin 6) K) with hM
  set A : Matrix J J K := CFSG.SeitzReduction.UnitaryPilot.tvBlock 0 1 M with hA
  have hAu : (A.map h.bar)ᵀ * A = 1 :=
    CFSG.SeitzReduction.UnitaryPilot.barTranspose_tvBlock_mul_self h hij hg
  have hdetmap : (A.map h.bar).det = h.bar A.det := by
    rw [← RingHom.mapMatrix_apply, ← RingHom.map_det]
  have hdet_ne : A.det ≠ 0 := by
    intro h0
    have h := congrArg Matrix.det hAu
    rw [Matrix.det_mul, Matrix.det_transpose, hdetmap, h0, map_zero, zero_mul,
      Matrix.det_one] at h
    exact zero_ne_one h
  set c : K := (A.det)⁻¹ with hcdef
  have hc0 : c ≠ 0 := inv_ne_zero hdet_ne
  have hc3 : c ^ 3 = 1 := by
    have := cube_unit_eq_one hK (Units.mk0 c hc0)
    simpa using congrArg Units.val this
  have hc4 : c ^ 4 = c := by
    rw [show (4:ℕ) = 3 + 1 by norm_num, pow_add, hc3, one_mul, pow_one]
  have hc6K : c ^ 6 = 1 := by
    rw [show (6:ℕ) = 3 * 2 by norm_num, pow_mul, hc3, one_pow]
  have hc6 : (Units.mk0 c hc0) ^ 6 = 1 := by
    apply Units.ext
    rw [Units.val_pow_eq_pow_val, Units.val_one, Units.val_mk0]
    exact hc6K
  have hnorm : h.norm c = 1 := by
    rw [CFSG.LocalAnalysis.ComponentInitial.UnitaryFieldData.norm, fieldDataFour_bar hK]
    rw [show c * c ^ 2 = c ^ 3 by ring, hc3]
  have hmemS : (GeneralLinearGroup.scalar (Fin 6)) (Units.mk0 c hc0) ∈
      CFSG.ClassicalGroups.UnitaryFlag.unitarySU 2 1 K 6 :=
    CFSG.ClassicalGroups.UnitaryFlag.scalar_mem_unitarySU h (by norm_num) hnorm hc6
  let z : CFSG.ClassicalGroups.UnitaryFlag.unitarySU 2 1 K 6 :=
    ⟨(GeneralLinearGroup.scalar (Fin 6)) (Units.mk0 c hc0), hmemS⟩
  have hzZ : z ∈ CFSG.ClassicalGroups.UnitaryFlag.unitaryScalars h 6 := by
    rw [CFSG.ClassicalGroups.UnitaryFlag.mem_unitaryScalars]
    exact ⟨Units.mk0 c hc0, hnorm, hc6, rfl⟩
  have hzC : z ∈ Subgroup.centralizer {CFSG.SeitzReduction.UnitaryPilot.tvTransSU h hij} := by
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact (Subgroup.mem_center_iff.mp
      (CFSG.ClassicalGroups.UnitaryFlag.unitaryScalars_le_center h 6 hzZ)
      (CFSG.SeitzReduction.UnitaryPilot.tvTransSU h hij)).symm
  have hzgC : z * g ∈ Subgroup.centralizer {CFSG.SeitzReduction.UnitaryPilot.tvTransSU h hij} :=
    mul_mem hzC hg
  have hblock : CFSG.SeitzReduction.UnitaryPilot.tvBlock 0 1
      (((z * g : CFSG.ClassicalGroups.UnitaryFlag.unitarySU 2 1 K 6) : GL (Fin 6) K) :
        Matrix (Fin 6) (Fin 6) K) = c • A := by
    rw [Subgroup.coe_mul, Units.val_mul, GeneralLinearGroup.coe_scalar, Units.val_mk0]
    rw [TvCore.scalar_mul_eq_smul, TvCore.tvBlock_smul, hA]
  have hdet : (CFSG.SeitzReduction.UnitaryPilot.tvBlock 0 1
      (((z * g : CFSG.ClassicalGroups.UnitaryFlag.unitarySU 2 1 K 6) : GL (Fin 6) K) :
        Matrix (Fin 6) (Fin 6) K)).det = 1 := by
    rw [hblock, Matrix.det_smul]
    rw [show Fintype.card J = 4 by rw [hJ]; decide]
    rw [hc4, hcdef, inv_mul_cancel₀ hdet_ne]
  refine ⟨z, hzZ, ?_⟩
  exact CFSG.SeitzReduction.UnitaryPilot.mem_sup_of_det_tvBlock_eq_one h hij hzgC hdet

theorem TvCore.centralizer_eq_sup (hK : Nat.card K = 4) :
    TvCore.C hK = TvCore.B hK ⊔ TvCore.Q hK := by
  apply le_antisymm
  · intro x hx
    rw [show TvCore.C hK = (Subgroup.centralizer
        {CFSG.SeitzReduction.UnitaryPilot.tvTransSU (fieldDataFour hK)
          (by decide : (0 : Fin 6) ≠ 1)}).map
        (CFSG.ClassicalGroups.UnitaryFlag.unitaryProj (fieldDataFour hK) 6) from
      CFSG.SeitzReduction.UnitaryPilot.centralizer_stdTransvection (fieldDataFour hK)
        (by decide)] at hx
    obtain ⟨g, hg, rfl⟩ := hx
    obtain ⟨z, hzZ, hzg⟩ := TvCore.exists_scalar_mul_mem_sup hK hg
    have hz1 : (CFSG.ClassicalGroups.UnitaryFlag.unitaryProj (fieldDataFour hK) 6) z = 1 := by
      rw [← MonoidHom.mem_ker, CFSG.ClassicalGroups.UnitaryFlag.ker_unitaryProj]
      exact hzZ
    have hmap : (CFSG.ClassicalGroups.UnitaryFlag.unitaryProj (fieldDataFour hK) 6) (z * g) ∈
        (CFSG.SeitzReduction.UnitaryPilot.unitaryBlock (fieldDataFour hK)
          ({0, 1}ᶜ : Finset (Fin 6)) ⊔
          CFSG.SeitzReduction.UnitaryPilot.tvRadical (fieldDataFour hK)
            (by decide : (0 : Fin 6) ≠ 1)).map
          (CFSG.ClassicalGroups.UnitaryFlag.unitaryProj (fieldDataFour hK) 6) :=
      Subgroup.mem_map_of_mem _ hzg
    rw [Subgroup.map_sup] at hmap
    have hzg1 : (CFSG.ClassicalGroups.UnitaryFlag.unitaryProj (fieldDataFour hK) 6) (z * g) =
        (CFSG.ClassicalGroups.UnitaryFlag.unitaryProj (fieldDataFour hK) 6) g := by
      rw [map_mul, hz1, one_mul]
    rwa [hzg1] at hmap
  · refine sup_le ?_ ?_
    · show TvCore.B hK ≤ TvCore.C hK
      rw [show TvCore.B hK = (CFSG.SeitzReduction.UnitaryPilot.unitaryBlock (fieldDataFour hK)
          ({0, 1}ᶜ : Finset (Fin 6))).map
          (CFSG.ClassicalGroups.UnitaryFlag.unitaryProj (fieldDataFour hK) 6) from rfl]
      rw [show TvCore.C hK = (Subgroup.centralizer
          {CFSG.SeitzReduction.UnitaryPilot.tvTransSU (fieldDataFour hK)
            (by decide : (0 : Fin 6) ≠ 1)}).map
          (CFSG.ClassicalGroups.UnitaryFlag.unitaryProj (fieldDataFour hK) 6) from
        CFSG.SeitzReduction.UnitaryPilot.centralizer_stdTransvection (fieldDataFour hK) (by decide)]
      exact Subgroup.map_mono
        (CFSG.SeitzReduction.UnitaryPilot.unitaryBlock_le_centralizer_tvTransSU
          (fieldDataFour hK) (by decide : (0 : Fin 6) ≠ 1))
    · show TvCore.Q hK ≤ TvCore.C hK
      rw [show TvCore.Q hK = (CFSG.SeitzReduction.UnitaryPilot.tvRadical (fieldDataFour hK)
          (by decide : (0 : Fin 6) ≠ 1)).map
          (CFSG.ClassicalGroups.UnitaryFlag.unitaryProj (fieldDataFour hK) 6) from rfl]
      rw [show TvCore.C hK = (Subgroup.centralizer
          {CFSG.SeitzReduction.UnitaryPilot.tvTransSU (fieldDataFour hK)
            (by decide : (0 : Fin 6) ≠ 1)}).map
          (CFSG.ClassicalGroups.UnitaryFlag.unitaryProj (fieldDataFour hK) 6) from
        CFSG.SeitzReduction.UnitaryPilot.centralizer_stdTransvection (fieldDataFour hK) (by decide)]
      exact Subgroup.map_mono
        (CFSG.SeitzReduction.UnitaryPilot.tvRadical_le_centralizer
          (fieldDataFour hK) (by decide : (0 : Fin 6) ≠ 1))

theorem TvCore.Q_le_C (hK : Nat.card K = 4) : TvCore.Q hK ≤ TvCore.C hK := by
  rw [show TvCore.Q hK = (CFSG.SeitzReduction.UnitaryPilot.tvRadical (fieldDataFour hK)
      (by decide : (0 : Fin 6) ≠ 1)).map
      (CFSG.ClassicalGroups.UnitaryFlag.unitaryProj (fieldDataFour hK) 6) from rfl]
  rw [show TvCore.C hK = (Subgroup.centralizer
      {CFSG.SeitzReduction.UnitaryPilot.tvTransSU (fieldDataFour hK)
        (by decide : (0 : Fin 6) ≠ 1)}).map
      (CFSG.ClassicalGroups.UnitaryFlag.unitaryProj (fieldDataFour hK) 6) from
    CFSG.SeitzReduction.UnitaryPilot.centralizer_stdTransvection (fieldDataFour hK) (by decide)]
  exact Subgroup.map_mono
    (CFSG.SeitzReduction.UnitaryPilot.tvRadical_le_centralizer
      (fieldDataFour hK) (by decide : (0 : Fin 6) ≠ 1))

theorem TvCore.C_le_normalizer_Q (hK : Nat.card K = 4) :
    TvCore.C hK ≤ Subgroup.normalizer ((TvCore.Q hK : Set _)) := by
  rw [show TvCore.Q hK = (CFSG.SeitzReduction.UnitaryPilot.tvRadical (fieldDataFour hK)
      (by decide : (0 : Fin 6) ≠ 1)).map
      (CFSG.ClassicalGroups.UnitaryFlag.unitaryProj (fieldDataFour hK) 6) from rfl]
  rw [show TvCore.C hK = (Subgroup.centralizer
      {CFSG.SeitzReduction.UnitaryPilot.tvTransSU (fieldDataFour hK)
        (by decide : (0 : Fin 6) ≠ 1)}).map
      (CFSG.ClassicalGroups.UnitaryFlag.unitaryProj (fieldDataFour hK) 6) from
    CFSG.SeitzReduction.UnitaryPilot.centralizer_stdTransvection (fieldDataFour hK) (by decide)]
  exact (Subgroup.map_mono
    (CFSG.SeitzReduction.UnitaryPilot.centralizer_le_normalizer_tvRadical
      (fieldDataFour hK) (by decide : (0 : Fin 6) ≠ 1))).trans
    (Subgroup.le_normalizer_map _)

theorem TvCore.card_blockSU (hK : Nat.card K = 4) : Nat.card (TvCore.B hK) = 25920 := by
  obtain ⟨e⟩ := CFSG.SeitzReduction.UnitaryPilot.blockSU_mulEquiv (fieldDataFour hK)
    ({0, 1}ᶜ : Finset (Fin 6)) (by decide : ({0, 1}ᶜ : Finset (Fin 6)).card < 6)
  rw [Nat.card_congr e.toEquiv]
  exact card_unitarySU_four hK

theorem TvCore.exists_mul_of_mem_sup_of_normal_subgroup {G : Type*} [Group G]
    {B Q C : Subgroup G} (hB : B ≤ C) (hQ : Q ≤ C) (hC : B ⊔ Q = C)
    (hQn : C ≤ Subgroup.normalizer (Q : Set G)) {p : G} (hp : p ∈ C) :
    ∃ b ∈ B, ∃ q ∈ Q, b * q = p := by
  have hconj : ∀ c ∈ C, ∀ q ∈ Q, c * q * c⁻¹ ∈ Q := by
    intro c hc q hq
    exact (Subgroup.mem_normalizer_iff.mp (hQn hc) q).mp hq
  let Tset : Set G := {x | x ∈ C ∧ ∃ b ∈ B, ∃ q ∈ Q, b * q = x}
  let T : Subgroup G :=
    { carrier := Tset,
      one_mem' := ⟨one_mem C, 1, one_mem B, 1, one_mem Q, one_mul 1⟩,
      mul_mem' := by
        rintro x y ⟨hxC, b₁, hb₁, q₁, hq₁, rfl⟩ ⟨hyC, b₂, hb₂, q₂, hq₂, rfl⟩
        have hq' : b₂⁻¹ * q₁ * b₂ ∈ Q := by
          simpa using hconj b₂⁻¹ (inv_mem (hB hb₂)) q₁ hq₁
        refine ⟨mul_mem hxC hyC, b₁ * b₂, mul_mem hb₁ hb₂, (b₂⁻¹ * q₁ * b₂) * q₂,
          mul_mem hq' hq₂, ?_⟩
        group,
      inv_mem' := by
        rintro x ⟨hxC, b, hb, q, hq, rfl⟩
        have hq' : b * q⁻¹ * b⁻¹ ∈ Q := hconj b (hB hb) q⁻¹ (inv_mem hq)
        refine ⟨inv_mem hxC, b⁻¹, inv_mem hb, b * q⁻¹ * b⁻¹, hq', ?_⟩
        group }
  have hT : B ⊔ Q ≤ T := by
    refine sup_le ?_ ?_
    · intro x hx
      exact ⟨hB hx, x, hx, 1, one_mem Q, mul_one x⟩
    · intro x hx
      exact ⟨hQ hx, 1, one_mem B, x, hx, one_mul x⟩
  have hpT : p ∈ T := hT (hC ▸ hp)
  exact hpT.2

theorem TvCore.inf_normal_subgroupOf {G : Type*} [Group G]
    {P B C : Subgroup G} (hB : B ≤ C) (hP : C ≤ Subgroup.normalizer (P : Set G)) :
    ((P ⊓ B).subgroupOf B).Normal := by
  rw [Subgroup.normal_subgroupOf_iff_le_normalizer inf_le_right]
  intro b hb
  rw [Subgroup.mem_normalizer_iff]
  intro x
  constructor
  · rintro ⟨hxP, hxB⟩
    exact ⟨(Subgroup.mem_normalizer_iff.mp (hP (hB hb)) x).mp hxP,
      mul_mem (mul_mem hb hxB) (B.inv_mem hb)⟩
  · rintro ⟨hxP, hxB⟩
    have hbC : b ∈ C := hB hb
    refine ⟨?_, ?_⟩
    · have := (Subgroup.mem_normalizer_iff.mp (hP (inv_mem hbC)) (b * x * b⁻¹)).mp hxP
      simpa [mul_assoc] using this
    · have := mul_mem (mul_mem (B.inv_mem hb) hxB) hb
      simpa [mul_assoc] using this

theorem TvCore.pCoreOf_eq_Q (hK : Nat.card K = 4) :
    pCoreOf 2 (TvCore.C hK) = TvCore.Q hK := by
  haveI : Finite K := (fieldDataFour hK).finite
  have hQC : TvCore.Q hK ≤ TvCore.C hK := TvCore.Q_le_C hK
  have hQnorm : TvCore.C hK ≤ Subgroup.normalizer ((TvCore.Q hK : Set _)) :=
    TvCore.C_le_normalizer_Q hK
  have hQp : IsPGroup 2 (TvCore.Q hK) := by
    rw [show TvCore.Q hK = (CFSG.SeitzReduction.UnitaryPilot.tvRadical (fieldDataFour hK)
        (by decide : (0 : Fin 6) ≠ 1)).map
        (CFSG.ClassicalGroups.UnitaryFlag.unitaryProj (fieldDataFour hK) 6) from rfl]
    exact CFSG.SeitzReduction.UnitaryPilot.isPGroup_stdTransvectionRadical
      (fieldDataFour hK) (by decide : (0 : Fin 6) ≠ 1)
  have hQleP : TvCore.Q hK ≤ pCoreOf 2 (TvCore.C hK) :=
    CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 hQC hQnorm hQp
  have hPp : IsPGroup 2 (pCoreOf 2 (TvCore.C hK)) :=
    CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 _
  have hBC : TvCore.B hK ≤ TvCore.C hK := by
    rw [TvCore.centralizer_eq_sup hK]; exact le_sup_left
  have hPnorm : TvCore.C hK ≤ Subgroup.normalizer ((pCoreOf 2 (TvCore.C hK) : Set _)) :=
    CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 (TvCore.C hK)
  have hPBnormal : ((pCoreOf 2 (TvCore.C hK) ⊓ TvCore.B hK).subgroupOf
      (TvCore.B hK)).Normal := TvCore.inf_normal_subgroupOf hBC hPnorm
  have hPBbot : pCoreOf 2 (TvCore.C hK) ⊓ TvCore.B hK = ⊥ := by
    haveI : IsSimpleGroup (TvCore.B hK) := isSimpleGroup_blockSU hK
    haveI : ((pCoreOf 2 (TvCore.C hK) ⊓ TvCore.B hK).subgroupOf (TvCore.B hK)).Normal :=
      hPBnormal
    rcases Subgroup.Normal.eq_bot_or_eq_top ((pCoreOf 2 (TvCore.C hK) ⊓ TvCore.B hK).subgroupOf
      (TvCore.B hK)) with hbot | htop
    · apply le_antisymm _ bot_le
      intro x hx
      have hxH : (⟨x, hx.2⟩ : TvCore.B hK) ∈
          (pCoreOf 2 (TvCore.C hK) ⊓ TvCore.B hK).subgroupOf (TvCore.B hK) := by
        rw [Subgroup.mem_subgroupOf]; exact hx
      rw [hbot, Subgroup.mem_bot] at hxH
      exact Subtype.ext_iff.mp hxH
    · exfalso
      have hBleP : TvCore.B hK ≤ pCoreOf 2 (TvCore.C hK) := by
        intro x hx
        have hxH : (⟨x, hx⟩ : TvCore.B hK) ∈
            (pCoreOf 2 (TvCore.C hK) ⊓ TvCore.B hK).subgroupOf (TvCore.B hK) := by
          rw [htop]; exact Subgroup.mem_top _
        exact hxH.1
      have hBp : IsPGroup 2 (TvCore.B hK) := hPp.to_le hBleP
      have hcard2 : Nat.card (TvCore.B hK) = 2 :=
        (IsPGroup.isSimpleGroup_iff_card_eq (p := 2) (G := TvCore.B hK) hBp).mp inferInstance
      have hcard : Nat.card (TvCore.B hK) = 25920 := TvCore.card_blockSU hK
      omega
  refine le_antisymm ?_ hQleP
  intro p hp
  have hpC : p ∈ TvCore.C hK := CFSG.LieType.BorelTits.pCoreOf_le 2 _ hp
  have hQC' : TvCore.Q hK ≤ TvCore.C hK := hQC
  obtain ⟨b, hbB, q, hqQ, hbq⟩ := TvCore.exists_mul_of_mem_sup_of_normal_subgroup
    hBC hQC' (TvCore.centralizer_eq_sup hK).symm hQnorm hpC
  have hbP : b ∈ pCoreOf 2 (TvCore.C hK) := by
    have : b = p * q⁻¹ := by rw [← hbq]; group
    rw [this]
    exact mul_mem hp (inv_mem (hQleP hqQ))
  have hbBot : b ∈ pCoreOf 2 (TvCore.C hK) ⊓ TvCore.B hK := ⟨hbP, hbB⟩
  rw [hPBbot, Subgroup.mem_bot] at hbBot
  rw [← hbq, hbBot, one_mul]
  exact hqQ

abbrev TvCore.R (hK : Nat.card K = 4) :
    Subgroup (CFSG.ClassicalGroups.UnitaryFlag.unitarySU 2 1 K 6) :=
  CFSG.SeitzReduction.UnitaryPilot.tvRadical (fieldDataFour hK) (by decide : (0 : Fin 6) ≠ 1)

abbrev TvCore.Adm (hK : Nat.card K = 4) : Type :=
  {p : (Fin 6 → K) × K //
    p.1 0 = 0 ∧ p.1 1 = 0 ∧ p.2 + (fieldDataFour hK).bar p.2 =
      CFSG.SeitzReduction.UnitaryPilot.tvBar (fieldDataFour hK) p.1 ⬝ᵥ p.1}

theorem TvCore.tvESU_param_eq (hK : Nat.card K = 4)
    {x x' : Fin 6 → K} {s s' : K}
    {hxs : CFSG.SeitzReduction.UnitaryPilot.TvAdm (fieldDataFour hK) (0 : Fin 6) 1 x s}
    {hxs' : CFSG.SeitzReduction.UnitaryPilot.TvAdm (fieldDataFour hK) (0 : Fin 6) 1 x' s'}
    (he : CFSG.SeitzReduction.UnitaryPilot.tvESU (fieldDataFour hK)
      (by decide : (0 : Fin 6) ≠ 1) x s hxs =
      CFSG.SeitzReduction.UnitaryPilot.tvESU (fieldDataFour hK)
        (by decide : (0 : Fin 6) ≠ 1) x' s' hxs') :
    x = x' ∧ s = s' := by
  have hm := congrArg (fun g : CFSG.ClassicalGroups.UnitaryFlag.unitarySU 2 1 K 6 =>
    ((g : GL (Fin 6) K) : Matrix (Fin 6) (Fin 6) K)) he
  simp only [CFSG.SeitzReduction.UnitaryPilot.coe_tvESU] at hm
  have hentry : ∀ a, CFSG.SeitzReduction.UnitaryPilot.tvE (fieldDataFour hK) 0 1 x s a 0 =
      CFSG.SeitzReduction.UnitaryPilot.tvE (fieldDataFour hK) 0 1 x' s' a 0 := fun a =>
    congrFun (congrFun hm a) 0
  refine ⟨funext fun a => ?_, ?_⟩
  · by_cases ha0 : a = 0
    · rw [ha0, hxs.1, hxs'.1]
    · by_cases ha1 : a = 1
      · rw [ha1, hxs.2.1, hxs'.2.1]
      · have h := hentry a
        have hva : CFSG.SeitzReduction.UnitaryPilot.tvVec (K := K) (0 : Fin 6) 1 a = 0 := by
          simp [CFSG.SeitzReduction.UnitaryPilot.tvVec_apply, ha0, ha1]
        simpa [CFSG.SeitzReduction.UnitaryPilot.tvE_apply,
          Matrix.one_apply_ne (Ne.symm ha0), hva,
          CFSG.SeitzReduction.UnitaryPilot.tvVec_left (by decide : (0 : Fin 6) ≠ 1)] using h
  · have h := hentry 1
    simpa [CFSG.SeitzReduction.UnitaryPilot.tvE_apply,
      Matrix.one_apply_ne (by decide : (1 : Fin 6) ≠ 0),
      CFSG.SeitzReduction.UnitaryPilot.tvVec_left (by decide : (0 : Fin 6) ≠ 1),
      CFSG.SeitzReduction.UnitaryPilot.tvVec_right (by decide : (0 : Fin 6) ≠ 1),
      hxs.1, hxs'.1, hxs.2.1, hxs'.2.1] using h

noncomputable def TvCore.admEquivR (hK : Nat.card K = 4) : TvCore.Adm hK ≃ TvCore.R hK := by
  refine Equiv.ofBijective
    (fun p => (⟨CFSG.SeitzReduction.UnitaryPilot.tvESU (fieldDataFour hK)
        (by decide : (0 : Fin 6) ≠ 1) p.1.1 p.1.2 p.2,
      CFSG.SeitzReduction.UnitaryPilot.tvESU_mem_tvRadical (fieldDataFour hK)
        (by decide : (0 : Fin 6) ≠ 1) p.2⟩ : TvCore.R hK)) ?_
  constructor
  · intro p q hpq
    have h := TvCore.tvESU_param_eq hK (x := p.1.1) (s := p.1.2) (hxs := p.2)
      (x' := q.1.1) (s' := q.1.2) (hxs' := q.2) (congrArg Subtype.val hpq)
    rcases h with ⟨hx, hs⟩
    exact Subtype.ext (Prod.ext hx hs)
  · intro r
    obtain ⟨x, s, hxs, hr⟩ :=
      CFSG.SeitzReduction.UnitaryPilot.exists_eq_tvESU_of_mem_tvRadical
        (fieldDataFour hK) (by decide : (0 : Fin 6) ≠ 1) r.2
    refine ⟨⟨(x, s), hxs⟩, ?_⟩
    exact Subtype.ext hr.symm

abbrev TvCore.X (hK : Nat.card K = 4) : Type :=
  {x : Fin 6 → K // x 0 = 0 ∧ x 1 = 0}

noncomputable def TvCore.XEquivJ (hK : Nat.card K = 4) :
    TvCore.X hK ≃ (({0, 1}ᶜ : Finset (Fin 6)) → K) where
  toFun x := fun j => x.1 j
  invFun f := ⟨fun a => if h : a ∈ ({0, 1}ᶜ : Finset (Fin 6)) then f ⟨a, h⟩ else 0,
    by
      show (if h : (0 : Fin 6) ∈ ({0, 1}ᶜ : Finset (Fin 6)) then f ⟨0, h⟩ else 0) = 0
      rw [dif_neg (show (0 : Fin 6) ∉ ({0, 1}ᶜ : Finset (Fin 6)) by decide)],
    by
      show (if h : (1 : Fin 6) ∈ ({0, 1}ᶜ : Finset (Fin 6)) then f ⟨1, h⟩ else 0) = 0
      rw [dif_neg (show (1 : Fin 6) ∉ ({0, 1}ᶜ : Finset (Fin 6)) by decide)]⟩
  left_inv x := by
    ext a
    show (if h : a ∈ ({0, 1}ᶜ : Finset (Fin 6)) then x.1 a else 0) = x.1 a
    by_cases ha : a ∈ ({0, 1}ᶜ : Finset (Fin 6))
    · rw [dif_pos ha]
    · rw [dif_neg ha]
      have hmem : a ∈ ({0, 1} : Finset (Fin 6)) := by
        by_contra h
        exact ha (by simpa [Finset.mem_compl] using h)
      rcases Finset.mem_insert.mp hmem with h | h
      · rw [h, x.2.1]
      · have ha1 : a = 1 := by simpa using h
        rw [ha1, x.2.2]
  right_inv f := by
    ext j
    show (if h : (j : Fin 6) ∈ ({0, 1}ᶜ : Finset (Fin 6)) then f ⟨j, h⟩ else 0) = f j
    rw [dif_pos j.2]

theorem TvCore.card_X (hK : Nat.card K = 4) : Nat.card (TvCore.X hK) = 4 ^ 4 := by
  rw [Nat.card_congr (TvCore.XEquivJ hK), Nat.card_fun, hK]
  rw [show Nat.card ({0, 1}ᶜ : Finset (Fin 6)) = 4 by
    rw [Nat.card_eq_fintype_card]; decide]

noncomputable def TvCore.trHom (hK : Nat.card K = 4) : K →+ K :=
  (AddMonoidHom.id K) + (fieldDataFour hK).bar.toAddMonoidHom

theorem TvCore.trHom_apply (hK : Nat.card K = 4) (s : K) :
    TvCore.trHom hK s = s + (fieldDataFour hK).bar s := by
  simp [TvCore.trHom]

theorem TvCore.mem_trHom_ker (hK : Nat.card K = 4) {s : K} :
    s ∈ (TvCore.trHom hK).ker ↔ s = 0 ∨ s = 1 := by
  haveI := charP_two_of_card_four hK
  rw [AddMonoidHom.mem_ker, TvCore.trHom_apply, add_eq_zero_iff_eq_neg]
  constructor
  · intro h
    have hbar : (fieldDataFour hK).bar s = s := by
      have h1 : (fieldDataFour hK).bar s = -s := by linear_combination h
      rw [h1, CharTwo.neg_eq]
    rw [fieldDataFour_bar hK] at hbar
    have hfac : s * (s - 1) = 0 := by linear_combination hbar
    rcases mul_eq_zero.mp hfac with h0 | h1
    · exact Or.inl h0
    · exact Or.inr (sub_eq_zero.mp h1)
  · rintro (rfl | rfl)
    · simp
    · simp [fieldDataFour_bar hK, CharTwo.neg_eq, one_add_one_eq_zero hK]

noncomputable def TvCore.trKerEquivFin2 (hK : Nat.card K = 4) :
    (TvCore.trHom hK).ker ≃ Fin 2 := by
  classical
  exact
    { toFun := fun s => if (s : K) = 0 then 0 else 1
      invFun := fun i => if i = 0 then ⟨0, by simp [TvCore.trHom]⟩ else
        ⟨1, by
          rw [AddMonoidHom.mem_ker, TvCore.trHom_apply, fieldDataFour_bar hK, one_pow,
            one_add_one_eq_zero hK]⟩
      left_inv := by
        intro s
        rcases (TvCore.mem_trHom_ker hK).mp s.2 with h0 | h1
        · apply Subtype.ext
          simp [h0]
        · apply Subtype.ext
          simp [h1]
      right_inv := by
        intro i
        fin_cases i <;> simp }

theorem TvCore.card_trKer (hK : Nat.card K = 4) :
    Nat.card (TvCore.trHom hK).ker = 2 := by
  rw [Nat.card_congr (TvCore.trKerEquivFin2 hK)]
  simp

noncomputable def TvCore.omegaSix (hK : Nat.card K = 4) : K :=
  letI : Finite K := (fieldDataFour hK).finite
  Classical.choose (exists_root_omega hK)

theorem TvCore.omegaSix_spec (hK : Nat.card K = 4) :
    (TvCore.omegaSix hK) ^ 2 + TvCore.omegaSix hK + 1 = 0 := by
  letI : Finite K := (fieldDataFour hK).finite
  exact Classical.choose_spec (exists_root_omega hK)

noncomputable def TvCore.s0 (hK : Nat.card K = 4) (x : TvCore.X hK) : K := by
  classical
  exact if CFSG.SeitzReduction.UnitaryPilot.tvBar (fieldDataFour hK) x.1 ⬝ᵥ x.1 = 0 then 0
    else TvCore.omegaSix hK

theorem TvCore.bar_dotProduct_tvBar_self (hK : Nat.card K = 4) (x : Fin 6 → K) :
    (fieldDataFour hK).bar
      (CFSG.SeitzReduction.UnitaryPilot.tvBar (fieldDataFour hK) x ⬝ᵥ x) =
      CFSG.SeitzReduction.UnitaryPilot.tvBar (fieldDataFour hK) x ⬝ᵥ x := by
  simp only [dotProduct, map_sum, map_mul, CFSG.SeitzReduction.UnitaryPilot.tvBar_apply,
    CFSG.LocalAnalysis.ComponentInitial.UnitaryFieldData.bar_bar, mul_comm]

theorem TvCore.dotProduct_tvBar_self_eq_zero_or_one (hK : Nat.card K = 4)
    (x : Fin 6 → K) :
    CFSG.SeitzReduction.UnitaryPilot.tvBar (fieldDataFour hK) x ⬝ᵥ x = 0 ∨
      CFSG.SeitzReduction.UnitaryPilot.tvBar (fieldDataFour hK) x ⬝ᵥ x = 1 := by
  set t := CFSG.SeitzReduction.UnitaryPilot.tvBar (fieldDataFour hK) x ⬝ᵥ x with ht
  have hbar := TvCore.bar_dotProduct_tvBar_self hK x
  have hsq : t ^ 2 = t := by
    rw [← fieldDataFour_bar hK t, hbar]
  have hfac : t * (t - 1) = 0 := by linear_combination hsq
  rcases mul_eq_zero.mp hfac with h | h
  · exact Or.inl h
  · exact Or.inr (sub_eq_zero.mp h)

theorem TvCore.s0_spec (hK : Nat.card K = 4) (x : TvCore.X hK) :
    TvCore.trHom hK (TvCore.s0 hK x) =
      CFSG.SeitzReduction.UnitaryPilot.tvBar (fieldDataFour hK) x.1 ⬝ᵥ x.1 := by
  letI : Finite K := (fieldDataFour hK).finite
  have hω := TvCore.omegaSix_spec hK
  by_cases h0 : CFSG.SeitzReduction.UnitaryPilot.tvBar (fieldDataFour hK) x.1 ⬝ᵥ x.1 = 0
  · simp [TvCore.s0, h0, TvCore.trHom]
  · have h1 : CFSG.SeitzReduction.UnitaryPilot.tvBar (fieldDataFour hK) x.1 ⬝ᵥ x.1 = 1 :=
      (TvCore.dotProduct_tvBar_self_eq_zero_or_one hK x.1).resolve_left h0
    have hωsum : TvCore.omegaSix hK + TvCore.omegaSix hK ^ 2 = 1 :=
      omega_add_sq hK hω
    rw [TvCore.s0, if_neg h0, TvCore.trHom_apply, fieldDataFour_bar hK, hωsum]
    exact h1.symm

noncomputable def TvCore.admEquivProd (hK : Nat.card K = 4) :
    TvCore.Adm hK ≃ TvCore.X hK × (TvCore.trHom hK).ker where
  toFun p :=
    ⟨⟨p.1.1, p.2.1, p.2.2.1⟩,
      ⟨p.1.2 + TvCore.s0 hK ⟨p.1.1, p.2.1, p.2.2.1⟩, by
        rw [AddMonoidHom.mem_ker, TvCore.trHom_apply, map_add]
        have hs : p.1.2 + (fieldDataFour hK).bar p.1.2 =
            CFSG.SeitzReduction.UnitaryPilot.tvBar (fieldDataFour hK) p.1.1 ⬝ᵥ p.1.1 :=
          p.2.2.2
        have hs0 : TvCore.s0 hK ⟨p.1.1, p.2.1, p.2.2.1⟩ +
            (fieldDataFour hK).bar (TvCore.s0 hK ⟨p.1.1, p.2.1, p.2.2.1⟩) =
            CFSG.SeitzReduction.UnitaryPilot.tvBar (fieldDataFour hK) p.1.1 ⬝ᵥ p.1.1 := by
          simpa [TvCore.trHom_apply] using
            TvCore.s0_spec hK ⟨p.1.1, p.2.1, p.2.2.1⟩
        calc
          p.1.2 + TvCore.s0 hK ⟨p.1.1, p.2.1, p.2.2.1⟩ +
              ((fieldDataFour hK).bar p.1.2 +
                (fieldDataFour hK).bar (TvCore.s0 hK ⟨p.1.1, p.2.1, p.2.2.1⟩)) =
              (p.1.2 + (fieldDataFour hK).bar p.1.2) +
                (TvCore.s0 hK ⟨p.1.1, p.2.1, p.2.2.1⟩ +
                  (fieldDataFour hK).bar (TvCore.s0 hK ⟨p.1.1, p.2.1, p.2.2.1⟩)) := by
                abel
          _ = CFSG.SeitzReduction.UnitaryPilot.tvBar (fieldDataFour hK) p.1.1 ⬝ᵥ p.1.1 +
                CFSG.SeitzReduction.UnitaryPilot.tvBar (fieldDataFour hK) p.1.1 ⬝ᵥ p.1.1 := by
                exact congrArg₂ (· + ·) hs hs0
          _ = 0 := by
                have h2 : (2 : K) = 0 := two_eq_zero hK
                linear_combination
                  (CFSG.SeitzReduction.UnitaryPilot.tvBar (fieldDataFour hK) p.1.1 ⬝ᵥ p.1.1) * h2⟩⟩
  invFun q :=
    ⟨(q.1.1, q.2.1 + TvCore.s0 hK q.1), by
      refine ⟨q.1.2.1, q.1.2.2, ?_⟩
      have hk : (q.2 : K) + (fieldDataFour hK).bar q.2 = 0 := by
        have h := q.2.2
        rw [AddMonoidHom.mem_ker, TvCore.trHom_apply] at h
        exact h
      have hs0 : TvCore.s0 hK q.1 + (fieldDataFour hK).bar (TvCore.s0 hK q.1) =
          CFSG.SeitzReduction.UnitaryPilot.tvBar (fieldDataFour hK) q.1.1 ⬝ᵥ q.1.1 := by
        simpa [TvCore.trHom_apply] using TvCore.s0_spec hK q.1
      dsimp only [Prod.fst, Prod.snd]
      rw [map_add]
      change q.2.1 + TvCore.s0 hK q.1 +
          ((fieldDataFour hK).bar q.2 + (fieldDataFour hK).bar (TvCore.s0 hK q.1)) =
          CFSG.SeitzReduction.UnitaryPilot.tvBar (fieldDataFour hK) q.1.1 ⬝ᵥ q.1.1
      calc
        q.2.1 + TvCore.s0 hK q.1 +
            ((fieldDataFour hK).bar q.2 + (fieldDataFour hK).bar (TvCore.s0 hK q.1)) =
            ((q.2 : K) + (fieldDataFour hK).bar q.2) +
              (TvCore.s0 hK q.1 + (fieldDataFour hK).bar (TvCore.s0 hK q.1)) := by
              abel
        _ = 0 + CFSG.SeitzReduction.UnitaryPilot.tvBar (fieldDataFour hK) q.1.1 ⬝ᵥ q.1.1 := by
              exact congrArg₂ (· + ·) hk hs0
        _ = CFSG.SeitzReduction.UnitaryPilot.tvBar (fieldDataFour hK) q.1.1 ⬝ᵥ q.1.1 := by
              rw [zero_add]⟩
  left_inv p := by
    apply Subtype.ext
    apply Prod.ext
    · rfl
    · show p.1.2 + TvCore.s0 hK ⟨p.1.1, p.2.1, p.2.2.1⟩ +
        TvCore.s0 hK ⟨p.1.1, p.2.1, p.2.2.1⟩ = p.1.2
      have h2 : (2 : K) = 0 := two_eq_zero hK
      have hs : TvCore.s0 hK ⟨p.1.1, p.2.1, p.2.2.1⟩ +
          TvCore.s0 hK ⟨p.1.1, p.2.1, p.2.2.1⟩ = 0 := by
        linear_combination TvCore.s0 hK ⟨p.1.1, p.2.1, p.2.2.1⟩ * h2
      rw [add_assoc, hs, add_zero]
  right_inv q := by
    apply Prod.ext
    · rfl
    · apply Subtype.ext
      show q.2.1 + TvCore.s0 hK q.1 + TvCore.s0 hK q.1 = q.2.1
      have h2 : (2 : K) = 0 := two_eq_zero hK
      have hs : TvCore.s0 hK q.1 + TvCore.s0 hK q.1 = 0 := by
        linear_combination TvCore.s0 hK q.1 * h2
      rw [add_assoc, hs, add_zero]

theorem TvCore.card_Adm (hK : Nat.card K = 4) : Nat.card (TvCore.Adm hK) = 2 ^ 9 := by
  rw [Nat.card_congr (TvCore.admEquivProd hK), Nat.card_prod,
    TvCore.card_X, TvCore.card_trKer]
  norm_num

theorem TvCore.card_R (hK : Nat.card K = 4) : Nat.card (TvCore.R hK) = 2 ^ 9 := by
  rw [← Nat.card_congr (TvCore.admEquivR hK), TvCore.card_Adm]

theorem TvCore.R_inf_ker (hK : Nat.card K = 4) :
    TvCore.R hK ⊓ (CFSG.ClassicalGroups.UnitaryFlag.unitaryProj (fieldDataFour hK) 6).ker = ⊥ := by
  ext r
  constructor
  · rintro ⟨hrR, hrK⟩
    rw [Subgroup.mem_bot]
    rw [CFSG.ClassicalGroups.UnitaryFlag.ker_unitaryProj] at hrK
    change r ∈ CFSG.ClassicalGroups.UnitaryFlag.unitaryScalars (fieldDataFour hK) 6 at hrK
    rw [CFSG.ClassicalGroups.UnitaryFlag.mem_unitaryScalars] at hrK
    obtain ⟨c, hcN, hc6, hcmat⟩ := hrK
    obtain ⟨x, s, hxs, hrx⟩ :=
      CFSG.SeitzReduction.UnitaryPilot.exists_eq_tvESU_of_mem_tvRadical
        (fieldDataFour hK) (by decide : (0 : Fin 6) ≠ 1) hrR
    have hmat : (((r : CFSG.ClassicalGroups.UnitaryFlag.unitarySU 2 1 K 6) : GL (Fin 6) K) :
        Matrix (Fin 6) (Fin 6) K) =
        CFSG.SeitzReduction.UnitaryPilot.tvE (fieldDataFour hK) 0 1 x s := by
      rw [hrx, CFSG.SeitzReduction.UnitaryPilot.coe_tvESU]
    have hscal : (((r : CFSG.ClassicalGroups.UnitaryFlag.unitarySU 2 1 K 6) : GL (Fin 6) K) :
        Matrix (Fin 6) (Fin 6) K) = Matrix.scalar (Fin 6) (c : K) := by
      rw [hcmat]
      rfl
    have hEq : CFSG.SeitzReduction.UnitaryPilot.tvE (fieldDataFour hK) 0 1 x s =
        Matrix.scalar (Fin 6) (c : K) := by
      rw [← hmat, hscal]
    have hentry : ∀ a b, CFSG.SeitzReduction.UnitaryPilot.tvE (fieldDataFour hK) 0 1 x s a b =
        Matrix.scalar (Fin 6) (c : K) a b := fun a b =>
      congrFun (congrFun hEq a) b
    have hx0 : ∀ a, a ∈ ({0, 1}ᶜ : Finset (Fin 6)) → x a = 0 := by
      intro a ha
      have ha' : a ∉ ({0, 1} : Finset (Fin 6)) := by simpa [Finset.mem_compl] using ha
      have ha0 : a ≠ 0 := fun h => ha' (by simp [h])
      have ha1 : a ≠ 1 := fun h => ha' (by simp [h])
      have h := hentry a 0
      have hv : CFSG.SeitzReduction.UnitaryPilot.tvVec (K := K) 0 1 a = 0 := by
        simp [CFSG.SeitzReduction.UnitaryPilot.tvVec_apply, ha0, ha1]
      have hv0 : CFSG.SeitzReduction.UnitaryPilot.tvVec (K := K) 0 1 0 = 1 :=
        CFSG.SeitzReduction.UnitaryPilot.tvVec_left (by decide : (0 : Fin 6) ≠ 1)
      have hone : (1 : Matrix (Fin 6) (Fin 6) K) a 0 = 0 := by
        simp [Matrix.one_apply, ha0]
      simp [CFSG.SeitzReduction.UnitaryPilot.tvE_apply, hone, hv, hv0,
        Matrix.scalar_apply, ha0] at h
      exact h
    have hs0 : s = 0 := by
      have h := hentry 1 0
      have hone : (1 : Matrix (Fin 6) (Fin 6) K) 1 0 = 0 :=
        Matrix.one_apply_ne (by decide : (1 : Fin 6) ≠ 0)
      have hv1 := CFSG.SeitzReduction.UnitaryPilot.tvVec_left
        (K := K) (i := (0 : Fin 6)) (j := 1) (by decide : (0 : Fin 6) ≠ 1)
      have hv2 := CFSG.SeitzReduction.UnitaryPilot.tvVec_right
        (K := K) (i := (0 : Fin 6)) (j := 1) (by decide : (0 : Fin 6) ≠ 1)
      simp [CFSG.SeitzReduction.UnitaryPilot.tvE_apply, hone, hv1, hv2, hxs.1,
        Matrix.scalar_apply, hxs.2.1] at h
      exact h
    have hx : x = 0 := by
      funext a
      by_cases ha : a ∈ ({0, 1}ᶜ : Finset (Fin 6))
      · exact hx0 a ha
      · have hmem : a ∈ ({0, 1} : Finset (Fin 6)) := by
          by_contra h
          exact ha (by simpa [Finset.mem_compl] using h)
        rcases Finset.mem_insert.mp hmem with h | h
        · rw [h]; exact hxs.1
        · have ha1 : a = 1 := by simpa using h
          rw [ha1]; exact hxs.2.1
    rw [hrx]
    subst hx
    subst hs0
    exact CFSG.SeitzReduction.UnitaryPilot.tvESU_zero_zero (fieldDataFour hK)
      (by decide : (0 : Fin 6) ≠ 1)
  · intro hr
    rw [Subgroup.mem_bot] at hr
    rw [hr]
    exact ⟨one_mem _, one_mem _⟩

noncomputable def TvCore.REquivQ (hK : Nat.card K = 4) :
    TvCore.R hK ≃ TvCore.Q hK := by
  refine Equiv.ofBijective
    (fun r => (⟨(CFSG.ClassicalGroups.UnitaryFlag.unitaryProj (fieldDataFour hK) 6) r,
      Subgroup.mem_map_of_mem _ r.2⟩ : TvCore.Q hK)) ?_
  constructor
  · intro r1 r2 h
    have hker : ((r1 : CFSG.ClassicalGroups.UnitaryFlag.unitarySU 2 1 K 6) *
        (r2 : CFSG.ClassicalGroups.UnitaryFlag.unitarySU 2 1 K 6)⁻¹) ∈ TvCore.R hK ⊓
        (CFSG.ClassicalGroups.UnitaryFlag.unitaryProj (fieldDataFour hK) 6).ker := by
      refine ⟨Subgroup.mul_mem (TvCore.R hK) r1.2 (Subgroup.inv_mem (TvCore.R hK) r2.2), ?_⟩
      change (CFSG.ClassicalGroups.UnitaryFlag.unitaryProj (fieldDataFour hK) 6)
        ((r1 : CFSG.ClassicalGroups.UnitaryFlag.unitarySU 2 1 K 6) *
          (r2 : CFSG.ClassicalGroups.UnitaryFlag.unitarySU 2 1 K 6)⁻¹) = 1
      rw [map_mul, map_inv]
      have hval : (CFSG.ClassicalGroups.UnitaryFlag.unitaryProj (fieldDataFour hK) 6)
          (r1 : CFSG.ClassicalGroups.UnitaryFlag.unitarySU 2 1 K 6) =
          (CFSG.ClassicalGroups.UnitaryFlag.unitaryProj (fieldDataFour hK) 6)
            (r2 : CFSG.ClassicalGroups.UnitaryFlag.unitarySU 2 1 K 6) := by
        simpa using congrArg Subtype.val h
      rw [hval]
      exact mul_inv_cancel _
    rw [TvCore.R_inf_ker hK, Subgroup.mem_bot] at hker
    exact Subtype.ext (mul_inv_eq_one.mp hker)
  · intro q
    have hq : q.1 ∈ (TvCore.R hK).map
        (CFSG.ClassicalGroups.UnitaryFlag.unitaryProj (fieldDataFour hK) 6) := by
      show q.1 ∈ TvCore.Q hK
      exact q.2
    obtain ⟨r, hr, hqr⟩ := Subgroup.mem_map.mp hq
    exact ⟨⟨r, hr⟩, Subtype.ext hqr⟩

theorem TvCore.card_Q (hK : Nat.card K = 4) : Nat.card (TvCore.Q hK) = 2 ^ 9 := by
  rw [← Nat.card_congr (TvCore.REquivQ hK), TvCore.card_R]

theorem TvCore.omega_cube (hK : Nat.card K = 4) {ω : K} (hω : ω ^ 2 + ω + 1 = 0) :
    ω ^ 2 * ω = 1 := by
  letI : Finite K := (fieldDataFour hK).finite
  have hsq : ω + ω ^ 2 = 1 := omega_add_sq hK hω
  linear_combination ω * hω + hsq - (ω ^ 2 + ω) * two_eq_zero hK

theorem TvCore.E_zero_one_not_scalar (hK : Nat.card K = 4) :
    CFSG.SeitzReduction.UnitaryPilot.tvESU (fieldDataFour hK)
      (by decide : (0 : Fin 6) ≠ 1) 0 1 (CFSG.SeitzReduction.UnitaryPilot.tvAdm_one
        (fieldDataFour hK) 0 1) ∉
      (CFSG.ClassicalGroups.UnitaryFlag.unitaryProj (fieldDataFour hK) 6).ker := by
  intro hc
  rw [CFSG.ClassicalGroups.UnitaryFlag.ker_unitaryProj] at hc
  change (CFSG.SeitzReduction.UnitaryPilot.tvESU (fieldDataFour hK)
      (by decide : (0 : Fin 6) ≠ 1) 0 1 (CFSG.SeitzReduction.UnitaryPilot.tvAdm_one
        (fieldDataFour hK) 0 1)) ∈
      CFSG.ClassicalGroups.UnitaryFlag.unitaryScalars (fieldDataFour hK) 6 at hc
  rw [CFSG.ClassicalGroups.UnitaryFlag.mem_unitaryScalars] at hc
  obtain ⟨d, hdN, hd6, hdmat⟩ := hc
  have hmat : (((CFSG.SeitzReduction.UnitaryPilot.tvESU (fieldDataFour hK)
      (by decide : (0 : Fin 6) ≠ 1) 0 1 (CFSG.SeitzReduction.UnitaryPilot.tvAdm_one
        (fieldDataFour hK) 0 1) : CFSG.ClassicalGroups.UnitaryFlag.unitarySU 2 1 K 6) :
      GL (Fin 6) K) : Matrix (Fin 6) (Fin 6) K) =
      ((GeneralLinearGroup.scalar (Fin 6) d : GL (Fin 6) K) : Matrix (Fin 6) (Fin 6) K) :=
    congrArg (fun g : GL (Fin 6) K => (g : Matrix (Fin 6) (Fin 6) K)) hdmat
  rw [CFSG.SeitzReduction.UnitaryPilot.coe_tvESU] at hmat
  have hEq : CFSG.SeitzReduction.UnitaryPilot.tvE (fieldDataFour hK) 0 1 0 1 =
      Matrix.scalar (Fin 6) (d : K) := by
    simpa using hmat
  have h := congrFun (congrFun hEq 1) 0
  simp [CFSG.SeitzReduction.UnitaryPilot.tvE_apply, Matrix.scalar_apply,
    Matrix.one_apply_ne (by decide : (1 : Fin 6) ≠ 0),
    CFSG.SeitzReduction.UnitaryPilot.tvVec_left (by decide : (0 : Fin 6) ≠ 1),
    CFSG.SeitzReduction.UnitaryPilot.tvVec_right (by decide : (0 : Fin 6) ≠ 1)] at h

theorem TvCore.Q_not_commutative (hK : Nat.card K = 4) :
    ∃ a ∈ TvCore.Q hK, ∃ b ∈ TvCore.Q hK, a * b ≠ b * a := by
  letI : Finite K := (fieldDataFour hK).finite
  let ω := TvCore.omegaSix hK
  have hω : ω ^ 2 + ω + 1 = 0 := TvCore.omegaSix_spec hK
  have hωsq : ω + ω ^ 2 = 1 := omega_add_sq hK hω
  have hω3 : ω ^ 2 * ω = 1 := TvCore.omega_cube hK hω
  let x : Fin 6 → K := Pi.single 2 1
  let x' : Fin 6 → K := Pi.single 2 ω
  have hx : CFSG.SeitzReduction.UnitaryPilot.TvAdm (fieldDataFour hK) 0 1 x ω := by
    rw [show x = Pi.single (2 : Fin 6) (1 : K) from rfl]
    exact CFSG.SeitzReduction.UnitaryPilot.tvAdm_single (fieldDataFour hK)
      (by decide : (2 : Fin 6) ∈ ({0, 1}ᶜ : Finset (Fin 6)))
      (by rw [map_one, one_mul]; exact hωsq)
  have hx' : CFSG.SeitzReduction.UnitaryPilot.TvAdm (fieldDataFour hK) 0 1 x' ω := by
    rw [show x' = Pi.single (2 : Fin 6) ω from rfl]
    exact CFSG.SeitzReduction.UnitaryPilot.tvAdm_single (fieldDataFour hK)
      (by decide : (2 : Fin 6) ∈ ({0, 1}ᶜ : Finset (Fin 6)))
      (by rw [fieldDataFour_bar hK]; exact hωsq.trans hω3.symm)
  let a := CFSG.SeitzReduction.UnitaryPilot.tvESU (fieldDataFour hK)
    (by decide : (0 : Fin 6) ≠ 1) x ω hx
  let b := CFSG.SeitzReduction.UnitaryPilot.tvESU (fieldDataFour hK)
    (by decide : (0 : Fin 6) ≠ 1) x' ω hx'
  refine ⟨(CFSG.ClassicalGroups.UnitaryFlag.unitaryProj (fieldDataFour hK) 6) a,
    Subgroup.mem_map_of_mem _ (CFSG.SeitzReduction.UnitaryPilot.tvESU_mem_tvRadical
      (fieldDataFour hK) (by decide : (0 : Fin 6) ≠ 1) hx),
    (CFSG.ClassicalGroups.UnitaryFlag.unitaryProj (fieldDataFour hK) 6) b,
    Subgroup.mem_map_of_mem _ (CFSG.SeitzReduction.UnitaryPilot.tvESU_mem_tvRadical
      (fieldDataFour hK) (by decide : (0 : Fin 6) ≠ 1) hx'), ?_⟩
  intro hcomm
  have hab : a * b = CFSG.SeitzReduction.UnitaryPilot.tvESU (fieldDataFour hK)
      (by decide : (0 : Fin 6) ≠ 1) 0 1 (CFSG.SeitzReduction.UnitaryPilot.tvAdm_one
        (fieldDataFour hK) 0 1) * (b * a) := by
    rw [show a = CFSG.SeitzReduction.UnitaryPilot.tvESU (fieldDataFour hK)
        (by decide : (0 : Fin 6) ≠ 1) x ω hx from rfl,
      show b = CFSG.SeitzReduction.UnitaryPilot.tvESU (fieldDataFour hK)
        (by decide : (0 : Fin 6) ≠ 1) x' ω hx' from rfl,
      CFSG.SeitzReduction.UnitaryPilot.tvESU_mul,
      CFSG.SeitzReduction.UnitaryPilot.tvESU_mul,
      CFSG.SeitzReduction.UnitaryPilot.tvESU_mul]
    refine CFSG.SeitzReduction.UnitaryPilot.tvESU_congr (fieldDataFour hK)
      (by decide : (0 : Fin 6) ≠ 1) ?_ ?_ _ _
    · simp only [x, x', zero_add]
      rw [add_comm]
    · simp only [x, x', CFSG.SeitzReduction.UnitaryPilot.tvBar_single,
        single_dotProduct, Pi.single_eq_same,
        CFSG.SeitzReduction.UnitaryPilot.tvBar_zero, zero_dotProduct, zero_add,
        mul_one, one_mul, map_one, map_add, fieldDataFour_bar hK]
      simp only [one_pow, one_mul, add_zero]
      linear_combination hωsq - (ω ^ 2) * two_eq_zero hK
  have hcab : ⁅a, b⁆ = CFSG.SeitzReduction.UnitaryPilot.tvESU (fieldDataFour hK)
      (by decide : (0 : Fin 6) ≠ 1) 0 1 (CFSG.SeitzReduction.UnitaryPilot.tvAdm_one
        (fieldDataFour hK) 0 1) :=
    CFSG.SeitzReduction.UnitaryPilot.commutatorElement_eq_of_mul_eq hab
  have hker : ⁅a, b⁆ ∈ (CFSG.ClassicalGroups.UnitaryFlag.unitaryProj (fieldDataFour hK) 6).ker := by
    rw [MonoidHom.mem_ker]
    have hm : (CFSG.ClassicalGroups.UnitaryFlag.unitaryProj (fieldDataFour hK) 6) ⁅a, b⁆ =
        (CFSG.ClassicalGroups.UnitaryFlag.unitaryProj (fieldDataFour hK) 6) a *
          ((CFSG.ClassicalGroups.UnitaryFlag.unitaryProj (fieldDataFour hK) 6) b) *
          ((CFSG.ClassicalGroups.UnitaryFlag.unitaryProj (fieldDataFour hK) 6) a)⁻¹ *
          ((CFSG.ClassicalGroups.UnitaryFlag.unitaryProj (fieldDataFour hK) 6) b)⁻¹ := by
      simp [commutatorElement_def, map_mul, map_inv]
    rw [hm, hcomm]
    group
  rw [hcab] at hker
  exact TvCore.E_zero_one_not_scalar hK hker

theorem TvCore.map_centralizer_bijective {G H : Type*} [Group G] [Group H]
    (e : G ≃* H) (S : Set G) :
    (Subgroup.centralizer S).map e.toMonoidHom = Subgroup.centralizer (e '' S) := by
  apply le_antisymm
  · exact Subgroup.map_centralizer_le_centralizer_image S e.toMonoidHom
  · intro x hx
    refine ⟨e.symm x, ?_, e.apply_symm_apply x⟩
    change ∀ s ∈ S, s * e.symm x = e.symm x * s
    intro s hs
    have hxmem : x ∈ Subgroup.centralizer (e '' S) := by simpa using hx
    have hx' : e s * x = x * e s :=
      (Subgroup.mem_centralizer_iff.mp hxmem) (e s) ⟨s, hs, rfl⟩
    apply e.injective
    simpa [map_mul] using hx'

theorem TvCore.centralizer_tZero_eq_map (hK : Nat.card K = 4) :
    Subgroup.centralizer {tZero hK} =
      (TvCore.C hK).map (largeEvenProjEquiv hK).toMonoidHom := by
  rw [tZero_eq_largeEvenProjEquiv_stdTransvection]
  rw [TvCore.C]
  rw [show TvCore.uZ hK = CFSG.SeitzReduction.UnitaryPilot.stdTransvection (fieldDataFour hK)
      (by decide : (0 : Fin 6) ≠ 1) from rfl]
  rw [TvCore.map_centralizer_bijective (largeEvenProjEquiv hK) {TvCore.uZ hK}]
  simp

theorem TvCore.pCoreOf_centralizer_tZero_eq_map_Q (hK : Nat.card K = 4) :
    pCoreOf 2 (Subgroup.centralizer {tZero hK}) =
      (TvCore.Q hK).map (largeEvenProjEquiv hK).toMonoidHom := by
  rw [TvCore.centralizer_tZero_eq_map]
  rw [CFSG.LieType.BorelTits.pCoreOf_map_mulEquiv 2 (largeEvenProjEquiv hK)
    (TvCore.C hK)]
  rw [TvCore.pCoreOf_eq_Q]

theorem pCoreOf_centralizer_tZero_eq (hK : Nat.card K = 4) :
    pCoreOf 2 (Subgroup.centralizer {tZero hK}) =
      (CFSG.SeitzReduction.UnitaryPilot.tvRadical (fieldDataFour hK)
        (by decide : (0 : Fin 6) ≠ 1)).map (LargeEvenProjMk _) := by
  rw [TvCore.pCoreOf_centralizer_tZero_eq_map_Q]
  conv_lhs =>
    rw [show TvCore.Q hK = (CFSG.SeitzReduction.UnitaryPilot.tvRadical (fieldDataFour hK)
        (by decide : (0 : Fin 6) ≠ 1)).map
        (CFSG.ClassicalGroups.UnitaryFlag.unitaryProj (fieldDataFour hK) 6) from rfl,
      Subgroup.map_map, largeEvenProjEquiv_comp_unitaryProj]
  change Subgroup.map (LargeEvenProjMk (LargeEvenSUGroup (Fin 6) K (2 ^ 1)))
      (tvRadicalSix hK) =
    Subgroup.map (LargeEvenProjMk (LargeEvenSUGroup (Fin 6) K (2 ^ 1)))
      (tvRadicalSix hK)
  rfl

theorem card_pCoreOf_centralizer_tZero (hK : Nat.card K = 4) :
    Nat.card (pCoreOf 2 (Subgroup.centralizer {tZero hK})) = 2 ^ 9 := by
  rw [TvCore.pCoreOf_centralizer_tZero_eq_map_Q]
  rw [Subgroup.card_map_of_injective (largeEvenProjEquiv hK).injective]
  exact TvCore.card_Q hK

theorem exists_ne_of_pCoreOf_centralizer_tZero (hK : Nat.card K = 4) :
    ∃ x ∈ pCoreOf 2 (Subgroup.centralizer {tZero hK}),
      ∃ y ∈ pCoreOf 2 (Subgroup.centralizer {tZero hK}), x * y ≠ y * x := by
  rw [TvCore.pCoreOf_centralizer_tZero_eq_map_Q]
  obtain ⟨a, ha, b, hb, hne⟩ := TvCore.Q_not_commutative hK
  refine ⟨largeEvenProjEquiv hK a, Subgroup.mem_map_of_mem _ ha,
    largeEvenProjEquiv hK b, Subgroup.mem_map_of_mem _ hb, ?_⟩
  intro h
  apply hne
  apply (largeEvenProjEquiv hK).injective
  simpa [map_mul] using h

theorem TvCore.fixed_eq_zero_or_one (hK : Nat.card K = 4) {t : K}
    (ht : (fieldDataFour hK).bar t = t) : t = 0 ∨ t = 1 := by
  have hsq : t ^ 2 = t := by
    rw [← fieldDataFour_bar hK t, ht]
  have hfac : t * (t - 1) = 0 := by linear_combination hsq
  rcases mul_eq_zero.mp hfac with h | h
  · exact Or.inl h
  · exact Or.inr (sub_eq_zero.mp h)

theorem TvCore.bar_commutator_scalar (hK : Nat.card K = 4) (x x' : Fin 6 → K) :
    (fieldDataFour hK).bar
      (CFSG.SeitzReduction.UnitaryPilot.tvBar (fieldDataFour hK) x ⬝ᵥ x' +
        CFSG.SeitzReduction.UnitaryPilot.tvBar (fieldDataFour hK) x' ⬝ᵥ x) =
      CFSG.SeitzReduction.UnitaryPilot.tvBar (fieldDataFour hK) x ⬝ᵥ x' +
        CFSG.SeitzReduction.UnitaryPilot.tvBar (fieldDataFour hK) x' ⬝ᵥ x := by
  simp only [map_add, dotProduct, map_sum, map_mul,
    CFSG.SeitzReduction.UnitaryPilot.tvBar_apply,
    CFSG.LocalAnalysis.ComponentInitial.UnitaryFieldData.bar_bar]
  rw [add_comm]
  congr 1
  · apply Finset.sum_congr rfl
    intro i _
    exact mul_comm _ _
  · apply Finset.sum_congr rfl
    intro i _
    exact mul_comm _ _

theorem TvCore.tvAdm_zero_of_bar_eq_self (hK : Nat.card K = 4) {t : K}
    (ht : (fieldDataFour hK).bar t = t) :
    CFSG.SeitzReduction.UnitaryPilot.TvAdm (fieldDataFour hK) (0 : Fin 6) 1 0 t := by
  haveI := charP_two_of_card_four hK
  refine ⟨rfl, rfl, ?_⟩
  rw [CFSG.SeitzReduction.UnitaryPilot.tvBar_zero, zero_dotProduct, ht]
  exact CharTwo.add_self_eq_zero t

theorem TvCore.commutator_tvESU (hK : Nat.card K = 4)
    {x x' : Fin 6 → K} {s s' : K}
    (hxs : CFSG.SeitzReduction.UnitaryPilot.TvAdm (fieldDataFour hK) 0 1 x s)
    (hxs' : CFSG.SeitzReduction.UnitaryPilot.TvAdm (fieldDataFour hK) 0 1 x' s') :
    ⁅CFSG.SeitzReduction.UnitaryPilot.tvESU (fieldDataFour hK)
        (by decide : (0 : Fin 6) ≠ 1) x s hxs,
      CFSG.SeitzReduction.UnitaryPilot.tvESU (fieldDataFour hK)
        (by decide : (0 : Fin 6) ≠ 1) x' s' hxs'⁆ =
      CFSG.SeitzReduction.UnitaryPilot.tvESU (fieldDataFour hK)
        (by decide : (0 : Fin 6) ≠ 1) 0
        (CFSG.SeitzReduction.UnitaryPilot.tvBar (fieldDataFour hK) x ⬝ᵥ x' +
          CFSG.SeitzReduction.UnitaryPilot.tvBar (fieldDataFour hK) x' ⬝ᵥ x)
        (TvCore.tvAdm_zero_of_bar_eq_self hK (TvCore.bar_commutator_scalar hK x x')) := by
  refine CFSG.SeitzReduction.UnitaryPilot.commutatorElement_eq_of_mul_eq ?_
  rw [CFSG.SeitzReduction.UnitaryPilot.tvESU_mul,
    CFSG.SeitzReduction.UnitaryPilot.tvESU_mul,
    CFSG.SeitzReduction.UnitaryPilot.tvESU_mul]
  refine CFSG.SeitzReduction.UnitaryPilot.tvESU_congr (fieldDataFour hK)
    (by decide : (0 : Fin 6) ≠ 1) ?_ ?_ _ _
  · rw [zero_add, add_comm]
  · simp only [CFSG.SeitzReduction.UnitaryPilot.tvBar_zero, zero_dotProduct, zero_add,
      add_assoc]
    have h2 : (2 : K) = 0 := two_eq_zero hK
    linear_combination
      -(CFSG.SeitzReduction.UnitaryPilot.tvBar (fieldDataFour hK) x' ⬝ᵥ x) * two_eq_zero hK

theorem TvCore.commutator_Q_le_zpowers (hK : Nat.card K = 4) :
    ⁅TvCore.Q hK, TvCore.Q hK⁆ ≤ Subgroup.zpowers (TvCore.uZ hK) := by
  rw [Subgroup.commutator_le]
  intro q1 hq1 q2 hq2
  have hq1' : q1 ∈ (TvCore.R hK).map
      (CFSG.ClassicalGroups.UnitaryFlag.unitaryProj (fieldDataFour hK) 6) := by
    simpa [TvCore.Q, CFSG.SeitzReduction.UnitaryPilot.stdTransvectionRadical,
      TvCore.R] using hq1
  have hq2' : q2 ∈ (TvCore.R hK).map
      (CFSG.ClassicalGroups.UnitaryFlag.unitaryProj (fieldDataFour hK) 6) := by
    simpa [TvCore.Q, CFSG.SeitzReduction.UnitaryPilot.stdTransvectionRadical,
      TvCore.R] using hq2
  obtain ⟨r1, hr1, rfl⟩ := Subgroup.mem_map.mp hq1'
  obtain ⟨r2, hr2, rfl⟩ := Subgroup.mem_map.mp hq2'
  obtain ⟨x1, s1, h1, rfl⟩ :=
    CFSG.SeitzReduction.UnitaryPilot.exists_eq_tvESU_of_mem_tvRadical
      (fieldDataFour hK) (by decide : (0 : Fin 6) ≠ 1) hr1
  obtain ⟨x2, s2, h2, rfl⟩ :=
    CFSG.SeitzReduction.UnitaryPilot.exists_eq_tvESU_of_mem_tvRadical
      (fieldDataFour hK) (by decide : (0 : Fin 6) ≠ 1) hr2
  rw [← map_commutatorElement (CFSG.ClassicalGroups.UnitaryFlag.unitaryProj
    (fieldDataFour hK) 6)]
  rw [TvCore.commutator_tvESU hK h1 h2]
  have ht : (fieldDataFour hK).bar
      (CFSG.SeitzReduction.UnitaryPilot.tvBar (fieldDataFour hK) x1 ⬝ᵥ x2 +
        CFSG.SeitzReduction.UnitaryPilot.tvBar (fieldDataFour hK) x2 ⬝ᵥ x1) =
      CFSG.SeitzReduction.UnitaryPilot.tvBar (fieldDataFour hK) x1 ⬝ᵥ x2 +
        CFSG.SeitzReduction.UnitaryPilot.tvBar (fieldDataFour hK) x2 ⬝ᵥ x1 :=
    TvCore.bar_commutator_scalar hK x1 x2
  rcases TvCore.fixed_eq_zero_or_one hK ht with h0 | h1
  · rw [show CFSG.SeitzReduction.UnitaryPilot.tvESU (fieldDataFour hK)
        (by decide : (0 : Fin 6) ≠ 1) 0
        (CFSG.SeitzReduction.UnitaryPilot.tvBar (fieldDataFour hK) x1 ⬝ᵥ x2 +
          CFSG.SeitzReduction.UnitaryPilot.tvBar (fieldDataFour hK) x2 ⬝ᵥ x1)
        (TvCore.tvAdm_zero_of_bar_eq_self hK
          (TvCore.bar_commutator_scalar hK x1 x2)) =
        CFSG.SeitzReduction.UnitaryPilot.tvESU (fieldDataFour hK)
          (by decide : (0 : Fin 6) ≠ 1) 0 0
          (CFSG.SeitzReduction.UnitaryPilot.TvAdm.zero_zero (fieldDataFour hK)) from
      CFSG.SeitzReduction.UnitaryPilot.tvESU_congr (fieldDataFour hK)
        (by decide : (0 : Fin 6) ≠ 1) rfl h0 _ _]
    rw [show CFSG.SeitzReduction.UnitaryPilot.tvESU (fieldDataFour hK)
        (by decide : (0 : Fin 6) ≠ 1) 0 0
        (CFSG.SeitzReduction.UnitaryPilot.TvAdm.zero_zero (fieldDataFour hK)) = 1 from
      CFSG.SeitzReduction.UnitaryPilot.tvESU_zero_zero (fieldDataFour hK)
        (by decide : (0 : Fin 6) ≠ 1)]
    rw [map_one]
    exact Subgroup.one_mem _
  · rw [show CFSG.SeitzReduction.UnitaryPilot.tvESU (fieldDataFour hK)
        (by decide : (0 : Fin 6) ≠ 1) 0
        (CFSG.SeitzReduction.UnitaryPilot.tvBar (fieldDataFour hK) x1 ⬝ᵥ x2 +
          CFSG.SeitzReduction.UnitaryPilot.tvBar (fieldDataFour hK) x2 ⬝ᵥ x1)
        (TvCore.tvAdm_zero_of_bar_eq_self hK
          (TvCore.bar_commutator_scalar hK x1 x2)) =
        CFSG.SeitzReduction.UnitaryPilot.tvESU (fieldDataFour hK)
          (by decide : (0 : Fin 6) ≠ 1) 0 1
          (CFSG.SeitzReduction.UnitaryPilot.tvAdm_one (fieldDataFour hK) 0 1) from
      CFSG.SeitzReduction.UnitaryPilot.tvESU_congr (fieldDataFour hK)
        (by decide : (0 : Fin 6) ≠ 1) rfl h1 _ _]
    rw [show (CFSG.ClassicalGroups.UnitaryFlag.unitaryProj (fieldDataFour hK) 6)
        (CFSG.SeitzReduction.UnitaryPilot.tvESU (fieldDataFour hK)
          (by decide : (0 : Fin 6) ≠ 1) 0 1
          (CFSG.SeitzReduction.UnitaryPilot.tvAdm_one (fieldDataFour hK) 0 1)) =
        TvCore.uZ hK from rfl]
    exact Subgroup.mem_zpowers _

theorem TvCore.card_C (hK : Nat.card K = 4) :
    Nat.card (TvCore.C hK) = 25920 * 2 ^ 9 := by
  let B := TvCore.B hK
  let Q := TvCore.Q hK
  let C := TvCore.C hK
  have hBC : B ≤ C := by
    rw [show C = B ⊔ Q from TvCore.centralizer_eq_sup hK]
    exact le_sup_left
  have hQC : Q ≤ C := TvCore.Q_le_C hK
  have hBQ : B ⊓ Q = ⊥ := by
    rw [inf_comm]
    exact CFSG.SeitzReduction.UnitaryPilot.stdTransvectionRadical_inf_blockSU
      (fieldDataFour hK) (by decide : (0 : Fin 6) ≠ 1)
  have hQnorm : C ≤ Subgroup.normalizer (Q : Set _) := TvCore.C_le_normalizer_Q hK
  have hsup : B.subgroupOf C ⊔ Q.subgroupOf C = ⊤ := by
    rw [← Subgroup.subgroupOf_sup hBC hQC]
    exact Subgroup.subgroupOf_eq_top.mpr (by
      rw [show C = B ⊔ Q from TvCore.centralizer_eq_sup hK])
  haveI : (Q.subgroupOf C).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hQC).mpr hQnorm
  let f : (B × Q) → C := fun p => ⟨(p.1 : _) * (p.2 : _), C.mul_mem (hBC p.1.2) (hQC p.2.2)⟩
  have hf_inj : Function.Injective f := by
    rintro ⟨b1, q1⟩ ⟨b2, q2⟩ h
    have hbq : (b1 : CFSG.ClassicalGroups.UnitaryFlag.unitaryPSU (fieldDataFour hK) 6) *
        (q1 : CFSG.ClassicalGroups.UnitaryFlag.unitaryPSU (fieldDataFour hK) 6) =
        (b2 : CFSG.ClassicalGroups.UnitaryFlag.unitaryPSU (fieldDataFour hK) 6) *
          (q2 : CFSG.ClassicalGroups.UnitaryFlag.unitaryPSU (fieldDataFour hK) 6) :=
      congrArg Subtype.val h
    have hmem : (b2 : CFSG.ClassicalGroups.UnitaryFlag.unitaryPSU (fieldDataFour hK) 6)⁻¹ *
        (b1 : CFSG.ClassicalGroups.UnitaryFlag.unitaryPSU (fieldDataFour hK) 6) =
        (q2 : CFSG.ClassicalGroups.UnitaryFlag.unitaryPSU (fieldDataFour hK) 6) *
          (q1 : CFSG.ClassicalGroups.UnitaryFlag.unitaryPSU (fieldDataFour hK) 6)⁻¹ := by
      have h := congrArg (fun x =>
        (b2 : CFSG.ClassicalGroups.UnitaryFlag.unitaryPSU (fieldDataFour hK) 6)⁻¹ * x *
          (q1 : CFSG.ClassicalGroups.UnitaryFlag.unitaryPSU (fieldDataFour hK) 6)⁻¹) hbq
      simpa [mul_assoc] using h
    have hmemB : (b2 : CFSG.ClassicalGroups.UnitaryFlag.unitaryPSU (fieldDataFour hK) 6)⁻¹ *
        (b1 : CFSG.ClassicalGroups.UnitaryFlag.unitaryPSU (fieldDataFour hK) 6) ∈ B :=
      B.mul_mem (B.inv_mem b2.2) b1.2
    have hmemQ : (q2 : CFSG.ClassicalGroups.UnitaryFlag.unitaryPSU (fieldDataFour hK) 6) *
        (q1 : CFSG.ClassicalGroups.UnitaryFlag.unitaryPSU (fieldDataFour hK) 6)⁻¹ ∈ Q :=
      Q.mul_mem q2.2 (Q.inv_mem q1.2)
    have hone : (b2 : CFSG.ClassicalGroups.UnitaryFlag.unitaryPSU (fieldDataFour hK) 6)⁻¹ *
        (b1 : CFSG.ClassicalGroups.UnitaryFlag.unitaryPSU (fieldDataFour hK) 6) = 1 := by
      have hmemQ' : (b2 : CFSG.ClassicalGroups.UnitaryFlag.unitaryPSU (fieldDataFour hK) 6)⁻¹ *
          (b1 : CFSG.ClassicalGroups.UnitaryFlag.unitaryPSU (fieldDataFour hK) 6) ∈ Q := by
        rwa [← hmem] at hmemQ
      have : (b2 : CFSG.ClassicalGroups.UnitaryFlag.unitaryPSU (fieldDataFour hK) 6)⁻¹ *
          (b1 : CFSG.ClassicalGroups.UnitaryFlag.unitaryPSU (fieldDataFour hK) 6) ∈ B ⊓ Q :=
        ⟨hmemB, hmemQ'⟩
      rwa [hBQ, Subgroup.mem_bot] at this
    have hb : b1 = b2 := by
      have := congrArg (fun x =>
        (b2 : CFSG.ClassicalGroups.UnitaryFlag.unitaryPSU (fieldDataFour hK) 6) * x) hone
      simpa [mul_assoc] using this
    have hq : q1 = q2 := by
      apply Subtype.ext
      have hb' : (b1 : CFSG.ClassicalGroups.UnitaryFlag.unitaryPSU (fieldDataFour hK) 6) =
          (b2 : CFSG.ClassicalGroups.UnitaryFlag.unitaryPSU (fieldDataFour hK) 6) :=
        congrArg Subtype.val hb
      rw [hb'] at hbq
      exact mul_left_cancel hbq
    exact Prod.ext hb hq
  have hf_surj : Function.Surjective f := by
    intro c
    have hc : c ∈ B.subgroupOf C ⊔ Q.subgroupOf C := by
      rw [hsup]; exact Subgroup.mem_top c
    obtain ⟨b, hb, q, hq, hbq⟩ := (Subgroup.mem_sup_of_normal_right.mp hc)
    refine ⟨(⟨b, (Subgroup.mem_subgroupOf.mp hb)⟩, ⟨q, (Subgroup.mem_subgroupOf.mp hq)⟩), ?_⟩
    apply Subtype.ext
    exact congrArg Subtype.val hbq
  have hcard : Nat.card C = Nat.card (B × Q) :=
    Nat.card_congr (Equiv.ofBijective f ⟨hf_inj, hf_surj⟩).symm
  rw [hcard, Nat.card_prod, TvCore.card_blockSU hK, TvCore.card_Q hK]

theorem TvCore.card_sup_XQ (hK : Nat.card K = 4)
    {X : Subgroup (CFSG.ClassicalGroups.UnitaryFlag.unitaryPSU (fieldDataFour hK) 6)}
    (hXC : X ≤ TvCore.C hK) (hXc : Nat.card X = 25920)
    (hXQ : X ⊓ TvCore.Q hK = ⊥) :
    Nat.card ↥(X ⊔ TvCore.Q hK) = 25920 * 2 ^ 9 := by
  let Q := TvCore.Q hK
  let C := TvCore.C hK
  let XQ := X ⊔ Q
  have hQC : Q ≤ C := TvCore.Q_le_C hK
  have hXQC : XQ ≤ C := sup_le hXC hQC
  have hQnorm : XQ ≤ Subgroup.normalizer (Q : Set _) :=
    le_trans hXQC (TvCore.C_le_normalizer_Q hK)
  have hsup : X.subgroupOf XQ ⊔ Q.subgroupOf XQ = ⊤ := by
    rw [← Subgroup.subgroupOf_sup le_sup_left le_sup_right]
    exact Subgroup.subgroupOf_eq_top.mpr le_rfl
  haveI : (Q.subgroupOf XQ).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer le_sup_right).mpr hQnorm
  let f : (X × Q) → XQ :=
    fun p => ⟨(p.1 : CFSG.ClassicalGroups.UnitaryFlag.unitaryPSU (fieldDataFour hK) 6) *
        (p.2 : CFSG.ClassicalGroups.UnitaryFlag.unitaryPSU (fieldDataFour hK) 6),
      XQ.mul_mem (Subgroup.mem_sup_left p.1.2) (Subgroup.mem_sup_right p.2.2)⟩
  have hf_inj : Function.Injective f := by
    rintro ⟨x1, q1⟩ ⟨x2, q2⟩ h
    have hxq : (x1 : CFSG.ClassicalGroups.UnitaryFlag.unitaryPSU (fieldDataFour hK) 6) *
        (q1 : CFSG.ClassicalGroups.UnitaryFlag.unitaryPSU (fieldDataFour hK) 6) =
        (x2 : CFSG.ClassicalGroups.UnitaryFlag.unitaryPSU (fieldDataFour hK) 6) *
          (q2 : CFSG.ClassicalGroups.UnitaryFlag.unitaryPSU (fieldDataFour hK) 6) :=
      congrArg Subtype.val h
    have hmem : (x2 : CFSG.ClassicalGroups.UnitaryFlag.unitaryPSU (fieldDataFour hK) 6)⁻¹ *
        (x1 : CFSG.ClassicalGroups.UnitaryFlag.unitaryPSU (fieldDataFour hK) 6) =
        (q2 : CFSG.ClassicalGroups.UnitaryFlag.unitaryPSU (fieldDataFour hK) 6) *
          (q1 : CFSG.ClassicalGroups.UnitaryFlag.unitaryPSU (fieldDataFour hK) 6)⁻¹ := by
      have hc := congrArg (fun z =>
        (x2 : CFSG.ClassicalGroups.UnitaryFlag.unitaryPSU (fieldDataFour hK) 6)⁻¹ * z *
          (q1 : CFSG.ClassicalGroups.UnitaryFlag.unitaryPSU (fieldDataFour hK) 6)⁻¹) hxq
      simpa [mul_assoc] using hc
    have hmemX : (x2 : CFSG.ClassicalGroups.UnitaryFlag.unitaryPSU (fieldDataFour hK) 6)⁻¹ *
        (x1 : CFSG.ClassicalGroups.UnitaryFlag.unitaryPSU (fieldDataFour hK) 6) ∈ X :=
      X.mul_mem (X.inv_mem x2.2) x1.2
    have hmemQ : (q2 : CFSG.ClassicalGroups.UnitaryFlag.unitaryPSU (fieldDataFour hK) 6) *
        (q1 : CFSG.ClassicalGroups.UnitaryFlag.unitaryPSU (fieldDataFour hK) 6)⁻¹ ∈ Q :=
      Q.mul_mem q2.2 (Q.inv_mem q1.2)
    have hone : (x2 : CFSG.ClassicalGroups.UnitaryFlag.unitaryPSU (fieldDataFour hK) 6)⁻¹ *
        (x1 : CFSG.ClassicalGroups.UnitaryFlag.unitaryPSU (fieldDataFour hK) 6) = 1 := by
      have hmemQ' : (x2 : CFSG.ClassicalGroups.UnitaryFlag.unitaryPSU (fieldDataFour hK) 6)⁻¹ *
          (x1 : CFSG.ClassicalGroups.UnitaryFlag.unitaryPSU (fieldDataFour hK) 6) ∈ Q := by
        rwa [← hmem] at hmemQ
      have : (x2 : CFSG.ClassicalGroups.UnitaryFlag.unitaryPSU (fieldDataFour hK) 6)⁻¹ *
          (x1 : CFSG.ClassicalGroups.UnitaryFlag.unitaryPSU (fieldDataFour hK) 6) ∈ X ⊓ Q :=
        ⟨hmemX, hmemQ'⟩
      rwa [hXQ, Subgroup.mem_bot] at this
    have hx : x1 = x2 := by
      have := congrArg (fun z =>
        (x2 : CFSG.ClassicalGroups.UnitaryFlag.unitaryPSU (fieldDataFour hK) 6) * z) hone
      simpa [mul_assoc] using this
    have hq : q1 = q2 := by
      apply Subtype.ext
      have hx' : (x1 : CFSG.ClassicalGroups.UnitaryFlag.unitaryPSU (fieldDataFour hK) 6) =
          (x2 : CFSG.ClassicalGroups.UnitaryFlag.unitaryPSU (fieldDataFour hK) 6) :=
        congrArg Subtype.val hx
      rw [hx'] at hxq
      exact mul_left_cancel hxq
    exact Prod.ext hx hq
  have hf_surj : Function.Surjective f := by
    intro c
    have hc : c ∈ X.subgroupOf XQ ⊔ Q.subgroupOf XQ := by
      rw [hsup]; exact Subgroup.mem_top c
    obtain ⟨x, hx, q, hq, hxq⟩ := (Subgroup.mem_sup_of_normal_right.mp hc)
    refine ⟨(⟨x, Subgroup.mem_subgroupOf.mp hx⟩, ⟨q, Subgroup.mem_subgroupOf.mp hq⟩), ?_⟩
    apply Subtype.ext
    exact congrArg Subtype.val hxq
  have hcard : Nat.card XQ = Nat.card (X × Q) :=
    Nat.card_congr (Equiv.ofBijective f ⟨hf_inj, hf_surj⟩).symm
  rw [hcard, Nat.card_prod, hXc, TvCore.card_Q hK]

theorem TvCore.XQ_eq_C (hK : Nat.card K = 4)
    {X : Subgroup (CFSG.ClassicalGroups.UnitaryFlag.unitaryPSU (fieldDataFour hK) 6)}
    (hXC : X ≤ TvCore.C hK) (hXc : Nat.card X = 25920)
    (hXQ : X ⊓ TvCore.Q hK = ⊥) :
    X ⊔ TvCore.Q hK = TvCore.C hK := by
  haveI : Finite ↥(TvCore.C hK) :=
    Nat.finite_of_card_ne_zero (by rw [TvCore.card_C hK]; norm_num)
  apply Subgroup.eq_of_le_of_card_ge (sup_le hXC (TvCore.Q_le_C hK))
  rw [TvCore.card_sup_XQ hK hXC hXc hXQ, TvCore.card_C hK]

theorem TvCore.exists_mul_of_mem_C (hK : Nat.card K = 4)
    {X : Subgroup (CFSG.ClassicalGroups.UnitaryFlag.unitaryPSU (fieldDataFour hK) 6)}
    (hXC : X ≤ TvCore.C hK) (hXc : Nat.card X = 25920)
    (hXQ : X ⊓ TvCore.Q hK = ⊥)
    {c : CFSG.ClassicalGroups.UnitaryFlag.unitaryPSU (fieldDataFour hK) 6}
    (hc : c ∈ TvCore.C hK) :
    ∃ x ∈ X, ∃ q ∈ TvCore.Q hK, x * q = c := by
  let Q := TvCore.Q hK
  let C := TvCore.C hK
  have hXC' : X ≤ C := hXC
  have hQC : Q ≤ C := TvCore.Q_le_C hK
  have hXQC : X ≤ C := hXC'
  have hsup : X.subgroupOf C ⊔ Q.subgroupOf C = ⊤ := by
    rw [← Subgroup.subgroupOf_sup hXC' hQC]
    exact Subgroup.subgroupOf_eq_top.mpr (by rw [TvCore.XQ_eq_C hK hXC hXc hXQ])
  haveI : (Q.subgroupOf C).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hQC).mpr (TvCore.C_le_normalizer_Q hK)
  have hc' : (⟨c, hc⟩ : C) ∈ X.subgroupOf C ⊔ Q.subgroupOf C := by
    rw [hsup]; exact Subgroup.mem_top _
  obtain ⟨x, hx, q, hq, hxq⟩ := (Subgroup.mem_sup_of_normal_right.mp hc')
  exact ⟨x, Subgroup.mem_subgroupOf.mp hx, q, Subgroup.mem_subgroupOf.mp hq,
    congrArg Subtype.val hxq⟩

theorem TvCore.B_le_normalizer_Y (hK : Nat.card K = 4)
    {X Y : Subgroup (CFSG.ClassicalGroups.UnitaryFlag.unitaryPSU (fieldDataFour hK) 6)}
    (hXC : X ≤ TvCore.C hK) (hXc : Nat.card X = 25920)
    (hXQ : X ⊓ TvCore.Q hK = ⊥)
    (hXY : X ≤ Subgroup.normalizer (Y : Set _))
    (hY₁ : Subgroup.zpowers (TvCore.uZ hK) ≤ Y)
    (hY₂ : Y ≤ TvCore.Q hK) :
    TvCore.B hK ≤ Subgroup.normalizer (Y : Set _) := by
  intro g hg
  have hgC : g ∈ TvCore.C hK := by
    rw [TvCore.centralizer_eq_sup hK]
    exact Subgroup.mem_sup_left hg
  obtain ⟨x, hx, q, hq, hxq⟩ :=
    TvCore.exists_mul_of_mem_C hK hXC hXc hXQ hgC
  have hconj : ∀ (x : CFSG.ClassicalGroups.UnitaryFlag.unitaryPSU (fieldDataFour hK) 6),
      x ∈ X → ∀ (q : CFSG.ClassicalGroups.UnitaryFlag.unitaryPSU (fieldDataFour hK) 6),
      q ∈ TvCore.Q hK → ∀ (y : CFSG.ClassicalGroups.UnitaryFlag.unitaryPSU (fieldDataFour hK) 6),
      y ∈ Y → (x * q) * y * (x * q)⁻¹ ∈ Y := by
    intro x hx q hq y hy
    have hqy : q * y * q⁻¹ ∈ Y := by
      have hcomm : ⁅q, y⁆ ∈ Y := by
        have hmem : ⁅q, y⁆ ∈ ⁅TvCore.Q hK, TvCore.Q hK⁆ :=
          Subgroup.commutator_mem_commutator hq (hY₂ hy)
        exact hY₁ (TvCore.commutator_Q_le_zpowers hK hmem)
      have heq : q * y * q⁻¹ = ⁅q, y⁆ * y := by
        rw [commutatorElement_def]; group
      rw [heq]
      exact Y.mul_mem hcomm hy
    have hxconj : x * (q * y * q⁻¹) * x⁻¹ ∈ Y :=
      (Subgroup.mem_normalizer_iff.mp (hXY hx) (q * y * q⁻¹)).mp hqy
    have hEq : (x * q) * y * (x * q)⁻¹ = x * (q * y * q⁻¹) * x⁻¹ := by group
    rw [hEq]
    exact hxconj
  have hconj_inv : ∀ (y : CFSG.ClassicalGroups.UnitaryFlag.unitaryPSU (fieldDataFour hK) 6),
      y ∈ Y → (x * q)⁻¹ * y * (x * q) ∈ Y := by
    intro y hy
    have hxNQ : x ∈ Subgroup.normalizer (TvCore.Q hK : Set _) :=
      le_trans hXC (TvCore.C_le_normalizer_Q hK) hx
    let q' : CFSG.ClassicalGroups.UnitaryFlag.unitaryPSU (fieldDataFour hK) 6 :=
      x * q⁻¹ * x⁻¹
    have hq' : q' ∈ TvCore.Q hK :=
      (Subgroup.mem_normalizer_iff.mp hxNQ (q⁻¹)).mp ((TvCore.Q hK).inv_mem hq)
    have hgInv : (x * q)⁻¹ = x⁻¹ * q' := by
      dsimp [q']; group
    have hback : (x⁻¹ * q')⁻¹ = x * q := by
      dsimp [q']; group
    rw [hgInv, ← hback]
    exact hconj (x⁻¹) (X.inv_mem hx) q' hq' y hy
  rw [← hxq]
  exact Subgroup.mem_normalizer_iff.mpr (fun y => ⟨hconj x hx q hq y, fun hy => by
    have := hconj_inv ((x * q) * y * (x * q)⁻¹) hy
    simpa [mul_assoc] using this⟩)

abbrev TvCore.J6 : Finset (Fin 6) := {0, 1}ᶜ
theorem TvCore.mem_unitaryBlock_mulVec_support (hK : Nat.card K = 4)
    {u : CFSG.ClassicalGroups.UnitaryFlag.unitarySU 2 1 K 6}
    (hu : u ∈ CFSG.SeitzReduction.UnitaryPilot.unitaryBlock (fieldDataFour hK) TvCore.J6)
    {x : Fin 6 → K} (hx : ∀ i, i ∉ TvCore.J6 → x i = 0) :
    ∀ i, i ∉ TvCore.J6 →
      ((((u : GL (Fin 6) K) : Matrix (Fin 6) (Fin 6) K) *ᵥ x) i) = 0 := by
  intro i hi
  rw [Matrix.mulVec, dotProduct]
  apply Finset.sum_eq_zero
  intro j hj
  by_cases hxj : x j = 0
  · simp [hxj]
  · have hjJ : j ∈ TvCore.J6 := by
      by_contra hj'
      exact hxj (hx j hj')
    have hM : (((u : GL (Fin 6) K) : Matrix (Fin 6) (Fin 6) K)) i j = 0 := by
      have h := (CFSG.SeitzReduction.UnitaryPilot.mem_unitaryBlock (fieldDataFour hK)).1 hu i j
        (Or.inl hi)
      rw [h]
      have hij : i ≠ j := by
        rintro rfl
        exact hi hjJ
      simp [Matrix.one_apply, hij]
    rw [hM, zero_mul]

noncomputable def TvCore.V (hK : Nat.card K = 4)
    (Y : Subgroup (CFSG.ClassicalGroups.UnitaryFlag.unitaryPSU (fieldDataFour hK) 6)) :
    AddSubgroup (Fin 6 → K) where
  carrier := {x | (∀ i, i ∉ TvCore.J6 → x i = 0) ∧ ∃ (s : K)
    (hxs : CFSG.SeitzReduction.UnitaryPilot.TvAdm (fieldDataFour hK) (0 : Fin 6) 1 x s),
    (CFSG.ClassicalGroups.UnitaryFlag.unitaryProj (fieldDataFour hK) 6)
      (CFSG.SeitzReduction.UnitaryPilot.tvESU (fieldDataFour hK)
        (by decide : (0 : Fin 6) ≠ 1) x s hxs) ∈ Y}
  zero_mem' := by
    refine ⟨by simp, 0, CFSG.SeitzReduction.UnitaryPilot.TvAdm.zero_zero (fieldDataFour hK), ?_⟩
    rw [CFSG.SeitzReduction.UnitaryPilot.tvESU_zero_zero]
    exact Y.one_mem
  add_mem' := by
    intro x y hx hy
    obtain ⟨hxsupp, sx, hxs, hxY⟩ := hx
    obtain ⟨hysupp, sy, hys, hyY⟩ := hy
    refine ⟨?_, sx + sy +
      CFSG.SeitzReduction.UnitaryPilot.tvBar (fieldDataFour hK) x ⬝ᵥ y,
      hxs.mul (fieldDataFour hK) hys, ?_⟩
    · intro i hi
      simp [hxsupp i hi, hysupp i hi]
    · rw [← CFSG.SeitzReduction.UnitaryPilot.tvESU_mul (fieldDataFour hK)
        (by decide : (0 : Fin 6) ≠ 1) hxs hys]
      rw [map_mul]
      exact Y.mul_mem hxY hyY
  neg_mem' := by
    intro x hx
    obtain ⟨hxsupp, s, hxs, hxY⟩ := hx
    haveI := charP_two_of_card_four hK
    have hneg : (-x : Fin 6 → K) = x := by
      ext i
      exact (eq_neg_of_add_eq_zero_left (CharTwo.add_self_eq_zero (x i))).symm
    refine ⟨?_, (fieldDataFour hK).bar s, ?_, ?_⟩
    · intro i hi
      rw [Pi.neg_apply, hxsupp i hi, neg_zero]
    · simpa [hneg] using hxs.bar (fieldDataFour hK)
    · have hmem : (CFSG.ClassicalGroups.UnitaryFlag.unitaryProj (fieldDataFour hK) 6)
          (CFSG.SeitzReduction.UnitaryPilot.tvESU (fieldDataFour hK)
            (by decide : (0 : Fin 6) ≠ 1) x ((fieldDataFour hK).bar s)
            (hxs.bar (fieldDataFour hK))) ∈ Y := by
        rw [← CFSG.SeitzReduction.UnitaryPilot.tvESU_inv (fieldDataFour hK)
          (by decide : (0 : Fin 6) ≠ 1) hxs]
        rw [map_inv]
        exact Y.inv_mem hxY
      simpa [hneg] using hmem

theorem TvCore.V_mem_mulVec (hK : Nat.card K = 4)
    {X Y : Subgroup (CFSG.ClassicalGroups.UnitaryFlag.unitaryPSU (fieldDataFour hK) 6)}
    (hXC : X ≤ TvCore.C hK) (hXc : Nat.card X = 25920)
    (hXQ : X ⊓ TvCore.Q hK = ⊥)
    (hXY : X ≤ Subgroup.normalizer (Y : Set _))
    (hY₁ : Subgroup.zpowers (TvCore.uZ hK) ≤ Y)
    (hY₂ : Y ≤ TvCore.Q hK)
    {u : CFSG.ClassicalGroups.UnitaryFlag.unitarySU 2 1 K 6}
    (hu : u ∈ CFSG.SeitzReduction.UnitaryPilot.unitaryBlock (fieldDataFour hK) TvCore.J6)
    {x : Fin 6 → K} (hx : x ∈ TvCore.V hK Y) :
    ((((u : GL (Fin 6) K) : Matrix (Fin 6) (Fin 6) K) *ᵥ x)) ∈ TvCore.V hK Y := by
  obtain ⟨hxsupp, s, hxs, hxY⟩ := hx
  have hBnorm : TvCore.B hK ≤ Subgroup.normalizer (Y : Set _) :=
    TvCore.B_le_normalizer_Y hK hXC hXc hXQ hXY hY₁ hY₂
  obtain ⟨hxs', hconj⟩ :=
    CFSG.SeitzReduction.UnitaryPilot.conj_tvESU (fieldDataFour hK)
      (by decide : (0 : Fin 6) ≠ 1) hu hxs
  refine ⟨?_, s, hxs', ?_⟩
  · exact TvCore.mem_unitaryBlock_mulVec_support hK hu hxsupp
  · have hB : (CFSG.ClassicalGroups.UnitaryFlag.unitaryProj (fieldDataFour hK) 6) u ∈
        TvCore.B hK := by
      rw [TvCore.B, CFSG.SeitzReduction.UnitaryPilot.blockSU]
      exact Subgroup.mem_map.mpr ⟨u, hu, rfl⟩
    have hmem : (CFSG.ClassicalGroups.UnitaryFlag.unitaryProj (fieldDataFour hK) 6)
        (CFSG.SeitzReduction.UnitaryPilot.tvESU (fieldDataFour hK)
          (by decide : (0 : Fin 6) ≠ 1)
          ((((u : GL (Fin 6) K) : Matrix (Fin 6) (Fin 6) K) *ᵥ x)) s hxs') ∈ Y := by
      rw [← hconj]
      rw [map_mul, map_mul, map_inv]
      exact (Subgroup.mem_normalizer_iff.mp (hBnorm hB)
        ((CFSG.ClassicalGroups.UnitaryFlag.unitaryProj (fieldDataFour hK) 6)
          (CFSG.SeitzReduction.UnitaryPilot.tvESU (fieldDataFour hK)
            (by decide : (0 : Fin 6) ≠ 1) x s hxs))).mp hxY
    exact hmem

theorem TvCore.tvBlock_unitaryBlockEquiv (hK : Nat.card K = 4)
    (g : CFSG.ClassicalGroups.UnitaryFlag.unitarySU 2 1 K TvCore.J6.card) :
    CFSG.SeitzReduction.UnitaryPilot.tvBlock (0 : Fin 6) 1
      ((((CFSG.SeitzReduction.UnitaryPilot.unitaryBlockEquiv (fieldDataFour hK) TvCore.J6 g :
        CFSG.SeitzReduction.UnitaryPilot.unitaryBlock (fieldDataFour hK) TvCore.J6) :
          CFSG.ClassicalGroups.UnitaryFlag.unitarySU 2 1 K 6) : GL (Fin 6) K) :
        Matrix (Fin 6) (Fin 6) K) =
      Matrix.reindex TvCore.J6.equivFin.symm TvCore.J6.equivFin.symm
        ((g : GL (Fin TvCore.J6.card) K) :
          Matrix (Fin TvCore.J6.card) (Fin TvCore.J6.card) K) := by
  ext i j
  rw [CFSG.SeitzReduction.UnitaryPilot.tvBlock_apply,
    CFSG.SeitzReduction.UnitaryPilot.coe_unitaryBlockEquiv,
    CFSG.SeitzReduction.UnitaryPilot.coe_unitaryBlockEmbed,
    CFSG.SeitzReduction.LinearPilot.blockMatrix_apply]
  rw [dif_pos ⟨i.2, j.2⟩]

noncomputable def TvCore.restrictJ : (Fin 6 → K) →+ (TvCore.J6 → K) where
  toFun x := fun j => x j
  map_zero' := rfl
  map_add' x y := rfl

noncomputable abbrev TvCore.blockEmbedBlock (hK : Nat.card K = 4)
    (g : CFSG.ClassicalGroups.UnitaryFlag.unitarySU 2 1 K TvCore.J6.card) :
    CFSG.SeitzReduction.UnitaryPilot.unitaryBlock (fieldDataFour hK) TvCore.J6 :=
  CFSG.SeitzReduction.UnitaryPilot.unitaryBlockEquiv (fieldDataFour hK) TvCore.J6 g

noncomputable abbrev TvCore.blockEmbedSU (hK : Nat.card K = 4)
    (g : CFSG.ClassicalGroups.UnitaryFlag.unitarySU 2 1 K TvCore.J6.card) :
    CFSG.ClassicalGroups.UnitaryFlag.unitarySU 2 1 K 6 :=
  (TvCore.blockEmbedBlock hK g :
    CFSG.ClassicalGroups.UnitaryFlag.unitarySU 2 1 K 6)

theorem TvCore.restrictJ_mulVec_unitaryBlock (hK : Nat.card K = 4)
    (g : CFSG.ClassicalGroups.UnitaryFlag.unitarySU 2 1 K TvCore.J6.card)
    (v : Fin 6 → K) (hv : ∀ i, i ∉ TvCore.J6 → v i = 0) :
    TvCore.restrictJ (K := K)
        ((((TvCore.blockEmbedSU hK g : CFSG.ClassicalGroups.UnitaryFlag.unitarySU 2 1 K 6) :
          GL (Fin 6) K) : Matrix (Fin 6) (Fin 6) K) *ᵥ v) =
      (((reindexMatrixEquiv TvCore.J6.equivFin).symm (g : GL (Fin TvCore.J6.card) K)) :
        Matrix TvCore.J6 TvCore.J6 K) *ᵥ TvCore.restrictJ (K := K) v := by
  let e := TvCore.J6.equivFin
  let A : GL TvCore.J6 K := (reindexMatrixEquiv e).symm (g : GL (Fin TvCore.J6.card) K)
  have hA : (A : Matrix TvCore.J6 TvCore.J6 K) =
      Matrix.reindex e.symm e.symm ((g : GL (Fin TvCore.J6.card) K) :
        Matrix (Fin TvCore.J6.card) (Fin TvCore.J6.card) K) := by
    dsimp [A]
    rw [reindexMatrixEquiv_symm_val, Matrix.reindex_apply, Equiv.symm_symm]
  ext j
  change ((((TvCore.blockEmbedSU hK g : CFSG.ClassicalGroups.UnitaryFlag.unitarySU 2 1 K 6) :
          GL (Fin 6) K) : Matrix (Fin 6) (Fin 6) K) *ᵥ v) ↑j =
    ((A : Matrix TvCore.J6 TvCore.J6 K) *ᵥ (fun i : TvCore.J6 => v i)) j
  simp only [Matrix.mulVec, dotProduct]
  rw [← Finset.sum_subset (s₁ := TvCore.J6) (s₂ := Finset.univ)
    (Finset.subset_univ _)]
  · rw [Finset.sum_subtype (s := TvCore.J6) (fun x => Iff.rfl)
      (fun i => ((((TvCore.blockEmbedSU hK g : CFSG.ClassicalGroups.UnitaryFlag.unitarySU 2 1 K 6) :
        GL (Fin 6) K) : Matrix (Fin 6) (Fin 6) K) ↑j i * v i))]
    apply Finset.sum_congr rfl
    intro i hi
    have hM : ((((TvCore.blockEmbedSU hK g : CFSG.ClassicalGroups.UnitaryFlag.unitarySU 2 1 K 6) :
          GL (Fin 6) K) : Matrix (Fin 6) (Fin 6) K) ↑j ↑i) =
        (A : Matrix TvCore.J6 TvCore.J6 K) j i := by
      rw [← CFSG.SeitzReduction.UnitaryPilot.tvBlock_apply (0 : Fin 6) 1
        ((((TvCore.blockEmbedSU hK g : CFSG.ClassicalGroups.UnitaryFlag.unitarySU 2 1 K 6) :
          GL (Fin 6) K) : Matrix (Fin 6) (Fin 6) K)) j i,
        TvCore.tvBlock_unitaryBlockEquiv hK g, ← hA]
    rw [hM]
  · intro i _ hi
    rw [hv i hi, mul_zero]

theorem TvCore.reindex_smul_unitaryBlock (hK : Nat.card K = 4)
    (g : CFSG.ClassicalGroups.UnitaryFlag.unitarySU 2 1 K TvCore.J6.card)
    (v : Fin 6 → K) (hv : ∀ i, i ∉ TvCore.J6 → v i = 0) :
    reindexVectorEquiv TvCore.J6.equivFin
        (TvCore.restrictJ (K := K)
          ((((TvCore.blockEmbedSU hK g : CFSG.ClassicalGroups.UnitaryFlag.unitarySU 2 1 K 6) :
            GL (Fin 6) K) : Matrix (Fin 6) (Fin 6) K) *ᵥ v)) =
      (((g : GL (Fin TvCore.J6.card) K) :
        Matrix (Fin TvCore.J6.card) (Fin TvCore.J6.card) K) *ᵥ
        reindexVectorEquiv TvCore.J6.equivFin (TvCore.restrictJ (K := K) v)) := by
  let e := TvCore.J6.equivFin
  let A : GL TvCore.J6 K := (reindexMatrixEquiv e).symm (g : GL (Fin TvCore.J6.card) K)
  rw [TvCore.restrictJ_mulVec_unitaryBlock hK g v hv]
  change reindexVectorEquiv e ((A : Matrix TvCore.J6 TvCore.J6 K) *ᵥ
    TvCore.restrictJ (K := K) v) = _
  rw [← reindexMatrixEquiv_mulVec e A (TvCore.restrictJ (K := K) v)]
  rw [show reindexMatrixEquiv e A = (g : GL (Fin TvCore.J6.card) K) from
    MulEquiv.apply_symm_apply _ _]
  rw [matrixLinearEquiv_apply]

noncomputable def TvCore.W (hK : Nat.card K = 4)
    (Y : Subgroup (CFSG.ClassicalGroups.UnitaryFlag.unitaryPSU (fieldDataFour hK) 6)) :
    AddSubgroup (Fin TvCore.J6.card → K) :=
  (TvCore.V hK Y).map
    (((reindexVectorEquiv TvCore.J6.equivFin).toLinearMap).toAddMonoidHom.comp
      TvCore.restrictJ)

theorem TvCore.W_invariant (hK : Nat.card K = 4)
    {X Y : Subgroup (CFSG.ClassicalGroups.UnitaryFlag.unitaryPSU (fieldDataFour hK) 6)}
    (hXC : X ≤ TvCore.C hK) (hXc : Nat.card X = 25920)
    (hXQ : X ⊓ TvCore.Q hK = ⊥)
    (hXY : X ≤ Subgroup.normalizer (Y : Set _))
    (hY₁ : Subgroup.zpowers (TvCore.uZ hK) ≤ Y)
    (hY₂ : Y ≤ TvCore.Q hK) :
    ∀ (g : CFSG.ClassicalGroups.UnitaryFlag.unitarySU 2 1 K TvCore.J6.card),
      ∀ w ∈ TvCore.W hK Y, (g : GL (Fin TvCore.J6.card) K) • w ∈ TvCore.W hK Y := by
  intro g w hw
  obtain ⟨v, hv, rfl⟩ := AddSubgroup.mem_map.mp hw
  have hvsupp : ∀ i, i ∉ TvCore.J6 → v i = 0 := hv.1
  have hV : ((((TvCore.blockEmbedSU hK g : CFSG.ClassicalGroups.UnitaryFlag.unitarySU 2 1 K 6) :
      GL (Fin 6) K) : Matrix (Fin 6) (Fin 6) K) *ᵥ v) ∈ TvCore.V hK Y :=
    TvCore.V_mem_mulVec hK hXC hXc hXQ hXY hY₁ hY₂
      (u := TvCore.blockEmbedSU hK g) (TvCore.blockEmbedBlock hK g).2 hv
  refine AddSubgroup.mem_map.mpr ⟨_, hV, ?_⟩
  change reindexVectorEquiv TvCore.J6.equivFin (TvCore.restrictJ (K := K)
    ((((TvCore.blockEmbedSU hK g : CFSG.ClassicalGroups.UnitaryFlag.unitarySU 2 1 K 6) :
      GL (Fin 6) K) : Matrix (Fin 6) (Fin 6) K) *ᵥ v)) =
    (g : GL (Fin TvCore.J6.card) K) • reindexVectorEquiv TvCore.J6.equivFin
      (TvCore.restrictJ (K := K) v)
  exact TvCore.reindex_smul_unitaryBlock hK g v hvsupp

theorem TvCore.W_eq_bot_or_top (hK : Nat.card K = 4)
    {X Y : Subgroup (CFSG.ClassicalGroups.UnitaryFlag.unitaryPSU (fieldDataFour hK) 6)}
    (hXC : X ≤ TvCore.C hK) (hXc : Nat.card X = 25920)
    (hXQ : X ⊓ TvCore.Q hK = ⊥)
    (hXY : X ≤ Subgroup.normalizer (Y : Set _))
    (hY₁ : Subgroup.zpowers (TvCore.uZ hK) ≤ Y)
    (hY₂ : Y ≤ TvCore.Q hK) :
    TvCore.W hK Y = ⊥ ∨ TvCore.W hK Y = ⊤ := by
  haveI : Finite K := Nat.finite_of_card_ne_zero (by rw [hK]; norm_num)
  haveI : CharP K 2 := charP_two_of_card_four hK
  let σ : K ≃+* K := CFSG.LieType.BorelTits.unitaryInvolution K 2 1
  have hσ : CFSG.ClassicalGroups.Unitary.IsUnitaryInvolution σ :=
    CFSG.ClassicalGroups.Unitary.isUnitaryInvolution_unitaryInvolution
      (K := K) (p := 2) (f := 1) (by simpa using hK)
  have hSU : CFSG.LieType.Universal.Unitary.SUid σ TvCore.J6.card =
      CFSG.ClassicalGroups.UnitaryFlag.unitarySU 2 1 K TvCore.J6.card := by
    rw [CFSG.LieType.Universal.Unitary.SUid_eq_statedSU (p := 2) (f := 1)
      (by simpa using hK)]
  have hcard : 3 ≤ TvCore.J6.card := by decide
  apply CFSG.RankThree.GF2n.Smith81.U6Cube.addSubgroup_eq_top_of_SUid_invariant
    (σ := σ) hσ (n := TvCore.J6.card) hcard (TvCore.W hK Y)
  intro g w hw
  change (g : GL (Fin TvCore.J6.card) K) • w ∈ TvCore.W hK Y
  let g' : CFSG.ClassicalGroups.UnitaryFlag.unitarySU 2 1 K TvCore.J6.card :=
    ⟨g, by rw [← hSU]; exact g.2⟩
  have hg' := TvCore.W_invariant hK hXC hXc hXQ hXY hY₁ hY₂ g' w hw
  simpa [g'] using hg'

theorem TvCore.V_eq_bot_of_W_eq_bot (hK : Nat.card K = 4)
    {Y : Subgroup (CFSG.ClassicalGroups.UnitaryFlag.unitaryPSU (fieldDataFour hK) 6)}
    (hW : TvCore.W hK Y = ⊥) : TvCore.V hK Y = ⊥ := by
  apply le_antisymm _ bot_le
  intro x hx
  have hxW : (((reindexVectorEquiv TvCore.J6.equivFin).toLinearMap).toAddMonoidHom.comp
      TvCore.restrictJ) x ∈ TvCore.W hK Y :=
    AddSubgroup.mem_map.mpr ⟨x, hx, rfl⟩
  rw [hW, AddSubgroup.mem_bot] at hxW
  have hres : TvCore.restrictJ (K := K) x = 0 := by
    have := congrArg (reindexVectorEquiv TvCore.J6.equivFin).symm hxW
    simpa using this
  ext i
  by_cases hi : i ∈ TvCore.J6
  · have := congrFun hres ⟨i, hi⟩
    change x i = 0
    simpa [TvCore.restrictJ] using this
  · exact hx.1 i hi

theorem TvCore.supported_mem_V_of_W_eq_top (hK : Nat.card K = 4)
    {Y : Subgroup (CFSG.ClassicalGroups.UnitaryFlag.unitaryPSU (fieldDataFour hK) 6)}
    (hW : TvCore.W hK Y = ⊤) {x : Fin 6 → K}
    (hxsupp : ∀ i, i ∉ TvCore.J6 → x i = 0) : x ∈ TvCore.V hK Y := by
  have hxW : (((reindexVectorEquiv TvCore.J6.equivFin).toLinearMap).toAddMonoidHom.comp
      TvCore.restrictJ) x ∈ TvCore.W hK Y := by
    rw [hW]; exact AddSubgroup.mem_top _
  obtain ⟨v, hv, hveq⟩ := AddSubgroup.mem_map.mp hxW
  have hres : TvCore.restrictJ (K := K) v = TvCore.restrictJ (K := K) x := by
    apply (reindexVectorEquiv TvCore.J6.equivFin).injective
    simpa using hveq
  have hvx : v = x := by
    ext i
    by_cases hi : i ∈ TvCore.J6
    · have := congrFun hres ⟨i, hi⟩
      change v i = x i
      simpa [TvCore.restrictJ] using this
    · rw [hv.1 i hi, hxsupp i hi]
  rwa [hvx] at hv

theorem TvCore.tvESU_zero_mem_zpowers (hK : Nat.card K = 4) {t : K}
    (ht : (fieldDataFour hK).bar t = t) :
    (CFSG.ClassicalGroups.UnitaryFlag.unitaryProj (fieldDataFour hK) 6)
      (CFSG.SeitzReduction.UnitaryPilot.tvESU (fieldDataFour hK)
        (by decide : (0 : Fin 6) ≠ 1) 0 t
        (TvCore.tvAdm_zero_of_bar_eq_self hK ht)) ∈
      Subgroup.zpowers (TvCore.uZ hK) := by
  rcases TvCore.fixed_eq_zero_or_one hK ht with h0 | h1
  · rw [show CFSG.SeitzReduction.UnitaryPilot.tvESU (fieldDataFour hK)
        (by decide : (0 : Fin 6) ≠ 1) 0 t
        (TvCore.tvAdm_zero_of_bar_eq_self hK ht) =
        CFSG.SeitzReduction.UnitaryPilot.tvESU (fieldDataFour hK)
          (by decide : (0 : Fin 6) ≠ 1) 0 0
          (CFSG.SeitzReduction.UnitaryPilot.TvAdm.zero_zero (fieldDataFour hK)) from
      CFSG.SeitzReduction.UnitaryPilot.tvESU_congr (fieldDataFour hK)
        (by decide : (0 : Fin 6) ≠ 1) rfl h0 _ _]
    rw [CFSG.SeitzReduction.UnitaryPilot.tvESU_zero_zero]
    rw [map_one]
    exact Subgroup.one_mem _
  · rw [show CFSG.SeitzReduction.UnitaryPilot.tvESU (fieldDataFour hK)
        (by decide : (0 : Fin 6) ≠ 1) 0 t
        (TvCore.tvAdm_zero_of_bar_eq_self hK ht) =
        CFSG.SeitzReduction.UnitaryPilot.tvESU (fieldDataFour hK)
          (by decide : (0 : Fin 6) ≠ 1) 0 1
          (CFSG.SeitzReduction.UnitaryPilot.tvAdm_one (fieldDataFour hK) 0 1) from
      CFSG.SeitzReduction.UnitaryPilot.tvESU_congr (fieldDataFour hK)
        (by decide : (0 : Fin 6) ≠ 1) rfl h1 _ _]
    rw [show (CFSG.ClassicalGroups.UnitaryFlag.unitaryProj (fieldDataFour hK) 6)
        (CFSG.SeitzReduction.UnitaryPilot.tvESU (fieldDataFour hK)
          (by decide : (0 : Fin 6) ≠ 1) 0 1
          (CFSG.SeitzReduction.UnitaryPilot.tvAdm_one (fieldDataFour hK) 0 1)) =
        TvCore.uZ hK from rfl]
    exact Subgroup.mem_zpowers _

theorem TvCore.E_mul_E_inv_mem_zpowers (hK : Nat.card K = 4)
    {x : Fin 6 → K} {s s0 : K}
    (hxs : CFSG.SeitzReduction.UnitaryPilot.TvAdm (fieldDataFour hK) (0 : Fin 6) 1 x s)
    (hxs0 : CFSG.SeitzReduction.UnitaryPilot.TvAdm (fieldDataFour hK) (0 : Fin 6) 1 x s0) :
    (CFSG.ClassicalGroups.UnitaryFlag.unitaryProj (fieldDataFour hK) 6)
        (CFSG.SeitzReduction.UnitaryPilot.tvESU (fieldDataFour hK)
          (by decide : (0 : Fin 6) ≠ 1) x s hxs) *
      ((CFSG.ClassicalGroups.UnitaryFlag.unitaryProj (fieldDataFour hK) 6)
        (CFSG.SeitzReduction.UnitaryPilot.tvESU (fieldDataFour hK)
          (by decide : (0 : Fin 6) ≠ 1) x s0 hxs0))⁻¹ ∈
      Subgroup.zpowers (TvCore.uZ hK) := by
  haveI := charP_two_of_card_four hK
  let T : K := CFSG.SeitzReduction.UnitaryPilot.tvBar (fieldDataFour hK) x ⬝ᵥ x
  let t : K := s + (fieldDataFour hK).bar s0 + T
  have hT : (fieldDataFour hK).bar T = T := by
    have hs := hxs.2.2
    dsimp [T] at hs ⊢
    rw [← hs, map_add, CFSG.LocalAnalysis.ComponentInitial.UnitaryFieldData.bar_bar]
    exact add_comm _ _
  have ht : (fieldDataFour hK).bar t = t := by
    have hEq : s + (fieldDataFour hK).bar s0 =
        (fieldDataFour hK).bar s + s0 := by
      linear_combination (hxs.2.2 - hxs0.2.2) +
        ((fieldDataFour hK).bar s0 - (fieldDataFour hK).bar s) * two_eq_zero hK
    dsimp [t]
    rw [map_add, map_add, CFSG.LocalAnalysis.ComponentInitial.UnitaryFieldData.bar_bar, hT, hEq]
  have hprod : CFSG.SeitzReduction.UnitaryPilot.tvESU (fieldDataFour hK)
        (by decide : (0 : Fin 6) ≠ 1) x s hxs *
      (CFSG.SeitzReduction.UnitaryPilot.tvESU (fieldDataFour hK)
        (by decide : (0 : Fin 6) ≠ 1) x s0 hxs0)⁻¹ =
      CFSG.SeitzReduction.UnitaryPilot.tvESU (fieldDataFour hK)
        (by decide : (0 : Fin 6) ≠ 1) 0 t
        (TvCore.tvAdm_zero_of_bar_eq_self hK ht) := by
    rw [CFSG.SeitzReduction.UnitaryPilot.tvESU_inv (fieldDataFour hK)
      (by decide : (0 : Fin 6) ≠ 1) hxs0]
    rw [CFSG.SeitzReduction.UnitaryPilot.tvESU_mul (fieldDataFour hK)
      (by decide : (0 : Fin 6) ≠ 1) hxs (hxs0.bar (fieldDataFour hK))]
    have hx : x + x = 0 := by
      ext i
      exact CharTwo.add_self_eq_zero (x i)
    have hst : s + (fieldDataFour hK).bar s0 +
        CFSG.SeitzReduction.UnitaryPilot.tvBar (fieldDataFour hK) x ⬝ᵥ x = t := rfl
    rw [CFSG.SeitzReduction.UnitaryPilot.tvESU_congr (fieldDataFour hK)
      (by decide : (0 : Fin 6) ≠ 1) hx hst _ _]
  rw [← map_inv, ← map_mul, hprod]
  exact TvCore.tvESU_zero_mem_zpowers hK ht

theorem TvCore.eq_or_eq_of_le_Q (hK : Nat.card K = 4)
    {X Y : Subgroup (CFSG.ClassicalGroups.UnitaryFlag.unitaryPSU (fieldDataFour hK) 6)}
    (hXC : X ≤ TvCore.C hK) (hXc : Nat.card X = 25920)
    (hXQ : X ⊓ TvCore.Q hK = ⊥)
    (hY₁ : Subgroup.zpowers (TvCore.uZ hK) ≤ Y)
    (hY₂ : Y ≤ TvCore.Q hK)
    (hXY : X ≤ Subgroup.normalizer (Y : Set _)) :
    Y = Subgroup.zpowers (TvCore.uZ hK) ∨ Y = TvCore.Q hK := by
  haveI := charP_two_of_card_four hK
  have hW := TvCore.W_eq_bot_or_top hK hXC hXc hXQ hXY hY₁ hY₂
  rcases hW with hW | hW
  · left
    have hV : TvCore.V hK Y = ⊥ := TvCore.V_eq_bot_of_W_eq_bot hK hW
    apply le_antisymm _ hY₁
    intro y hy
    have hyQ : y ∈ TvCore.Q hK := hY₂ hy
    have hyQ' : y ∈ (TvCore.R hK).map
        (CFSG.ClassicalGroups.UnitaryFlag.unitaryProj (fieldDataFour hK) 6) := by
      simpa [TvCore.Q, CFSG.SeitzReduction.UnitaryPilot.stdTransvectionRadical,
        TvCore.R] using hyQ
    obtain ⟨r, hr, rfl⟩ := Subgroup.mem_map.mp hyQ'
    obtain ⟨x, s, hxs, rfl⟩ :=
      CFSG.SeitzReduction.UnitaryPilot.exists_eq_tvESU_of_mem_tvRadical
        (fieldDataFour hK) (by decide : (0 : Fin 6) ≠ 1) hr
    have hxsupp : ∀ i, i ∉ TvCore.J6 → x i = 0 := by
      intro i hi
      have hi' : i = 0 ∨ i = 1 := by
        by_cases h0 : i = 0
        · exact Or.inl h0
        · by_cases h1 : i = 1
          · exact Or.inr h1
          · exfalso
            apply hi
            simp [TvCore.J6, h0, h1]
      rcases hi' with rfl | rfl
      · exact hxs.1
      · exact hxs.2.1
    have hxV : x ∈ TvCore.V hK Y := ⟨hxsupp, s, hxs, hy⟩
    rw [hV, AddSubgroup.mem_bot] at hxV
    subst hxV
    have hbar : (fieldDataFour hK).bar s = s := by
      have hss : s + s = 0 := CharTwo.add_self_eq_zero s
      have h := hxs.2.2
      rw [CFSG.SeitzReduction.UnitaryPilot.tvBar_zero, zero_dotProduct] at h
      exact add_left_cancel (a := s) (by rw [h, hss])
    convert TvCore.tvESU_zero_mem_zpowers hK hbar using 2
  · right
    apply le_antisymm hY₂
    intro q hq
    have hqQ' : q ∈ (TvCore.R hK).map
        (CFSG.ClassicalGroups.UnitaryFlag.unitaryProj (fieldDataFour hK) 6) := by
      simpa [TvCore.Q, CFSG.SeitzReduction.UnitaryPilot.stdTransvectionRadical,
        TvCore.R] using hq
    obtain ⟨r, hr, rfl⟩ := Subgroup.mem_map.mp hqQ'
    obtain ⟨x, s, hxs, rfl⟩ :=
      CFSG.SeitzReduction.UnitaryPilot.exists_eq_tvESU_of_mem_tvRadical
        (fieldDataFour hK) (by decide : (0 : Fin 6) ≠ 1) hr
    have hxsupp : ∀ i, i ∉ TvCore.J6 → x i = 0 := by
      intro i hi
      have hi' : i = 0 ∨ i = 1 := by
        by_cases h0 : i = 0
        · exact Or.inl h0
        · by_cases h1 : i = 1
          · exact Or.inr h1
          · exfalso
            apply hi
            simp [TvCore.J6, h0, h1]
      rcases hi' with rfl | rfl
      · exact hxs.1
      · exact hxs.2.1
    have hxV : x ∈ TvCore.V hK Y :=
      TvCore.supported_mem_V_of_W_eq_top hK hW hxsupp
    obtain ⟨s0, h0, h0Y⟩ := hxV.2
    have hprod : (CFSG.ClassicalGroups.UnitaryFlag.unitaryProj (fieldDataFour hK) 6)
        (CFSG.SeitzReduction.UnitaryPilot.tvESU (fieldDataFour hK)
          (by decide : (0 : Fin 6) ≠ 1) x s hxs) *
        ((CFSG.ClassicalGroups.UnitaryFlag.unitaryProj (fieldDataFour hK) 6)
          (CFSG.SeitzReduction.UnitaryPilot.tvESU (fieldDataFour hK)
            (by decide : (0 : Fin 6) ≠ 1) x s0 h0))⁻¹ ∈
        Subgroup.zpowers (TvCore.uZ hK) :=
      TvCore.E_mul_E_inv_mem_zpowers hK hxs h0
    have hprodY : (CFSG.ClassicalGroups.UnitaryFlag.unitaryProj (fieldDataFour hK) 6)
        (CFSG.SeitzReduction.UnitaryPilot.tvESU (fieldDataFour hK)
          (by decide : (0 : Fin 6) ≠ 1) x s hxs) *
        ((CFSG.ClassicalGroups.UnitaryFlag.unitaryProj (fieldDataFour hK) 6)
          (CFSG.SeitzReduction.UnitaryPilot.tvESU (fieldDataFour hK)
            (by decide : (0 : Fin 6) ≠ 1) x s0 h0))⁻¹ ∈ Y :=
      hY₁ hprod
    rw [show (CFSG.ClassicalGroups.UnitaryFlag.unitaryProj (fieldDataFour hK) 6)
        (CFSG.SeitzReduction.UnitaryPilot.tvESU (fieldDataFour hK)
          (by decide : (0 : Fin 6) ≠ 1) x s hxs) =
        ((CFSG.ClassicalGroups.UnitaryFlag.unitaryProj (fieldDataFour hK) 6)
          (CFSG.SeitzReduction.UnitaryPilot.tvESU (fieldDataFour hK)
            (by decide : (0 : Fin 6) ≠ 1) x s hxs) *
          ((CFSG.ClassicalGroups.UnitaryFlag.unitaryProj (fieldDataFour hK) 6)
            (CFSG.SeitzReduction.UnitaryPilot.tvESU (fieldDataFour hK)
              (by decide : (0 : Fin 6) ≠ 1) x s0 h0))⁻¹) *
          (CFSG.ClassicalGroups.UnitaryFlag.unitaryProj (fieldDataFour hK) 6)
            (CFSG.SeitzReduction.UnitaryPilot.tvESU (fieldDataFour hK)
              (by decide : (0 : Fin 6) ≠ 1) x s0 h0) from by group]
    exact Y.mul_mem hprodY h0Y

theorem TvCore.eq_or_eq_of_le_pCoreOf_centralizer_tZero (hK : Nat.card K = 4)
    {X Y : Subgroup (LargeEvenProj (LargeEvenSUGroup (Fin 6) K (2 ^ 1)))}
    (hX : X ≤ Subgroup.centralizer {tZero hK})
    (hXc : Nat.card X = 25920)
    (hXQ : X ⊓ pCoreOf 2 (Subgroup.centralizer {tZero hK}) = ⊥)
    (hY₁ : Subgroup.zpowers (tZero hK) ≤ Y)
    (hY₂ : Y ≤ pCoreOf 2 (Subgroup.centralizer {tZero hK}))
    (hXY : X ≤ Subgroup.normalizer (Y : Set (LargeEvenProj (LargeEvenSUGroup (Fin 6) K (2 ^ 1))))) :
    Y = Subgroup.zpowers (tZero hK) ∨
      Y = pCoreOf 2 (Subgroup.centralizer {tZero hK}) := by
  let e := largeEvenProjEquiv hK
  let X' := X.map e.symm.toMonoidHom
  let Y' := Y.map e.symm.toMonoidHom
  have huZ : e.symm (tZero hK) = TvCore.uZ hK := by
    rw [tZero_eq_largeEvenProjEquiv_stdTransvection]
    rfl
  have heuZ : e (TvCore.uZ hK) = tZero hK := by
    rw [← huZ, e.apply_symm_apply]
  have hmapQ : TvCore.Q hK =
      (pCoreOf 2 (Subgroup.centralizer {tZero hK})).map e.symm.toMonoidHom := by
    rw [TvCore.pCoreOf_centralizer_tZero_eq_map_Q hK, Subgroup.map_map]
    rw [show e.symm.toMonoidHom.comp e.toMonoidHom = MonoidHom.id _ from by ext; simp]
    simp
  have hX'C : X' ≤ TvCore.C hK := by
    intro x' hx'
    obtain ⟨x, hxX, rfl⟩ := Subgroup.mem_map.mp hx'
    have hxcent : x * tZero hK = tZero hK * x :=
      (Subgroup.mem_centralizer_singleton_iff.mp (hX hxX))
    rw [TvCore.C, Subgroup.mem_centralizer_singleton_iff]
    simpa [huZ] using congrArg e.symm hxcent
  have hXc' : Nat.card X' = 25920 := by
    rw [Subgroup.card_map_of_injective e.symm.injective]
    exact hXc
  have hXQ' : X' ⊓ TvCore.Q hK = ⊥ := by
    rw [show X' ⊓ TvCore.Q hK =
        (X ⊓ pCoreOf 2 (Subgroup.centralizer {tZero hK})).map e.symm.toMonoidHom from by
      rw [hmapQ, ← Subgroup.map_inf X (pCoreOf 2 (Subgroup.centralizer {tZero hK}))
        e.symm.toMonoidHom e.symm.injective]]
    rw [hXQ, Subgroup.map_bot]
  have hY1' : Subgroup.zpowers (TvCore.uZ hK) ≤ Y' := by
    have hmapz : (Subgroup.zpowers (tZero hK)).map e.symm.toMonoidHom =
        Subgroup.zpowers (TvCore.uZ hK) := by
      simpa [huZ] using MonoidHom.map_zpowers e.symm.toMonoidHom (tZero hK)
    rw [← hmapz]
    exact Subgroup.map_mono hY₁
  have hY2' : Y' ≤ TvCore.Q hK := by
    rw [hmapQ]
    exact Subgroup.map_mono hY₂
  have hXY' : X' ≤ Subgroup.normalizer (Y' : Set _) := by
    refine le_trans (Subgroup.map_mono hXY) ?_
    exact Subgroup.le_normalizer_map e.symm.toMonoidHom
  rcases TvCore.eq_or_eq_of_le_Q hK hX'C hXc' hXQ' hY1' hY2' hXY' with h | h
  · left
    have hYmap : Y = (Subgroup.zpowers (TvCore.uZ hK)).map e.toMonoidHom := by
      rw [← h, Subgroup.map_map]
      simp
    rw [hYmap]
    simpa [heuZ] using MonoidHom.map_zpowers e.toMonoidHom (TvCore.uZ hK)
  · right
    have hYmap : Y = (TvCore.Q hK).map e.toMonoidHom := by
      rw [← h, Subgroup.map_map]
      simp
    rw [hYmap, ← TvCore.pCoreOf_centralizer_tZero_eq_map_Q hK]

theorem eq_or_eq_of_le_pCoreOf_centralizer_tZero (hK : Nat.card K = 4)
    {X Y : Subgroup (LargeEvenProj (LargeEvenSUGroup (Fin 6) K (2 ^ 1)))}
    (hX : X ≤ Subgroup.centralizer {tZero hK}) (hXc : Nat.card X = 25920)
    (hXQ : X ⊓ pCoreOf 2 (Subgroup.centralizer {tZero hK}) = ⊥)
    (hY₁ : Subgroup.zpowers (tZero hK) ≤ Y)
    (hY₂ : Y ≤ pCoreOf 2 (Subgroup.centralizer {tZero hK}))
    (hXY : X ≤ Subgroup.normalizer
      (Y : Set (LargeEvenProj (LargeEvenSUGroup (Fin 6) K (2 ^ 1))))) :
    Y = Subgroup.zpowers (tZero hK) ∨ Y = pCoreOf 2 (Subgroup.centralizer {tZero hK}) := by
  exact TvCore.eq_or_eq_of_le_pCoreOf_centralizer_tZero hK hX hXc hXQ hY₁ hY₂ hXY

noncomputable abbrev TvCore.diagTwoU [Finite K] {ω : K} {i j : Fin 6} (hω : ω ^ 2 + ω + 1 = 0)
    (hij : i ≠ j) : CFSG.ClassicalGroups.UnitaryFlag.unitarySU 2 1 K 6 :=
  diagTwoSU hω hij

abbrev TvCore.torSUU (hK : Nat.card K = 4) :
    Subgroup (CFSG.ClassicalGroups.UnitaryFlag.unitarySU 2 1 K 6) :=
  show Subgroup (CFSG.ClassicalGroups.UnitaryFlag.unitarySU 2 1 K 6) from torSU K

abbrev TvCore.torU (hK : Nat.card K = 4) :
    Subgroup (CFSG.ClassicalGroups.UnitaryFlag.unitaryPSU (fieldDataFour hK) 6) :=
  (TvCore.torSUU hK).map (CFSG.ClassicalGroups.UnitaryFlag.unitaryProj (fieldDataFour hK) 6)

theorem TvCore.diagTwoSU_mem_unitaryBlock [Finite K] (hK : Nat.card K = 4) {ω : K}
    (hω : ω ^ 2 + ω + 1 = 0) {i j : Fin 6} (hij : i ≠ j)
    (hi : i ∈ ({0, 1}ᶜ : Finset (Fin 6))) (hj : j ∈ ({0, 1}ᶜ : Finset (Fin 6))) :
    TvCore.diagTwoU hω hij ∈ CFSG.SeitzReduction.UnitaryPilot.unitaryBlock (fieldDataFour hK)
      ({0, 1}ᶜ : Finset (Fin 6)) := by
  let D : CFSG.ClassicalGroups.UnitaryFlag.unitarySU 2 1 K 6 := diagTwoSU hω hij
  change D ∈ CFSG.SeitzReduction.UnitaryPilot.unitaryBlock (fieldDataFour hK)
    ({0, 1}ᶜ : Finset (Fin 6))
  have hmat : (((D : GL (Fin 6) K) : Matrix (Fin 6) (Fin 6) K)) = diagTwo ω i j :=
    coe_diagTwoSU_matrix hω hij
  rw [CFSG.SeitzReduction.UnitaryPilot.mem_unitaryBlock]
  intro a b hab
  rw [hmat, diagTwo, Matrix.diagonal_apply, Matrix.one_apply]
  by_cases hab_eq : a = b
  · subst hab_eq
    have hi' : i ∉ ({0, 1} : Finset (Fin 6)) := by simpa [Finset.mem_compl] using hi
    have hj' : j ∉ ({0, 1} : Finset (Fin 6)) := by simpa [Finset.mem_compl] using hj
    have hi0 : i ≠ 0 := fun h => hi' (by simp [h])
    have hj0 : j ≠ 0 := fun h => hj' (by simp [h])
    have hi1 : i ≠ 1 := fun h => hi' (by simp [h])
    have hj1 : j ≠ 1 := fun h => hj' (by simp [h])
    have ha : a ∈ ({0, 1} : Finset (Fin 6)) := by
      rcases hab with h | h
      · by_contra h'
        exact h (by simpa [Finset.mem_compl] using h')
      · by_contra h'
        exact h (by simpa [Finset.mem_compl] using h')
    rcases Finset.mem_insert.mp ha with h0 | h1
    · rw [h0]
      simp [diagVec_of_ne (Ne.symm hi0) (Ne.symm hj0)]
    · have ha1 : a = 1 := by simpa using h1
      rw [ha1]
      simp [diagVec_of_ne (Ne.symm hi1) (Ne.symm hj1)]
  · simp [hab_eq]

theorem TvCore.diagTwoSU_mem_centralizer [Finite K] (hK : Nat.card K = 4) {ω : K}
    (hω : ω ^ 2 + ω + 1 = 0) {i j : Fin 6} (hij : i ≠ j)
    (hi : i ∈ ({0, 1}ᶜ : Finset (Fin 6))) (hj : j ∈ ({0, 1}ᶜ : Finset (Fin 6))) :
    TvCore.diagTwoU hω hij ∈ Subgroup.centralizer
      {CFSG.SeitzReduction.UnitaryPilot.tvTransSU (fieldDataFour hK)
        (by decide : (0 : Fin 6) ≠ 1)} := by
  let D : CFSG.ClassicalGroups.UnitaryFlag.unitarySU 2 1 K 6 := diagTwoSU hω hij
  change D ∈ Subgroup.centralizer
    {CFSG.SeitzReduction.UnitaryPilot.tvTransSU (fieldDataFour hK)
      (by decide : (0 : Fin 6) ≠ 1)}
  exact CFSG.SeitzReduction.UnitaryPilot.unitaryBlock_le_centralizer_tvTransSU
    (fieldDataFour hK) (by decide : (0 : Fin 6) ≠ 1)
    (TvCore.diagTwoSU_mem_unitaryBlock hK hω hij hi hj)

theorem TvCore.diagTwoU_mem_torU [Finite K] (hK : Nat.card K = 4) {ω : K}
    (hω : ω ^ 2 + ω + 1 = 0) {i j : Fin 6} (hij : i ≠ j) :
    (CFSG.ClassicalGroups.UnitaryFlag.unitaryProj (fieldDataFour hK) 6)
      (TvCore.diagTwoU hω hij) ∈ TvCore.torU hK :=
  Subgroup.mem_map_of_mem _ (diagTwoSU_mem_torSU hω hij)

theorem TvCore.diagTwoU_mem_C [Finite K] (hK : Nat.card K = 4) {ω : K}
    (hω : ω ^ 2 + ω + 1 = 0) {i j : Fin 6} (hij : i ≠ j)
    (hi : i ∈ ({0, 1}ᶜ : Finset (Fin 6))) (hj : j ∈ ({0, 1}ᶜ : Finset (Fin 6))) :
    (CFSG.ClassicalGroups.UnitaryFlag.unitaryProj (fieldDataFour hK) 6)
      (TvCore.diagTwoU hω hij) ∈ TvCore.C hK := by
  rw [TvCore.C,
    show TvCore.uZ hK = CFSG.SeitzReduction.UnitaryPilot.stdTransvection (fieldDataFour hK)
      (by decide : (0 : Fin 6) ≠ 1) from rfl,
    CFSG.SeitzReduction.UnitaryPilot.centralizer_stdTransvection]
  exact Subgroup.mem_map_of_mem _ (TvCore.diagTwoSU_mem_centralizer hK hω hij hi hj)

theorem TvCore.diagTwoU_mem_M [Finite K] (hK : Nat.card K = 4) {ω : K}
    (hω : ω ^ 2 + ω + 1 = 0) {i j : Fin 6} (hij : i ≠ j)
    (hi : i ∈ ({0, 1}ᶜ : Finset (Fin 6))) (hj : j ∈ ({0, 1}ᶜ : Finset (Fin 6))) :
    (CFSG.ClassicalGroups.UnitaryFlag.unitaryProj (fieldDataFour hK) 6)
      (TvCore.diagTwoU hω hij) ∈ TvCore.torU hK ⊓ TvCore.C hK :=
  ⟨TvCore.diagTwoU_mem_torU hK hω hij, TvCore.diagTwoU_mem_C hK hω hij hi hj⟩

theorem TvCore.centralizer_inf_Q (hK : Nat.card K = 4) :
    Subgroup.centralizer ((TvCore.torU hK ⊓ TvCore.C hK : Subgroup _) :
        Set (CFSG.ClassicalGroups.UnitaryFlag.unitaryPSU (fieldDataFour hK) 6)) ⊓
      TvCore.Q hK = Subgroup.zpowers (TvCore.uZ hK) := by
  letI : Finite K := (fieldDataFour hK).finite
  let ω := TvCore.omegaSix hK
  have hω : ω ^ 2 + ω + 1 = 0 := TvCore.omegaSix_spec hK
  apply le_antisymm
  · intro q hq
    rw [Subgroup.mem_inf] at hq
    obtain ⟨hqC, hqQ⟩ := hq
    have hqQ' : q ∈ (TvCore.R hK).map
        (CFSG.ClassicalGroups.UnitaryFlag.unitaryProj (fieldDataFour hK) 6) := by
      simpa [TvCore.Q, CFSG.SeitzReduction.UnitaryPilot.stdTransvectionRadical,
        TvCore.R] using hqQ
    obtain ⟨r, hrR, hqr⟩ := Subgroup.mem_map.mp hqQ'
    obtain ⟨x, s, hxs, hrx⟩ :=
      CFSG.SeitzReduction.UnitaryPilot.exists_eq_tvESU_of_mem_tvRadical
        (fieldDataFour hK) (by decide : (0 : Fin 6) ≠ 1) hrR
    have hq_eq : q = (CFSG.ClassicalGroups.UnitaryFlag.unitaryProj (fieldDataFour hK) 6)
        (CFSG.SeitzReduction.UnitaryPilot.tvESU (fieldDataFour hK)
          (by decide : (0 : Fin 6) ≠ 1) x s hxs) := by
      rw [← hqr, hrx]
    have hxzero : x = 0 := by
      funext k
      by_cases hk : k ∈ ({0, 1}ᶜ : Finset (Fin 6))
      · obtain ⟨l, hl, hlk⟩ := Finset.exists_mem_ne
          (show 1 < ({0, 1}ᶜ : Finset (Fin 6)).card by decide) k
        have hkl : k ≠ l := Ne.symm hlk
        let D : CFSG.ClassicalGroups.UnitaryFlag.unitarySU 2 1 K 6 :=
          TvCore.diagTwoU (K := K) (ω := ω) hω hkl
        have hDM : (CFSG.ClassicalGroups.UnitaryFlag.unitaryProj (fieldDataFour hK) 6) D ∈
            TvCore.torU hK ⊓ TvCore.C hK :=
          TvCore.diagTwoU_mem_M hK hω hkl hk hl
        have hcommq : (CFSG.ClassicalGroups.UnitaryFlag.unitaryProj (fieldDataFour hK) 6) D *
            q = q * (CFSG.ClassicalGroups.UnitaryFlag.unitaryProj (fieldDataFour hK) 6) D :=
          (Subgroup.mem_centralizer_iff.mp hqC) _ hDM
        have hDblock : D ∈ CFSG.SeitzReduction.UnitaryPilot.unitaryBlock (fieldDataFour hK)
            ({0, 1}ᶜ : Finset (Fin 6)) :=
          TvCore.diagTwoSU_mem_unitaryBlock hK hω hkl hk hl
        have hDcommSU : D ∈ Subgroup.centralizer
            {CFSG.SeitzReduction.UnitaryPilot.tvTransSU (fieldDataFour hK)
              (by decide : (0 : Fin 6) ≠ 1)} :=
          TvCore.diagTwoSU_mem_centralizer hK hω hkl hk hl
        have hDnorm : D ∈ Subgroup.normalizer (TvCore.R hK : Set _) :=
          CFSG.SeitzReduction.UnitaryPilot.centralizer_le_normalizer_tvRadical
            (fieldDataFour hK) (by decide : (0 : Fin 6) ≠ 1) hDcommSU
        have hcommD : D * r = r * D := by
          have hc_ker : D * r * (r * D)⁻¹ ∈
              (CFSG.ClassicalGroups.UnitaryFlag.unitaryProj (fieldDataFour hK) 6).ker := by
            rw [MonoidHom.mem_ker]
            have hm : (CFSG.ClassicalGroups.UnitaryFlag.unitaryProj (fieldDataFour hK) 6)
                (D * r * (r * D)⁻¹) =
                (CFSG.ClassicalGroups.UnitaryFlag.unitaryProj (fieldDataFour hK) 6) D *
                  (CFSG.ClassicalGroups.UnitaryFlag.unitaryProj (fieldDataFour hK) 6) r *
                  ((CFSG.ClassicalGroups.UnitaryFlag.unitaryProj (fieldDataFour hK) 6) D)⁻¹ *
                  ((CFSG.ClassicalGroups.UnitaryFlag.unitaryProj (fieldDataFour hK) 6) r)⁻¹ := by
              simp [map_mul, map_inv]
              group
            rw [hm, hqr, hcommq]
            group
          have hc_R : D * r * (r * D)⁻¹ ∈ TvCore.R hK := by
            have hconjR : D * r * D⁻¹ ∈ TvCore.R hK :=
              (Subgroup.mem_normalizer_iff.mp hDnorm r).mp hrR
            rw [show D * r * (r * D)⁻¹ = (D * r * D⁻¹) * r⁻¹ by group]
            exact Subgroup.mul_mem _ hconjR (Subgroup.inv_mem _ hrR)
          have hc_bot : D * r * (r * D)⁻¹ ∈ (⊥ : Subgroup _) := by
            rw [← TvCore.R_inf_ker hK]
            exact ⟨hc_R, hc_ker⟩
          rw [Subgroup.mem_bot] at hc_bot
          exact mul_inv_eq_one.mp hc_bot
        let DM : Matrix (Fin 6) (Fin 6) K := ((D : GL (Fin 6) K) : Matrix (Fin 6) (Fin 6) K)
        obtain ⟨hxs', hconj⟩ :=
          CFSG.SeitzReduction.UnitaryPilot.conj_tvESU (fieldDataFour hK)
            (by decide : (0 : Fin 6) ≠ 1) hDblock hxs
        have heq : CFSG.SeitzReduction.UnitaryPilot.tvESU (fieldDataFour hK)
            (by decide : (0 : Fin 6) ≠ 1) (DM *ᵥ x) s hxs' =
            CFSG.SeitzReduction.UnitaryPilot.tvESU (fieldDataFour hK)
              (by decide : (0 : Fin 6) ≠ 1) x s hxs := by
          rw [hrx] at hcommD
          rw [← hconj, hcommD]
          group
        have hDx : DM *ᵥ x = x := (TvCore.tvESU_param_eq hK heq).1
        have hkval := congrFun hDx k
        have hDk : DM k k = ω := by
          change ((TvCore.diagTwoU (ω := ω) hω hkl : GL (Fin 6) K) :
            Matrix (Fin 6) (Fin 6) K) k k = ω
          rw [show TvCore.diagTwoU (ω := ω) hω hkl = diagTwoSU hω hkl from rfl]
          rw [coe_diagTwoSU_matrix, diagTwo, Matrix.diagonal_apply_eq]
          exact diagVec_self (K := K) hkl
        have hDMdiag : DM = Matrix.diagonal (diagVec ω k l) := by
          change (((TvCore.diagTwoU (ω := ω) hω hkl : GL (Fin 6) K) :
            Matrix (Fin 6) (Fin 6) K)) = Matrix.diagonal (diagVec ω k l)
          rw [show TvCore.diagTwoU (ω := ω) hω hkl = diagTwoSU hω hkl from rfl]
          rw [coe_diagTwoSU_matrix, diagTwo]
        have hDvec : (DM *ᵥ x) k = ω * x k := by
          rw [hDMdiag, Matrix.mulVec_diagonal, diagVec_self (K := K) hkl]
        have hxD : x k = ω * x k := hkval.symm.trans hDvec
        have hzero : (ω - 1) * x k = 0 := by
          rw [sub_mul, one_mul]
          exact sub_eq_zero.mpr hxD.symm
        exact (mul_eq_zero.mp hzero).resolve_left (sub_ne_zero.mpr (omega_ne_one hK hω))
      · have hk' : k ∉ ({0, 1}ᶜ : Finset (Fin 6)) := hk
        have hmem : k ∈ ({0, 1} : Finset (Fin 6)) := by
          by_contra h
          exact hk' (by simpa [Finset.mem_compl] using h)
        rcases Finset.mem_insert.mp hmem with h | h
        · rw [h]; exact hxs.1
        · have hk1 : k = 1 := by simpa using h
          rw [hk1]; exact hxs.2.1
    subst x
    have hs01 : s = 0 ∨ s = 1 := by
      have hsker : s ∈ (TvCore.trHom hK).ker := by
        rw [AddMonoidHom.mem_ker, TvCore.trHom_apply]
        have := hxs.2.2
        rw [CFSG.SeitzReduction.UnitaryPilot.tvBar_zero, zero_dotProduct] at this
        exact this
      exact (TvCore.mem_trHom_ker hK).mp hsker
    rcases hs01 with rfl | rfl
    · rw [hq_eq]
      rw [show CFSG.SeitzReduction.UnitaryPilot.tvESU (fieldDataFour hK)
          (by decide : (0 : Fin 6) ≠ 1) 0 0 hxs = 1 from by
        rw [show hxs = CFSG.SeitzReduction.UnitaryPilot.TvAdm.zero_zero (fieldDataFour hK)
          from Subsingleton.elim _ _]
        exact CFSG.SeitzReduction.UnitaryPilot.tvESU_zero_zero (fieldDataFour hK)
          (by decide : (0 : Fin 6) ≠ 1)]
      exact Subgroup.one_mem _
    · rw [hq_eq]
      rw [show CFSG.SeitzReduction.UnitaryPilot.tvESU (fieldDataFour hK)
          (by decide : (0 : Fin 6) ≠ 1) 0 1 hxs =
          CFSG.SeitzReduction.UnitaryPilot.tvTransSU (fieldDataFour hK)
            (by decide : (0 : Fin 6) ≠ 1) from by
        apply Subtype.ext
        rfl]
      exact Subgroup.mem_zpowers _
  · rw [Subgroup.zpowers_le]
    constructor
    · change ∀ g ∈ (TvCore.torU hK ⊓ TvCore.C hK),
        g * TvCore.uZ hK = TvCore.uZ hK * g
      intro g hg
      exact Subgroup.mem_centralizer_singleton_iff.mp (by simpa [TvCore.C] using hg.2)
    · exact Subgroup.mem_map_of_mem _
        (CFSG.SeitzReduction.UnitaryPilot.tvESU_mem_tvRadical (fieldDataFour hK)
          (by decide : (0 : Fin 6) ≠ 1) (CFSG.SeitzReduction.UnitaryPilot.tvAdm_one
            (fieldDataFour hK) 0 1))

theorem TvCore.map_zpowers {G H : Type*} [Group G] [Group H] (e : G ≃* H) (g : G) :
    (Subgroup.zpowers g).map e.toMonoidHom = Subgroup.zpowers (e g) := by
  apply le_antisymm
  · rw [Subgroup.map_le_iff_le_comap, Subgroup.zpowers_le, Subgroup.mem_comap]
    exact Subgroup.mem_zpowers (e g)
  · rw [Subgroup.zpowers_le]
    exact Subgroup.mem_map_of_mem _ (Subgroup.mem_zpowers g)

theorem TvCore.torU_eq_map (hK : Nat.card K = 4) :
    CFSG.StandardType.USixTwo.torU K =
      (TvCore.torU hK).map (largeEvenProjEquiv hK).toMonoidHom := by
  rw [CFSG.StandardType.USixTwo.torU, TvCore.torU, Subgroup.map_map,
    largeEvenProjEquiv_comp_unitaryProj]
  change Subgroup.map (LargeEvenProjMk (LargeEvenSUGroup (Fin 6) K (2 ^ 1))) (torSU K) =
    Subgroup.map (LargeEvenProjMk (LargeEvenSUGroup (Fin 6) K (2 ^ 1))) (TvCore.torSUU hK)
  rfl

theorem TvCore.centralizer_inf_pCoreOf_centralizer_tZero (hK : Nat.card K = 4) :
    Subgroup.centralizer ((CFSG.StandardType.USixTwo.torU K ⊓
        Subgroup.centralizer {tZero hK} : Subgroup _) :
        Set (LargeEvenProj (LargeEvenSUGroup (Fin 6) K (2 ^ 1)))) ⊓
      pCoreOf 2 (Subgroup.centralizer {tZero hK}) = Subgroup.zpowers (tZero hK) := by
  have htor := TvCore.torU_eq_map hK
  have hC := TvCore.centralizer_tZero_eq_map hK
  have hQ := TvCore.pCoreOf_centralizer_tZero_eq_map_Q hK
  rw [htor, hQ, hC]
  rw [← Subgroup.map_inf (TvCore.torU hK) (TvCore.C hK)
    (largeEvenProjEquiv hK).toMonoidHom (largeEvenProjEquiv hK).injective]
  rw [Subgroup.coe_map]
  change Subgroup.centralizer ((largeEvenProjEquiv hK) ''
      (↑(TvCore.torU hK ⊓ TvCore.C hK) : Set _)) ⊓
    Subgroup.map (largeEvenProjEquiv hK).toMonoidHom (TvCore.Q hK) =
    Subgroup.zpowers (tZero hK)
  rw [← TvCore.map_centralizer_bijective (largeEvenProjEquiv hK)
    ((TvCore.torU hK ⊓ TvCore.C hK : Subgroup _) : Set _)]
  rw [Subgroup.coe_inf]
  change Subgroup.map (largeEvenProjEquiv hK).toMonoidHom
      (Subgroup.centralizer ((TvCore.torU hK : Set _) ⊓ (TvCore.C hK : Set _))) ⊓
    Subgroup.map (largeEvenProjEquiv hK).toMonoidHom (TvCore.Q hK) =
    Subgroup.zpowers (tZero hK)
  rw [← Subgroup.map_inf
    (Subgroup.centralizer ((TvCore.torU hK : Set _) ⊓ (TvCore.C hK : Set _)))
    (TvCore.Q hK) (largeEvenProjEquiv hK).toMonoidHom (largeEvenProjEquiv hK).injective]
  change Subgroup.map (largeEvenProjEquiv hK).toMonoidHom
      (Subgroup.centralizer ((TvCore.torU hK ⊓ TvCore.C hK : Subgroup _) : Set _) ⊓
        TvCore.Q hK) = Subgroup.zpowers (tZero hK)
  rw [TvCore.centralizer_inf_Q hK]
  rw [TvCore.map_zpowers]
  rw [show tZero hK = (largeEvenProjEquiv hK) (TvCore.uZ hK) from by
    rw [TvCore.uZ]
    exact tZero_eq_largeEvenProjEquiv_stdTransvection hK]

theorem centralizer_inf_pCoreOf_centralizer_tZero (hK : Nat.card K = 4) :
    Subgroup.centralizer ((torU K ⊓ Subgroup.centralizer {tZero hK} : Subgroup _) :
        Set (LargeEvenProj (LargeEvenSUGroup (Fin 6) K (2 ^ 1)))) ⊓
      pCoreOf 2 (Subgroup.centralizer {tZero hK}) = Subgroup.zpowers (tZero hK) := by
  exact TvCore.centralizer_inf_pCoreOf_centralizer_tZero hK

theorem card_blockFourU (hK : Nat.card K = 4) : Nat.card (blockFourU hK) = 25920 := by
  rw [blockFourU_eq_map_blockSU]
  rw [Subgroup.card_map_of_injective (largeEvenProjEquiv hK).injective]
  obtain ⟨e⟩ := CFSG.SeitzReduction.UnitaryPilot.blockSU_mulEquiv (fieldDataFour hK)
    ({0, 1}ᶜ : Finset (Fin 6)) (by decide : ({0, 1}ᶜ : Finset (Fin 6)).card < 6)
  rw [Nat.card_congr e.toEquiv]
  exact card_unitarySU_four hK

theorem isSimpleGroup_blockFourU (hK : Nat.card K = 4) : IsSimpleGroup (blockFourU hK) := by
  rw [blockFourU_eq_map_blockSU]
  have hblock := isSimpleGroup_blockSU hK
  let e := MulEquiv.subgroupMap (largeEvenProjEquiv hK)
    (CFSG.SeitzReduction.UnitaryPilot.blockSU (fieldDataFour hK) ({0, 1}ᶜ : Finset (Fin 6)))
  exact (MulEquiv.isSimpleGroup_congr e).mp hblock

theorem unitaryBlock_commute_threeAMatrix (hK : Nat.card K = 4) {ω : K}
    (hω : ω ^ 2 + ω + 1 = 0) {m : LargeEvenSUGroup (Fin 6) K (2 ^ 1)}
    (hm : m ∈ tvBlockSix hK) :
    ((m : GL (Fin 6) K) : Matrix (Fin 6) (Fin 6) K) * threeAMatrix ω =
      threeAMatrix ω * ((m : GL (Fin 6) K) : Matrix (Fin 6) (Fin 6) K) := by
  have hM := (CFSG.SeitzReduction.UnitaryPilot.mem_unitaryBlock (fieldDataFour hK)).1 hm
  rw [threeAMatrix]
  ext a b
  rw [Matrix.mul_diagonal, Matrix.diagonal_mul]
  fin_cases a <;> fin_cases b <;>
    simp [hM, Matrix.one_apply]

theorem blockFourU_le_centralizer_threeA (hK : Nat.card K = 4) {ω : K}
    (hω : ω ^ 2 + ω + 1 = 0) : blockFourU hK ≤ Subgroup.centralizer {threeA hω} := by
  intro x hx
  have hx' : x ∈ (tvBlockSix hK).map
      (LargeEvenProjMk (LargeEvenSUGroup (Fin 6) K (2 ^ 1))) := hx
  rw [Subgroup.mem_map] at hx'
  obtain ⟨m, hm, rfl⟩ := hx'
  rw [Subgroup.mem_centralizer_singleton_iff]
  rw [threeA, ← map_mul, ← map_mul]
  congr 1
  apply Subtype.ext
  apply Units.ext
  exact unitaryBlock_commute_threeAMatrix hK hω hm

end CFSG.StandardType.USixTwo

end
