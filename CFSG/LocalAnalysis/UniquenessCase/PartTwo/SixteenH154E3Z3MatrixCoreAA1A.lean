module

public import CFSG.LinearAlgebra.FixedPointFreeOrderThreeField
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalSemilinearCoordinates
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenH154E3Z3F4Facts1
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenH154E3Z3F4Facts3
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenH154E3Z3F4Facts4
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenH154E3Z3F4Facts5
public import CFSG.GroupTheory.SteinbergBKSemilinearFixedBasis
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenH154E3Z3NormalFive
public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.PCore.PCore
public import CFSG.GroupTheory.ElementaryAbelianTransport
public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.BGsection4.lemma_4_5_a
public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Card
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.LocalCriterionDenominatorLinear

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.LinearAlgebra CFSG.ComponentClassification.CatalogueBOrthogonalSemilinear Subgroup
  CFSG.Open

local notation "G3F4" => Matrix.GeneralLinearGroup (Fin 3) OmegaField

theorem s16h_e3_Z3MatrixCoreAA1A_three_subgroup_cyclic
    {K' : Subgroup G3F4}
    (hno : ∀ P : Subgroup G3F4, P ≤ K' →
      CFSG.Open.IsElemAbelian 3 P → Nat.card ↥P < 9)
    {R : Subgroup G3F4} (hRK : R ≤ K') (hR : IsPGroup 3 R) :
    IsCyclic ↥R := by
  by_contra hnc
  haveI : Finite OmegaField := by
    haveI : Module.Finite (ZMod 2) OmegaField := (AdjoinRoot.powerBasis' omegaPoly_monic).finite
    exact Module.finite_of_finite (ZMod 2)
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  haveI : Fact (IsPGroup 3 ↥R) := ⟨hR⟩
  obtain ⟨S, -, hScard, hS⟩ := CFSG.lemma_4_5_a (R := ↥R) (p := 3) (by norm_num) hnc
  have hSel : CFSG.Open.IsElemAbelian 3 S :=
    CFSG.Open.isElemAbelian_iff_isElementaryAbelian.mpr hS
  have hmapel : CFSG.Open.IsElemAbelian 3 (S.map R.subtype) := hSel.map R.subtype
  have hcard : Nat.card ↥(S.map R.subtype) = 9 := by
    rw [Subgroup.card_map_of_injective R.subtype_injective, hScard]
    norm_num
  have hlt := hno (S.map R.subtype) ((Subgroup.map_subtype_le S).trans hRK) hmapel
  rw [hcard] at hlt
  exact absurd hlt (by norm_num)

theorem s16h_e3_Z3MatrixCoreAA1A_scalar_le_center :
    (MonoidHom.range (Matrix.GeneralLinearGroup.scalar (Fin 3) : OmegaFieldˣ →*
      Matrix.GeneralLinearGroup (Fin 3) OmegaField)) ≤
      Subgroup.center (Matrix.GeneralLinearGroup (Fin 3) OmegaField) := by
  rintro x ⟨c, rfl⟩
  rw [Subgroup.mem_center_iff]
  intro A
  exact (Matrix.GeneralLinearGroup.scalar_commute c A).symm

theorem s16h_e3_Z3MatrixCoreAA1A_scalar_card :
    Nat.card ↥(MonoidHom.range (Matrix.GeneralLinearGroup.scalar (Fin 3) : OmegaFieldˣ →*
      Matrix.GeneralLinearGroup (Fin 3) OmegaField)) = 3 := by
  have hinj : Function.Injective (Matrix.GeneralLinearGroup.scalar (Fin 3) :
      OmegaFieldˣ →* Matrix.GeneralLinearGroup (Fin 3) OmegaField) := by
    intro a b hab
    apply Units.ext
    have h := congrArg (fun A : Matrix.GeneralLinearGroup (Fin 3) OmegaField =>
      (A : Matrix (Fin 3) (Fin 3) OmegaField)) hab
    rw [Matrix.GeneralLinearGroup.coe_scalar, Matrix.GeneralLinearGroup.coe_scalar] at h
    exact Matrix.scalar_inj.mp h
  haveI : Finite OmegaField := by
    haveI : Module.Finite (ZMod 2) OmegaField := (AdjoinRoot.powerBasis' omegaPoly_monic).finite
    exact Module.finite_of_finite (ZMod 2)
  rw [MonoidHom.range_eq_map, Subgroup.card_map_of_injective hinj, Subgroup.card_top,
    Nat.card_units, s16h_e3_z3_card_omegaField_eq_four]

theorem s16h_e3_Z3MatrixCoreAA1A_normal_two_eq_bot_of_le_normal
    {G : Type*} [Group G] {D K : Subgroup G} (hDK : D ≤ K)
    (hDKnormal : (D.subgroupOf K).Normal)
    (hO2 : ∀ P : Subgroup G, P ≤ K → (P.subgroupOf K).Normal → IsPGroup 2 P → P = ⊥) :
    ∀ P : Subgroup ↥D, P.Normal → IsPGroup 2 P → P = ⊥ := by
  intro P hPN hP2
  have hPle : P ≤ CFSG.pCore 2 ↥D :=
    le_sSup (show P ∈ {Q : Subgroup ↥D | Q.Normal ∧ IsPGroup 2 Q} from ⟨hPN, hP2⟩)
  have hRchar : (CFSG.pCore 2 ↥D).Characteristic := inferInstance
  have hR2 : IsPGroup 2 (CFSG.pCore 2 ↥D) := CFSG.pCore_isPGroup (p := 2) (G := ↥D)
  have hRmap_le : (CFSG.pCore 2 ↥D).map D.subtype ≤ K :=
    (Subgroup.map_subtype_le (CFSG.pCore 2 ↥D)).trans hDK
  have hRmap_norm : (((CFSG.pCore 2 ↥D).map D.subtype).subgroupOf K).Normal := by
    rw [Subgroup.normal_subgroupOf_iff hRmap_le]
    intro x k hx hk
    obtain ⟨y, hy, rfl⟩ := Subgroup.mem_map.mp hx
    let α : ↥D ≃* ↥D := {
      toFun := fun z =>
        ⟨k * z.1 * k⁻¹, (Subgroup.normal_subgroupOf_iff hDK).mp hDKnormal z.1 k z.2 hk⟩
      invFun := fun z =>
        ⟨k⁻¹ * z.1 * (k⁻¹)⁻¹, (Subgroup.normal_subgroupOf_iff hDK).mp hDKnormal z.1 k⁻¹ z.2
          (K.inv_mem hk)⟩
      left_inv := by intro z; ext; group
      right_inv := by intro z; ext; group
      map_mul' := by
        intro a b
        ext
        simp only [Subgroup.coe_mul]
        group }
    have hαy : α y ∈ CFSG.pCore 2 ↥D := by
      rw [← Subgroup.characteristic_iff_map_eq.mp hRchar α]
      exact Subgroup.mem_map.mpr ⟨y, hy, rfl⟩
    exact Subgroup.mem_map.mpr ⟨α y, hαy, rfl⟩
  have hRmap_bot : (CFSG.pCore 2 ↥D).map D.subtype = ⊥ :=
    hO2 _ hRmap_le hRmap_norm (hR2.map D.subtype)
  have hRbot : CFSG.pCore 2 ↥D = ⊥ := by
    apply Subgroup.map_injective D.subtype_injective
    rw [hRmap_bot, Subgroup.map_bot]
  exact le_bot_iff.mp (hPle.trans (le_of_eq hRbot))

theorem s16h_e3_Z3MatrixCoreAA1A_card_SL :
    Nat.card ↥(Matrix.GeneralLinearGroup.det (n := Fin 3) (R := OmegaField)).ker =
      2 ^ 6 * 3 ^ 3 * 5 * 7 := by
  haveI : Finite OmegaField := by
    haveI : Module.Finite (ZMod 2) OmegaField := (AdjoinRoot.powerBasis' omegaPoly_monic).finite
    exact Module.finite_of_finite (ZMod 2)
  have hGL : Nat.card (Matrix.GeneralLinearGroup (Fin 3) OmegaField) = 181440 :=
    s16h_e3_z3_card_gl
  rw [← Nat.card_congr
    (Matrix.SpecialLinearGroup.toGLKerEquiv (n := Fin 3) (R := OmegaField)).toEquiv]
  rw [Matrix.card_SL (n := Fin 3) (R := OmegaField), hGL, Nat.card_units,
    s16h_e3_z3_card_omegaField_eq_four]
  norm_num

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
