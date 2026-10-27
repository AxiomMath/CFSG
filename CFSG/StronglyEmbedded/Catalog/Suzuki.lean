module

public import CFSG.StronglyEmbedded.Catalog.Basic
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.MatrixGroups.Suzuki
public import TauCeti.GroupTheory.SpecificGroups.CFSG.Classification
public import TauCeti.GroupTheory.SpecificGroups.CFSG.Suzuki.Candidate
import all TauCeti.GroupTheory.SpecificGroups.CFSG.Assembly.LieType
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.MatrixGroups.PSL2
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.MatrixGroups.Unitary

public section

namespace CFSG.BenderSuzuki.Catalog

open TauCeti Matrix _root_.CFSG.BenderSuzuki.MatrixGroups

variable (m : ℕ)

local notation "F" => GaloisField 2 (2 * m + 1)

private theorem pow_two_pow_succ_sq (x : F) : (x ^ 2 ^ (m + 1)) ^ 2 ^ (m + 1) = x ^ 2 := by
  have h := galoisField_pow_card (p := 2) (k := 2 * m + 1) (by omega) x
  rw [← pow_mul, ← pow_add, show m + 1 + (m + 1) = 2 * m + 1 + 1 by omega, pow_succ, pow_mul, h]

theorem inverseTranspose_unipotent (a b : F) :
    GeneralLinearGroup.inverseTranspose (Suzuki.unipotent m a b) = SuzukiRootGL m a b := by
  have htwo : (2 : F) = 0 := CharTwo.two_eq_zero
  have hsq := pow_two_pow_succ_sq m a
  apply Matrix.GeneralLinearGroup.ext
  intro i j
  rw [GeneralLinearGroup.coe_inverseTranspose, Suzuki.unipotent_inv, Suzuki.coe_unipotent]
  simp only [SuzukiRootGL, Matrix.GeneralLinearGroup.mkOfDetNeZero, SuzukiRootMatrix]
  fin_cases i <;> fin_cases j <;>
    simp [add_pow_char_pow, mul_pow, hsq]
  all_goals ring_nf
  all_goals first
    | linear_combination (a * a ^ (2 ^ m * 2)) * htwo
    | linear_combination (a ^ 2 * a ^ (2 ^ m * 2)) * htwo

theorem inverseTranspose_weyl :
    GeneralLinearGroup.inverseTranspose (Suzuki.weyl m) = SuzukiWeylGL m := by
  apply Matrix.GeneralLinearGroup.ext
  intro i j
  rw [GeneralLinearGroup.coe_inverseTranspose, Suzuki.weyl_inv, Suzuki.coe_weyl]
  fin_cases i <;> fin_cases j <;> simp [SuzukiWeylGL, SuzukiWeylMatrix]

theorem inverseTranspose_torus (x : (GaloisField 2 (2 * m + 1))ˣ) :
    GeneralLinearGroup.inverseTranspose (Suzuki.torus m (x ^ (1 + 2 ^ m))⁻¹) =
      SuzukiTorusGL m x := by
  have hx : (x : F) ≠ 0 := x.ne_zero
  have hpow : ((x : F) ^ (1 + 2 ^ m)) ^ 2 ^ (m + 1) = (x : F) ^ 2 ^ (m + 1) * x := by
    have h := galoisField_pow_card (p := 2) (k := 2 * m + 1) (by omega) (x : F)
    rw [← pow_mul, show (1 + 2 ^ m) * 2 ^ (m + 1) = 2 ^ (m + 1) + 2 ^ (2 * m + 1) by ring,
      pow_add, h]
  have hsucc : (x : F) ^ 2 ^ (m + 1) = (x : F) ^ 2 ^ m * (x : F) ^ 2 ^ m := by
    rw [pow_succ, pow_mul, sq]
  apply Matrix.GeneralLinearGroup.ext
  intro i j
  rw [GeneralLinearGroup.coe_inverseTranspose, ← map_inv, inv_inv, Suzuki.coe_torus]
  simp only [SuzukiTorusGL, Matrix.GeneralLinearGroup.mkOfDetNeZero, SuzukiTorusMatrix]
  fin_cases i <;> fin_cases j <;> simp [hpow]
  all_goals field_simp
  all_goals rw [hsucc]; ring

theorem map_inverseTranspose_suzukiGroup :
    (suzukiGroup m).map (GeneralLinearGroup.inverseTranspose.toMonoidHom) =
      SuzukiMatrixGroup m := by
  have hgen := Suzuki.suzukiGroup_le_iff.mp (le_refl (suzukiGroup m))
  apply le_antisymm
  · rw [Subgroup.map_le_iff_le_comap, Suzuki.suzukiGroup_le_iff]
    refine ⟨fun a b => ?_, ?_⟩
    · rw [Subgroup.mem_comap, MulEquiv.coe_toMonoidHom, inverseTranspose_unipotent]
      exact Subgroup.subset_closure (Or.inl ⟨a, b, rfl⟩)
    · rw [Subgroup.mem_comap, MulEquiv.coe_toMonoidHom, inverseTranspose_weyl]
      exact Subgroup.subset_closure (Or.inr (Or.inr rfl))
  · rw [SuzukiMatrixGroup, SuzukiMatrixSubgroup, Subgroup.closure_le]
    rintro _ (⟨a, b, rfl⟩ | ⟨x, rfl⟩ | rfl)
    · exact ⟨_, hgen.1 a b, inverseTranspose_unipotent m a b⟩
    · exact ⟨_, Suzuki.torus_mem_suzukiGroup m _, inverseTranspose_torus m x⟩
    · exact ⟨_, hgen.2, inverseTranspose_weyl m⟩

noncomputable def suzukiGroupEquiv : suzukiGroup m ≃* SuzukiMatrixGroup m :=
  ((suzukiGroup m).equivMapOfInjective _
      (GeneralLinearGroup.inverseTranspose (n := Fin 4) (A := F)).injective).trans
    (MulEquiv.subgroupCongr (map_inverseTranspose_suzukiGroup m))

variable {m} in
noncomputable def groupEquivSuzukiMatrixGroup (hv : (LieTypeIndex.suzuki m).Valid) :
    ValidLieTypeIndex.Group ⟨_, hv⟩ ≃* SuzukiMatrixGroup m :=
  (SuzukiLieIndex.groupEquivSuzukiGroup m hv).trans (suzukiGroupEquiv m)

end CFSG.BenderSuzuki.Catalog
