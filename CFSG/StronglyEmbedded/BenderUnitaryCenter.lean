module

public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.External.Huppert.II.theorem_10_12
import CFSG.Adapters.QiuzhenLegacy.BenderSuzuki.Background.Huppert.II.theorem_10_12

public section

namespace CFSG.BenderSuzuki.External

open CFSG.BenderSuzuki.MatrixGroups
open scoped Matrix commutatorElement

noncomputable section

theorem hermitianUnipotent_commutator_pow_two
    {K : Type*} [Field K] [CharP K 2] {n : ℕ} (J : HermitianForm n K)
    (z : hermitianUnipotentCoord J) (hz : z ∈ commutator (hermitianUnipotentCoord J)) :
    z ^ 2 = 1 := by
  let Z : Subgroup (hermitianUnipotentCoord J) :=
    { carrier := {z | z.1.1 = 0}
      one_mem' := rfl
      mul_mem' := by
        intro x y hx hy
        change x.1.1 + y.1.1 = 0
        rw [hx, hy, zero_add]
      inv_mem' := by
        intro x hx
        change -x.1.1 = 0
        rw [hx, neg_zero] }
  have hcomm : commutator (hermitianUnipotentCoord J) ≤ Z := by
    apply Subgroup.commutator_le.mpr
    intro x _ y _
    exact CFSG.BenderSuzuki.Background.hermitianUnipotent_commutator_fst J x y
  have hfirst : z.1.1 = 0 := hcomm hz
  rw [pow_two]
  change hermitianUnipotentMul J z z = hermitianUnipotentOne J
  apply Subtype.ext
  apply Prod.ext
  · simp [hermitianUnipotentMul, hermitianUnipotentOne, hfirst]
  · simp [hermitianUnipotentMul, hermitianUnipotentOne, hfirst,
      CharTwo.add_self_eq_zero]

theorem hermitianRoot_center_pow_two_of_coordinates
    {K : Type*} [Field K] [CharP K 2] (J : HermitianForm 3 K)
    (hJ : J.form = !![0, 0, 1; 0, 1, 0; 1, 0, 0])
    (R : Subgroup (ProjectiveSpecialUnitaryMatrixGroup J))
    (hcomm : commutator R = Subgroup.center R)
    (coord : hermitianUnipotentCoord J ≃ R)
    (hcoord : ∀ z : hermitianUnipotentCoord J,
      ∃ M : GL (Fin 3) K,
        (M : Matrix (Fin 3) (Fin 3) K) =
          !![1, z.1.1, z.1.2; 0, 1, -J.conj z.1.1; 0, 0, 1] ∧
        (((coord z : R) : ProjectiveSpecialUnitaryMatrixGroup J) :
          Matrix.ProjGenLinGroup (Fin 3) K) = Matrix.ProjGenLinGroup.mk M) :
    ∀ r ∈ Subgroup.center R, r ^ 2 = 1 := by
  let f := hermitianUnipotentPSU J hJ
  have hmatch (z : hermitianUnipotentCoord J) : (coord z : _) = f z := by
    obtain ⟨M, hM, hproj⟩ := hcoord z
    have hMeq : M = hermitianUnipotentGL J z := by
      apply Matrix.GeneralLinearGroup.ext
      intro i j
      rw [hM, hermitianUnipotentGL_val, hermitianUnipotentMatrix_eq]
    apply Subtype.ext
    simpa only [f, hermitianUnipotentPSU_val, hMeq] using hproj
  have hrange : f.range = R := by
    ext x
    constructor
    · rintro ⟨z, rfl⟩
      rw [← hmatch]
      exact (coord z).property
    · intro hx
      obtain ⟨z, hz⟩ := coord.surjective ⟨x, hx⟩
      exact ⟨z, (hmatch z).symm.trans (congrArg Subtype.val hz)⟩
  let e : hermitianUnipotentCoord J ≃* R :=
    (MulEquiv.ofBijective f.rangeRestrict
      ⟨MonoidHom.rangeRestrict_injective_iff.mpr
        (CFSG.BenderSuzuki.Background.hermitianUnipotentPSU_injective J hJ), f.rangeRestrict_surjective⟩).trans
        (MulEquiv.subgroupCongr hrange)
  have hcomm_map : (commutator (hermitianUnipotentCoord J)).map e.toMonoidHom =
      commutator R := by
    change (⁅(⊤ : Subgroup (hermitianUnipotentCoord J)), ⊤⁆ :
      Subgroup (hermitianUnipotentCoord J)).map e.toMonoidHom = _
    rw [Subgroup.map_commutator, Subgroup.map_top_of_surjective _ e.surjective]
    rfl
  intro r hr
  have hrcomm : r ∈ commutator R := hcomm ▸ hr
  rw [← hcomm_map] at hrcomm
  obtain ⟨z, hz, rfl⟩ := hrcomm
  simpa using congrArg e (hermitianUnipotent_commutator_pow_two J z hz)

end

end CFSG.BenderSuzuki.External
