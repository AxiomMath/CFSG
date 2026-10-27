module

public import CFSG.LocalAnalysis.ComponentInitial.UnitaryHigherPrimeForm

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

open CFSG.ClassicalGroups.UnitaryFlag
open CFSG.LocalAnalysis.ComponentInitial (UnitaryFieldData)
open CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher

variable {K : Type} [Field K] {n : ℕ}

theorem uc22s218_u4_glAut_mem (h : UnitaryFieldData 2 n K) (θ : K ≃+* K) {g : GL (Fin 4) K}
    (hg : g ∈ unitarySU 2 n K 4) : glAut θ g ∈ unitarySU 2 n K 4 := by
  have hC : IsPrimeFormGram (1 : GL (Fin 4) K) := by
    refine ⟨by simp, fun i j => ?_⟩
    simp only [Units.val_one, Matrix.one_apply]
    split_ifs
    · exact one_mem _
    · exact zero_mem _
  rw [unitarySU_eq_gramSU h] at hg ⊢
  exact glAut_mem_gramSU h hC θ hg

@[expose] noncomputable def uc22s218_u4_field (h : UnitaryFieldData 2 n K) :
    (K ≃+* K) →* MulAut ↥(unitarySU 2 n K 4) where
  toFun θ :=
    { toFun := fun s => ⟨glAut θ (s : GL (Fin 4) K), uc22s218_u4_glAut_mem h θ s.2⟩
      invFun := fun s => ⟨glAut θ⁻¹ (s : GL (Fin 4) K), uc22s218_u4_glAut_mem h θ⁻¹ s.2⟩
      left_inv := fun s => Subtype.ext (by
        change glAut θ⁻¹ (glAut θ (s : GL (Fin 4) K)) = s
        rw [← MulAut.mul_apply, ← map_mul, inv_mul_cancel, map_one, MulAut.one_apply])
      right_inv := fun s => Subtype.ext (by
        change glAut θ (glAut θ⁻¹ (s : GL (Fin 4) K)) = s
        rw [← MulAut.mul_apply, ← map_mul, mul_inv_cancel, map_one, MulAut.one_apply])
      map_mul' := fun s t => Subtype.ext (map_mul (glAut θ) (s : GL (Fin 4) K) t) }
  map_one' := MulEquiv.ext fun s => Subtype.ext (by
    change glAut 1 (s : GL (Fin 4) K) = s
    rw [map_one]
    rfl)
  map_mul' θ ψ := MulEquiv.ext fun s => Subtype.ext (by
    change glAut (θ * ψ) (s : GL (Fin 4) K) = glAut θ (glAut ψ (s : GL (Fin 4) K))
    rw [map_mul]
    rfl)

theorem uc22s218_u4_field_conj (h : UnitaryFieldData 2 n K) (θ : K ≃+* K)
    (s : ↥(unitarySU 2 n K 4)) :
    uc22s218_u4_field h θ * MulAut.conj s * (uc22s218_u4_field h θ)⁻¹ =
      MulAut.conj (uc22s218_u4_field h θ s) := by
  refine MulEquiv.ext fun t => ?_
  rw [MulAut.mul_apply, MulAut.mul_apply, MulAut.conj_apply, MulAut.conj_apply, map_mul, map_mul,
    map_inv]
  congr 3
  rw [MulAut.inv_apply, MulEquiv.apply_symm_apply]

end CFSG.LocalAnalysis.UniquenessCase.UC22
