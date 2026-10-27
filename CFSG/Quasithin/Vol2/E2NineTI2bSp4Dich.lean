module

public import CFSG.Quasithin.Vol2.E2NineTI2bQU
public import CFSG.Quasithin.Vol2.E2NineTI2bSp4Corner

public section

namespace CFSG.Quasithin.E2.TI2b.Sp4

open Matrix CFSG.ComponentClassification.UnbalancedCatalog.SpChain
open CFSG.Quasithin.SteinbergBS (rootLong rootShort)
open CFSG.Open CFSG.QuasithinUnique B6

variable {k : Type} [Field k] [CharP k 2]

@[expose] def ρ4 (k : Type) [Field k] : antiSp k →* Matrix (Fin 4) (Fin 4) k where
  toFun g := glMat (g : GL (Fin 4) k)
  map_one' := rfl
  map_mul' _ _ := rfl

theorem ρ4_injective : Function.Injective (ρ4 k) := fun _ _ h => antiSp_ext h

private theorem ρ4_apply (g : antiSp k) : ρ4 k g = glMat (g : GL (Fin 4) k) := rfl

private theorem ρ4_long_sub_one_mulVec (t : k) (x : Fin 4 → k) :
    (ρ4 k (uElt 0 0 t 0) - 1) *ᵥ x = (t * x 3) • (Pi.single 0 1 : Fin 4 → k) := by
  rw [ρ4_apply, CFSG.Quasithin.SteinbergBS.glMat_uElt_long]
  ext i
  fin_cases i <;> simp [Matrix.mulVec, dotProduct, Fin.sum_univ_four, Pi.single_apply,
    Matrix.single_apply]

theorem dich_rootLong [Finite k] (hk : 4 ≤ Nat.card k) {Y : Subgroup (antiSp k)}
    (hY : rootLong k ≤ Y) : Dich (rootLong k) Y := by
  have : Finite (antiSp k) := Finite.of_injective _ (ρ4_injective (k := k))
  by_cases h30 : ∃ y ∈ Y, glMat (y : GL (Fin 4) k) 3 0 ≠ 0
  · obtain ⟨y, hyY, hy⟩ := h30
    obtain ⟨f, hf, hfY, hzf⟩ := exists_sl2_le_of_orbit hY hyY hy
    exact dich_of_sl2_range hk hf hfY hzf
  · push Not at h30
    left
    set U : Submodule k (Fin 4 → k) := Submodule.span k
      {v | ∃ y ∈ Y, v = glMat (y : GL (Fin 4) k) *ᵥ (Pi.single 0 1 : Fin 4 → k)}
    have hUinv : ∀ y ∈ Y, ∀ u ∈ U, ρ4 k y *ᵥ u ∈ U := by
      intro y hy
      have hle : U ≤ U.comap (Matrix.mulVecLin (ρ4 k y)) := by
        refine Submodule.span_le.mpr ?_
        rintro _ ⟨z, hz, rfl⟩
        refine Submodule.subset_span ⟨y * z, Y.mul_mem hy hz, ?_⟩
        rw [Matrix.mulVecLin_apply, Matrix.mulVec_mulVec]
        rfl
      intro u hu
      exact hle hu
    have hU3 : ∀ u ∈ U, u 3 = 0 := by
      intro u hu
      have hle : U ≤ LinearMap.ker (LinearMap.proj (R := k) (φ := fun _ : Fin 4 => k) 3) := by
        refine Submodule.span_le.mpr ?_
        rintro _ ⟨z, hz, rfl⟩
        have := h30 z hz
        simpa [Matrix.mulVec, dotProduct, Fin.sum_univ_four, Pi.single_apply] using this
      simpa using hle hu
    have he0 : (Pi.single 0 1 : Fin 4 → k) ∈ U :=
      Submodule.subset_span ⟨1, Y.one_mem, by simp only [Subgroup.coe_one, Units.val_one,
        Matrix.one_mulVec]⟩
    have hzQ : rootLong k ≤ Y ⊓ QU (ρ4 k) U := by
      rintro _ ⟨t, rfl⟩
      refine ⟨hY ⟨t, rfl⟩, ?_, ?_⟩
      · intro x
        rw [ρ4_long_sub_one_mulVec]
        exact U.smul_mem _ he0
      · intro u hu
        rw [ρ4_long_sub_one_mulVec, hU3 u hu, mul_zero, zero_smul]
    have h1 := inf_QU_le_pCoreOf (ρ := ρ4 k) ρ4_injective hUinv
    exact hzQ.trans h1

end CFSG.Quasithin.E2.TI2b.Sp4
