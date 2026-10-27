module

public import CFSG.Quasithin.Vol2.E2NineTI2bQU
public import CFSG.Quasithin.Vol2.E2NineTI2bL3Corner

public section

namespace CFSG.Quasithin.E2.TI2b.L3

open Matrix CFSG.LocalAnalysis.ComponentInitial.LinearFlag CFSG.Quasithin.Ch3E213M.P5
open CFSG.Open CFSG.QuasithinUnique B6
open scoped MatrixGroups

variable {k : Type} [Field k]

@[expose] def ρ3 (k : Type) [Field k] :
    Matrix.SpecialLinearGroup (Fin 3) k →* Matrix (Fin 3) (Fin 3) k where
  toFun g := (g : Matrix (Fin 3) (Fin 3) k)
  map_one' := rfl
  map_mul' _ _ := rfl

theorem ρ3_injective : Function.Injective (ρ3 k) := fun _ _ h => Subtype.ext h

theorem ρ3_apply (g : Matrix.SpecialLinearGroup (Fin 3) k) :
    ρ3 k g = (g : Matrix (Fin 3) (Fin 3) k) := rfl

theorem uu_zero_zero_sub_one_mulVec (c : k) (x : Fin 3 → k) :
    (ρ3 k (uu 0 0 c) - 1) *ᵥ x = (c * x 2) • (Pi.single 0 1 : Fin 3 → k) := by
  ext i
  fin_cases i <;> simp [ρ3_apply, coe_uu, Matrix.sub_mulVec, Matrix.mulVec, dotProduct,
    Fin.sum_univ_three, Pi.single_apply]

theorem dich_pzz [Finite k] [CharP k 2] (hk : 4 ≤ Nat.card k) {Y : Subgroup (projectiveSL 3 k)}
    (hY : pa1 k ≤ Y) : Dich (pzz k) Y := by
  set π := proj 3 k with hπ
  by_cases h20 : ∃ y : Matrix.SpecialLinearGroup (Fin 3) k, π y ∈ Y ∧
      (y : Matrix (Fin 3) (Fin 3) k) 2 0 ≠ 0
  · obtain ⟨y, hyY, hy20⟩ := h20
    obtain ⟨f, hf, hfY, hzf⟩ := exists_sl2_le_of_orbit hY hyY hy20
    exact dich_of_sl2_range hk hf hfY hzf
  · push Not at h20
    left
    have : Finite (Matrix.SpecialLinearGroup (Fin 3) k) :=
      Finite.of_injective _ (ρ3_injective (k := k))
    set Yt : Subgroup (Matrix.SpecialLinearGroup (Fin 3) k) := Y.comap π with hYt
    have hua1 : ua1 k ≤ Yt := fun g hg => hY ⟨g, hg, rfl⟩
    set U : Submodule k (Fin 3 → k) := Submodule.span k
      {v | ∃ y : Matrix.SpecialLinearGroup (Fin 3) k, π y ∈ Y ∧
        v = (y : Matrix (Fin 3) (Fin 3) k) *ᵥ (Pi.single 0 1 : Fin 3 → k)} with hU
    have hUinv : ∀ y ∈ Yt, ∀ u ∈ U, ρ3 k y *ᵥ u ∈ U := by
      intro y hy
      have hle : U ≤ U.comap (Matrix.mulVecLin (ρ3 k y)) := by
        refine Submodule.span_le.mpr ?_
        rintro _ ⟨z, hz, rfl⟩
        refine Submodule.subset_span ⟨y * z, ?_, ?_⟩
        · rw [map_mul]
          exact Y.mul_mem hy hz
        · rw [Matrix.mulVecLin_apply, Matrix.mulVec_mulVec]
          rfl
      intro u hu
      exact hle hu
    have hU2 : ∀ u ∈ U, u 2 = 0 := by
      intro u hu
      have hle : U ≤ LinearMap.ker (LinearMap.proj (R := k) (φ := fun _ : Fin 3 => k) 2) := by
        refine Submodule.span_le.mpr ?_
        rintro _ ⟨z, hz, rfl⟩
        have := h20 z hz
        simpa [Matrix.mulVec, dotProduct, Fin.sum_univ_three, Pi.single_apply] using this
      simpa using hle hu
    have he0 : (Pi.single 0 1 : Fin 3 → k) ∈ U :=
      Submodule.subset_span ⟨1, by rw [map_one]; exact Y.one_mem,
        by rw [Matrix.SpecialLinearGroup.coe_one, Matrix.one_mulVec]⟩
    have hzzQ : uzz k ≤ Yt ⊓ QU (ρ3 k) U := by
      rintro _ ⟨c, rfl⟩
      refine ⟨hua1 ⟨0, c, rfl⟩, ?_, ?_⟩
      · intro x
        rw [uu_zero_zero_sub_one_mulVec]
        exact U.smul_mem _ he0
      · intro u hu
        rw [uu_zero_zero_sub_one_mulVec, hU2 u hu, mul_zero, zero_smul]
    have h1 := inf_QU_le_pCoreOf (ρ := ρ3 k) ρ3_injective hUinv
    have h2 := map_pCoreOf_comap_le π (proj_surjective 3 k) Y
    calc pzz k = (uzz k).map π := rfl
      _ ≤ (pCoreOf 2 Yt).map π := Subgroup.map_mono (hzzQ.trans h1)
      _ ≤ pCoreOf 2 Y := h2

end CFSG.Quasithin.E2.TI2b.L3
