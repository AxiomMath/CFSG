module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.KNatBorelIrr.Model
public import CFSG.LocalAnalysis.ComponentInitial.UnitaryEvenCoverModel
public import CFSG.LocalAnalysis.ComponentInitial.UnitaryHigherParabolicData
public import CFSG.Quasithin.H13.U4ParCoord

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22.NatBorelIrr

open Matrix CFSG.ClassicalGroups.UnitaryFlag CFSG.LocalAnalysis.ComponentInitial
  CFSG.Quasithin.H13.U4Par
open CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher (flagStabilizer)
open scoped MatrixGroups Pointwise

private lemma transportInv_mulVec_mulVec_L13 {p f : ℕ} {K : Type} [Field K]
    (h : UnitaryFieldData p f K) {r ε : ℕ} {R : Matrix (Fin (2 * r + ε)) (HypIndex r ε) K}
    (hR : IsHypTransport h R) (v : HypIndex r ε → K) :
    transportInv h R *ᵥ (R *ᵥ v) = v := by
  rw [Matrix.mulVec_mulVec, transportInv_mul hR, Matrix.one_mulVec]

theorem hypTransport_mulVec_of_eq {p f : ℕ} {K : Type} [Field K] (h : UnitaryFieldData p f K)
    {r ε : ℕ} {R : Matrix (Fin (2 * r + ε)) (HypIndex r ε) K} (hR : IsHypTransport h R)
    (g : hypSU h r ε) {e₀ : Fin (2 * r + ε) → K} {e₁ : HypIndex r ε → K}
    (he : R *ᵥ e₁ = e₀) :
    (((hypTransport h hR g : unitarySU p f K (2 * r + ε)) : GL (Fin (2 * r + ε)) K) :
      Matrix (Fin (2 * r + ε)) (Fin (2 * r + ε)) K) *ᵥ e₀ =
      R *ᵥ (((g : GL (HypIndex r ε) K) : Matrix (HypIndex r ε) (HypIndex r ε) K) *ᵥ e₁) := by
  rw [coe_hypTransport, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, ← he,
    transportInv_mulVec_mulVec_L13 h hR e₁]

variable {a : ℕ} {K : Type} [Field K] (h : UnitaryFieldData 2 a K)

@[expose] noncomputable def su4AlphaRoot : SL(2, K) →* hypSU h 2 0 :=
  (UnitaryEvenCover.lHom h 2).comp (UnitaryEvenCover.slHom h 2)

theorem coe_su4AlphaRoot (B : SL(2, K)) :
    (((su4AlphaRoot h B : hypSU h 2 0) : GL (HypIndex 2 0) K) :
      Matrix (HypIndex 2 0) (HypIndex 2 0) K) = evenMat h (B : Matrix (Fin 2) (Fin 2) K) 0 := by
  rfl

theorem su4AlphaRoot_mulVec_mem_posFlag (B : SL(2, K)) {v : HypIndex 2 0 → K}
    (hv : v ∈ posFlag 2 0 K 2) :
    (((su4AlphaRoot h B : hypSU h 2 0) : GL (HypIndex 2 0) K) :
      Matrix (HypIndex 2 0) (HypIndex 2 0) K) *ᵥ v ∈ posFlag 2 0 K 2 := by
  rw [coe_su4AlphaRoot]
  refine mem_posFlag.mpr fun x hx => ?_
  rcases x with i | k | i
  · rw [fullPos_inl] at hx
    omega
  · exact k.elim0
  · simp only [Matrix.mulVec, dotProduct]
    refine Finset.sum_eq_zero fun c _ => ?_
    rcases c with j | l | j
    · simp [evenMat]
    · exact l.elim0
    · rw [mem_posFlag.mp hv (Sum.inr (Sum.inr j)) (by simp only [fullPos_inr_inr]; omega)]
      simp

theorem su4AlphaRoot_range_le_flagStabilizer :
    (su4AlphaRoot h).range ≤ flagStabilizer h 2 0 {2} := by
  rintro _ ⟨B, rfl⟩
  rw [CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher.mem_flagStabilizer]
  intro i hi
  rw [Set.mem_singleton_iff] at hi
  subst hi
  rw [hypFlag_eq_posFlag h (by norm_num) (by norm_num), Subgroup.smul_def]
  refine smul_eq_of_mulVec_mem (fun v hv => su4AlphaRoot_mulVec_mem_posFlag h B hv)
    fun v hv => ?_
  rw [← Subgroup.coe_inv, ← map_inv]
  exact su4AlphaRoot_mulVec_mem_posFlag h B⁻¹ hv

theorem su4AlphaRoot_torusSL_mem_hypBorel (c : Kˣ) :
    su4AlphaRoot h (torusSL c) ∈ hypBorel h 2 0 := by
  obtain ⟨g, hg, hgm⟩ := exists_mem_hypBorel_evenMat (h := h)
    (A := ((torusSL c : SL(2, K)) : Matrix (Fin 2) (Fin 2) K)) (C := 0)
    (by intro i j hij; fin_cases i <;> fin_cases j <;> simp_all [torusSL])
    (by rw [Matrix.SpecialLinearGroup.det_coe]; exact isUnit_one)
    (by simp) (by rw [Matrix.SpecialLinearGroup.det_coe, map_one, div_one])
  have hg' : g = su4AlphaRoot h (torusSL c) :=
    hypSU_ext h (hgm.trans (coe_su4AlphaRoot h (torusSL c)).symm)
  rw [← hg']
  exact hg

theorem su4AlphaRoot_torusSL_mulVec (c : Kˣ) :
    (((su4AlphaRoot h (torusSL c) : hypSU h 2 0) : GL (HypIndex 2 0) K) :
      Matrix (HypIndex 2 0) (HypIndex 2 0) K) *ᵥ (Pi.single ie1 1 : HypIndex 2 0 → K) =
      (c : K) • (Pi.single ie1 1 : HypIndex 2 0 → K) := by
  rw [coe_su4AlphaRoot]
  funext x
  rw [Matrix.mulVec_single_one, Matrix.col_apply, Pi.smul_apply]
  rcases ix_cases x with rfl | rfl | rfl | rfl <;>
    simp [evenMat, torusSL, ie1, ie2, if1, if2, Pi.single_apply, smul_eq_mul]

end CFSG.LocalAnalysis.UniquenessCase.UC22.NatBorelIrr
