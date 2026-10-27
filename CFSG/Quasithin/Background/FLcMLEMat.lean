module

public import CFSG.Quasithin.Background.FLcR2El
public import CFSG.Quasithin.Background.FLcP0Mat

public section

namespace CFSG.Quasithin.FLc

open Matrix Module CFSG.LocalAnalysis.ComponentInitial.LinearFlag

@[expose] def V1 (n : ℕ) : Subgroup (SLt n) where
  carrier := {g | g ∈ stabilizer (flagSpace n (ZMod 2) 1) ∧
    (∀ v ∈ flagSpace n (ZMod 2) 1, mat g *ᵥ v = v) ∧
    ∀ v : Vt n, mat g *ᵥ v - v ∈ flagSpace n (ZMod 2) 1}
  one_mem' := by
    refine ⟨(stabilizer (flagSpace n (ZMod 2) 1)).one_mem, fun v _ => ?_, fun v => ?_⟩
    · rw [mat_one, one_mulVec]
    · rw [mat_one, one_mulVec, sub_self]
      exact (flagSpace n (ZMod 2) 1).zero_mem
  mul_mem' := by
    rintro g h ⟨hgs, hg1, hg2⟩ ⟨hhs, hh1, hh2⟩
    refine ⟨(stabilizer (flagSpace n (ZMod 2) 1)).mul_mem hgs hhs, fun v hv => ?_, fun v => ?_⟩
    · rw [mat_mul, ← mulVec_mulVec, hh1 v hv, hg1 v hv]
    · have e : mat g *ᵥ (mat h *ᵥ v) - v =
          (mat g *ᵥ (mat h *ᵥ v) - mat h *ᵥ v) + (mat h *ᵥ v - v) := by abel
      rw [mat_mul, ← mulVec_mulVec, e]
      exact (flagSpace n (ZMod 2) 1).add_mem (hg2 _) (hh2 v)
  inv_mem' := by
    rintro g ⟨hgs, hg1, hg2⟩
    have hgg : ∀ w : Vt n, mat g *ᵥ (mat g⁻¹ *ᵥ w) = w := fun w => by
      rw [mulVec_mulVec, mat_mul_inv, one_mulVec]
    refine ⟨(stabilizer (flagSpace n (ZMod 2) 1)).inv_mem hgs, fun v hv => ?_, fun v => ?_⟩
    · have h1 := hg1 v hv
      have h2 := congrArg (fun w => mat g⁻¹ *ᵥ w) h1
      simp only [mulVec_mulVec] at h2
      have e : mat g⁻¹ * mat g = 1 := by rw [← mat_mul, inv_mul_cancel, mat_one]
      rw [e, one_mulVec] at h2
      exact h2.symm
    · have h1 := hg2 (mat g⁻¹ *ᵥ v)
      rw [hgg] at h1
      have h3 := (flagSpace n (ZMod 2) 1).neg_mem h1
      have e : mat g⁻¹ *ᵥ v - v = -(v - mat g⁻¹ *ᵥ v) := by abel
      rw [e]
      exact h3

theorem V1_le_Ut {n : ℕ} : V1 n ≤ Ut n := by
  rintro g ⟨hgs, hg1, hg2⟩
  refine mem_Ut_of_stab_all fun j hj1 hjn => ?_
  refine mem_stabilizer_of_forall fun v hv => ?_
  have h1 : mat g *ᵥ v = (mat g *ᵥ v - v) + v := by abel
  rw [h1]
  exact (flagSpace n (ZMod 2) j).add_mem (flagSpace_mono hj1 (hg2 v)) hv

theorem stab1_conj_mem_V1 {n : ℕ} {q g : SLt n} (hq : q ∈ stabilizer (flagSpace n (ZMod 2) 1))
    (hg : g ∈ V1 n) : q * g * q⁻¹ ∈ V1 n := by
  obtain ⟨hgs, hg1, hg2⟩ := hg
  have hqi : q⁻¹ ∈ stabilizer (flagSpace n (ZMod 2) 1) := (stabilizer _).inv_mem hq
  have hqq : ∀ w : Vt n, mat q *ᵥ (mat q⁻¹ *ᵥ w) = w := fun w => by
    rw [mulVec_mulVec, mat_mul_inv, one_mulVec]
  refine ⟨(stabilizer (flagSpace n (ZMod 2) 1)).mul_mem ((stabilizer _).mul_mem hq hgs) hqi,
    fun v hv => ?_, fun v => ?_⟩
  · have hv' : mat q⁻¹ *ᵥ v ∈ flagSpace n (ZMod 2) 1 := ((mem_stabilizer_iff.1 hqi v).1 hv)
    rw [mat_mul, mat_mul, ← mulVec_mulVec, ← mulVec_mulVec, hg1 _ hv', hqq]
  · have e : mat q *ᵥ (mat g *ᵥ (mat q⁻¹ *ᵥ v)) - v =
        mat q *ᵥ (mat g *ᵥ (mat q⁻¹ *ᵥ v) - mat q⁻¹ *ᵥ v) := by
      rw [mulVec_sub, hqq]
    rw [mat_mul, mat_mul, ← mulVec_mulVec, ← mulVec_mulVec, e]
    exact (mem_stabilizer_iff.1 hq _).1 (hg2 _)

theorem mle_compute {n : ℕ} (hn : n = 4 ∨ n = 5) (h3 : 3 ≤ n) :
    R1 n h3 * E02 n h3 * R1 n h3 = E12 n h3 ∧ R1 n h3 * R1 n h3 = 1 ∧
    (∀ v : Vt n, (∀ j : Fin n, 1 ≤ j.val → v j = 0) → mat (E02 n h3) *ᵥ v = v) ∧
    (∀ v : Vt n, ∀ j : Fin n, 1 ≤ j.val → (mat (E02 n h3) *ᵥ v - v) j = 0) ∧
    ¬ (∀ v : Vt n, ∀ j : Fin n, 1 ≤ j.val → (mat (E12 n h3) *ᵥ v - v) j = 0) := by
  rcases hn with rfl | rfl <;> decide +revert

theorem E02_mem_V1 {n : ℕ} (hn : n = 4 ∨ n = 5) (h3 : 3 ≤ n) : E02 n h3 ∈ V1 n := by
  obtain ⟨-, -, h1, h2, -⟩ := mle_compute hn h3
  refine ⟨mem_flagStabilizer.1 (Ut_le_QI n {1} (tv_mem_Ut _)) 1 rfl, fun v hv => ?_,
    fun v => ?_⟩
  · rw [mem_flagSpace] at hv
    exact h1 v hv
  · rw [mem_flagSpace]
    exact h2 v

theorem E12_notMem_V1 {n : ℕ} (hn : n = 4 ∨ n = 5) (h3 : 3 ≤ n) : E12 n h3 ∉ V1 n := by
  obtain ⟨-, -, -, -, h⟩ := mle_compute hn h3
  rintro ⟨-, -, h2⟩
  apply h
  intro v j hj
  exact mem_flagSpace.1 (h2 v) j hj

theorem no_swap_of_fixes {n : ℕ} (hn : n = 4 ∨ n = 5) (φ : SLt n ≃* SLt n)
    (hfix : ∀ u ∈ Ut n, φ u = u)
    (hswap : ∀ d, 1 ≤ d → d < n → (stabilizer (flagSpace n (ZMod 2) d)).map φ.toMonoidHom =
      stabilizer (flagSpace n (ZMod 2) (n - d))) : False := by
  have h3 : 3 ≤ n := by omega
  obtain ⟨hc1, hc2, -⟩ := mle_compute hn h3
  have hr : R1 n h3 ∈ stabilizer (flagSpace n (ZMod 2) (n - 1)) :=
    reflection_mem_stab (n := n) (j := n - 1) (by omega) (by omega)
  rw [← hswap 1 le_rfl (by omega)] at hr
  obtain ⟨q, hq, hqr⟩ := hr
  have hconj := stab1_conj_mem_V1 hq (E02_mem_V1 hn h3)
  have hU : q * E02 n h3 * q⁻¹ ∈ Ut n := V1_le_Ut hconj
  have h1 := hfix _ hU
  have hqr' : φ q = R1 n h3 := hqr
  have hE : φ (E02 n h3) = E02 n h3 := hfix _ (tv_mem_Ut _)
  rw [map_mul, map_mul, map_inv, hqr', hE] at h1
  have hRinv : (R1 n h3)⁻¹ = R1 n h3 := inv_eq_of_mul_eq_one_right hc2
  rw [hRinv, hc1] at h1
  rw [← h1] at hconj
  exact E12_notMem_V1 hn h3 hconj

theorem E01_ne_one {n : ℕ} (hn : n = 4 ∨ n = 5) (h3 : 3 ≤ n) : E01 n h3 ≠ 1 := by
  rcases hn with rfl | rfl <;> decide +revert

end CFSG.Quasithin.FLc
