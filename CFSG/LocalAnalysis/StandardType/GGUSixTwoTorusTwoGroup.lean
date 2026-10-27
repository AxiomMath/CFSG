module

public import CFSG.LocalAnalysis.StandardType.GGUSixTwoTorus
import CFSG.LocalAnalysis.StandardType.GGTableBUnitaryEndNodeRestOuter
import CFSG.LocalAnalysis.StandardType.GGUSixTwoTransvection

public section

namespace CFSG.StandardType.USixTwo

open CFSG.Assembly
open CFSG.SectionRank.OddCover (diagHom coe_diagHom)

variable {K : Type} [Field K] [Finite K]

private noncomputable def diagVecUnit {ω : K} (hω : ω ^ 2 + ω + 1 = 0) {i j : Fin 6}
    (hij : i ≠ j) : Fin 6 → Kˣ :=
  fun k => Units.mk0 (diagVec (K := K) ω i j k) (by
    have h3 := diagVec_cube (K := K) hω hij k
    intro hk
    rw [hk, zero_pow (by norm_num : 3 ≠ 0)] at h3
    exact zero_ne_one h3)

private theorem prod_diagVecUnit {ω : K} (hω : ω ^ 2 + ω + 1 = 0) {i j : Fin 6}
    (hij : i ≠ j) : ∏ k, diagVecUnit (K := K) hω hij k = 1 := by
  apply Units.ext
  simp only [Units.val_one]
  rw [Units.coe_prod]
  simpa [diagVecUnit] using diagVec_prod (K := K) hω hij

private theorem diagGL_diagVecUnit {ω : K} (hω : ω ^ 2 + ω + 1 = 0) {i j : Fin 6}
    (hij : i ≠ j) :
    TauCeti.diagGL (diagVecUnit (K := K) hω hij) = diagHom 6 (diagVecUnit hω hij) := by
  apply Units.ext
  rw [TauCeti.diagGL_coe, coe_diagHom]

private theorem diagVecUnit_ne (hK : Nat.card K = 4) {ω : K} (hω : ω ^ 2 + ω + 1 = 0)
    {i j : Fin 6} (hij : i ≠ j) : diagVecUnit (K := K) hω hij i ≠
      diagVecUnit (K := K) hω hij j := by
  intro h
  have hv : ω = ω ^ 2 := by
    have := congrArg (fun u : Kˣ => (u : K)) h
    simpa [diagVecUnit, diagVec_self hij, diagVec_other hij] using this
  exact omega_sq_ne_omega hK hω hv.symm

theorem eq_bot_of_isPGroup_two_of_torU_le_normalizer (hK : Nat.card K = 4)
    {V : Subgroup (LargeEvenProj (LargeEvenSUGroup (Fin 6) K (2 ^ 1)))} (hV : IsPGroup 2 V)
    (hTV : torU K ≤
      Subgroup.normalizer (V : Set (LargeEvenProj (LargeEvenSUGroup (Fin 6) K (2 ^ 1))))) :
    V = ⊥ := by
  have hdist : ∀ i j : Fin 6, i ≠ j → ∃ x ∈ torSU K, ∃ σ : Fin 6 → Kˣ,
      (x : GL (Fin 6) K) = diagHom 6 σ ∧ σ i ≠ σ j := by
    intro i j hij
    obtain ⟨ω, hω⟩ := exists_root_omega hK
    have hprod := prod_diagVecUnit (K := K) hω hij
    refine ⟨⟨TauCeti.diagGL (diagVecUnit hω hij),
        diagGL_mem_SU_of_prod_eq_one hK hprod⟩,
      diagGL_mem_torSU_of_prod_eq_one hK hprod, diagVecUnit hω hij, ?_,
      diagVecUnit_ne hK hω hij⟩
    exact diagGL_diagVecUnit hω hij
  exact CFSG.StandardType.TableBUR.eq_bot_of_normalizes_twoSubgroup
    (h := fieldDataFour hK) (n := 1) (d := 6) (A := torSU K) hdist hV hTV

end CFSG.StandardType.USixTwo
