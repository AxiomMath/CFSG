module

public import CFSG.Quasithin.Vol2.Ch5Sec1L34ModelL34

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique CFSG.Quasithin
open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.LinearFlag
open Matrix

theorem exists_ne_comm_unitriangular (k : Type*) [Field k] :
    ∃ A ∈ unitriangular 3 k, ∃ B ∈ unitriangular 3 k, A * B ≠ B * A := by
  refine ⟨SpecialLinearGroup.transvection (show (0 : Fin 3) ≠ 1 by decide) 1, ⟨?_, ?_⟩,
    SpecialLinearGroup.transvection (show (1 : Fin 3) ≠ 2 by decide) 1, ⟨?_, ?_⟩, fun h => ?_⟩
  · intro i j hij
    fin_cases i <;> fin_cases j <;>
      simp_all [SpecialLinearGroup.transvection_coe]
  · intro i
    fin_cases i <;> simp [SpecialLinearGroup.transvection_coe]
  · intro i j hij
    fin_cases i <;> fin_cases j <;>
      simp_all [SpecialLinearGroup.transvection_coe]
  · intro i
    fin_cases i <;> simp [SpecialLinearGroup.transvection_coe]
  · have h02 := congrFun (congrFun (congrArg
      (fun g : SpecialLinearGroup (Fin 3) k => (g : Matrix (Fin 3) (Fin 3) k)) h) 0) 2
    simp [SpecialLinearGroup.transvection_coe, Matrix.mul_apply, Fin.sum_univ_three,
      Matrix.single_apply] at h02

theorem not_isMulCommutative_of_isSylowTwoOf {X : Type} [Group X] [Finite X]
    (hX : LieModel X .PSL 3 2 2) {S : Subgroup X} (hS : IsSylowTwoOf S ⊤) :
    ¬ IsMulCommutative S := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  intro hcomm
  obtain ⟨k, _, _, hk, ⟨e⟩⟩ := exists_mulEquiv_projectiveSL_of_lieModel hX
  have : CharP k 2 :=
    CFSG.ProperTwoGeneratedCore.LocalCriterionSquareField.char_two_of_card (n := 2)
      (by rw [hk]; norm_num)
  set P := projectiveSL 3 k
  have hS2 : IsPGroup 2 (S.map e.toMonoidHom) := hS.2.1.map _
  have hSi : ¬ 2 ∣ (S.map e.toMonoidHom).index := by
    rw [Subgroup.index_map_of_bijective e.bijective]
    have := hS.2.2
    change ¬ 2 ∣ S.relIndex ⊤ at this
    rwa [Subgroup.relIndex_top_right] at this
  let PS : Sylow 2 P := hS2.toSylow hSi
  obtain ⟨PU, hPU⟩ := exists_sylow_projUnitriangular (K := k) 2 (n := 3) (by norm_num)
  obtain ⟨x, hx⟩ := MulAction.exists_smul_eq P PU PS
  have hPS : (S.map e.toMonoidHom : Subgroup P) =
      (projUnitriangular 3 k).map (MulAut.conj x : P →* P) := by
    have h1 : (S.map e.toMonoidHom : Subgroup P) = (PS : Subgroup P) := rfl
    rw [h1, ← hx, coe_sylow_smul, hPU]
  have hmem : ∀ A ∈ unitriangular 3 k, ∃ s ∈ S, e s = x * proj 3 k A * x⁻¹ := by
    intro A hA
    have h1 : x * proj 3 k A * x⁻¹ ∈ (S.map e.toMonoidHom : Subgroup P) := by
      rw [hPS]
      exact ⟨proj 3 k A, ⟨A, hA, rfl⟩, by simp [MulAut.conj_apply]⟩
    obtain ⟨s, hs, hse⟩ := h1
    exact ⟨s, hs, hse⟩
  obtain ⟨A, hA, B, hB, hAB⟩ := exists_ne_comm_unitriangular k
  obtain ⟨a, ha, hae⟩ := hmem A hA
  obtain ⟨b, hb, hbe⟩ := hmem B hB
  have hab : a * b = b * a := congrArg Subtype.val (hcomm.is_comm.comm ⟨a, ha⟩ ⟨b, hb⟩)
  have h1 : proj 3 k (A * B) = proj 3 k (B * A) := by
    have h2 := congrArg e hab
    rw [map_mul, map_mul, hae, hbe] at h2
    have h3 : x * (proj 3 k A * proj 3 k B) * x⁻¹ = x * (proj 3 k B * proj 3 k A) * x⁻¹ := by
      calc x * (proj 3 k A * proj 3 k B) * x⁻¹ =
            x * proj 3 k A * x⁻¹ * (x * proj 3 k B * x⁻¹) := by group
        _ = x * proj 3 k B * x⁻¹ * (x * proj 3 k A * x⁻¹) := h2
        _ = x * (proj 3 k B * proj 3 k A) * x⁻¹ := by group
    rw [map_mul, map_mul]
    simpa using h3
  exact hAB (proj_injOn_unitriangular 3 ((unitriangular 3 k).mul_mem hA hB)
    ((unitriangular 3 k).mul_mem hB hA) h1)

end CFSG.Quasithin.H13
