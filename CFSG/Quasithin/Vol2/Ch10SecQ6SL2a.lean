module

public import CFSG.RankThree.PartOne.KC.EvenSymplecticSL2Automorphisms

public section

namespace CFSG.Quasithin.Vol2.Ch10.SecD

namespace C10P06

open Matrix

variable {K : Type} [Field K]

@[expose] def ut (t : K) : SpecialLinearGroup (Fin 2) K :=
  ⟨!![1, t; 0, 1], by simp [det_fin_two]⟩

theorem coe_ut (t : K) : ((ut t : SpecialLinearGroup (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) =
    !![1, t; 0, 1] := rfl

theorem ut_mul (s t : K) : ut s * ut t = ut (s + t) := by
  apply Matrix.SpecialLinearGroup.ext
  intro i j
  rw [Matrix.SpecialLinearGroup.coe_mul, coe_ut, coe_ut, coe_ut]
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two, add_comm]

theorem ut_zero : ut (0 : K) = 1 := by
  apply Matrix.SpecialLinearGroup.ext
  intro i j
  rw [Matrix.SpecialLinearGroup.coe_one, coe_ut]
  fin_cases i <;> fin_cases j <;> simp

theorem ut_injective : Function.Injective (ut : K → SpecialLinearGroup (Fin 2) K) := by
  intro s t h
  have := congrArg (fun M : SpecialLinearGroup (Fin 2) K => (M : Matrix (Fin 2) (Fin 2) K) 0 1) h
  simpa [ut] using this

variable (K) in
@[expose] def uSub : Subgroup (SpecialLinearGroup (Fin 2) K) where
  carrier := {M | ∃ t, M = ut t}
  one_mem' := ⟨0, ut_zero.symm⟩
  mul_mem' := by
    rintro _ _ ⟨s, rfl⟩ ⟨t, rfl⟩
    exact ⟨s + t, ut_mul s t⟩
  inv_mem' := by
    rintro _ ⟨t, rfl⟩
    refine ⟨-t, ?_⟩
    rw [inv_eq_iff_mul_eq_one, ut_mul, add_neg_cancel, ut_zero]

theorem card_uSub [Finite K] : Nat.card (uSub K) = Nat.card K := by
  refine (Nat.card_eq_of_bijective (fun t => (⟨ut t, t, rfl⟩ : uSub K)) ⟨fun s t h => ?_,
    fun ⟨M, t, hM⟩ => ⟨t, Subtype.ext hM.symm⟩⟩).symm
  exact ut_injective (congrArg Subtype.val h)

theorem slFieldAut_ut (σ : K ≃+* K) (t : K) :
    CFSG.RankThree.PartOne.KCRootAxis.slFieldAut K σ (ut t) = ut (σ t) := by
  apply Matrix.SpecialLinearGroup.ext
  intro i j
  rw [CFSG.RankThree.PartOne.KCRootAxis.slFieldAut_apply, coe_ut, coe_ut]
  fin_cases i <;> fin_cases j <;> simp

theorem conj_ut_entry (M : SpecialLinearGroup (Fin 2) K) (s : K) :
    ((M * ut s * M⁻¹ : SpecialLinearGroup (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) 1 0 =
      -((M : Matrix (Fin 2) (Fin 2) K) 1 0) ^ 2 * s := by
  rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul,
    Matrix.SpecialLinearGroup.coe_inv, adjugate_fin_two, coe_ut]
  simp [Matrix.mul_apply, Fin.sum_univ_two]
  ring

theorem conj_ut_of {M : SpecialLinearGroup (Fin 2) K}
    (hM : (M : Matrix (Fin 2) (Fin 2) K) 1 0 = 0) (s : K) :
    M * ut s * M⁻¹ = ut (((M : Matrix (Fin 2) (Fin 2) K) 0 0) ^ 2 * s) := by
  have hdet := M.2
  rw [det_fin_two, hM, mul_zero, sub_zero] at hdet
  apply Matrix.SpecialLinearGroup.ext
  intro i j
  rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul,
    Matrix.SpecialLinearGroup.coe_inv, adjugate_fin_two, coe_ut, coe_ut]
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two, hM] <;>
    first | ring1 | linear_combination hdet

theorem card_sl2 [Finite K] :
    Nat.card (SpecialLinearGroup (Fin 2) K) = Nat.card K * (Nat.card K ^ 2 - 1) := by
  rw [CFSG.LocalAnalysis.ComponentInitial.LinearFlag.card_SL_eq (n := 2) (by norm_num)]
  norm_num

theorem isPGroup_uSub [Finite K] {n : ℕ} (hK : Nat.card K = 2 ^ n) : IsPGroup 2 (uSub K) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  exact IsPGroup.of_card (n := n) (by rw [card_uSub, hK])

theorem not_two_dvd_index_uSub [Finite K] {n : ℕ} (hK : Nat.card K = 2 ^ n) (hn : 1 ≤ n) :
    ¬ 2 ∣ (uSub K).index := by
  have h := (uSub K).card_mul_index
  rw [card_uSub, card_sl2] at h
  have hidx : (uSub K).index = Nat.card K ^ 2 - 1 := Nat.eq_of_mul_eq_mul_left Nat.card_pos h
  rw [hidx, hK]
  have h2 : 2 ∣ (2 ^ n) ^ 2 := dvd_pow (dvd_pow_self 2 (by omega)) (by norm_num)
  have h1 : 1 ≤ (2 ^ n) ^ 2 := Nat.one_le_pow _ _ (by positivity)
  generalize (2 ^ n) ^ 2 = a at h1 h2 ⊢
  omega

theorem exists_conj_mem_uSub [Finite K] {n : ℕ} (hK : Nat.card K = 2 ^ n) (hn : 1 ≤ n)
    {D : Subgroup (SpecialLinearGroup (Fin 2) K)} (hD : IsPGroup 2 D) :
    ∃ g : SpecialLinearGroup (Fin 2) K, ∀ d ∈ D, g * d * g⁻¹ ∈ uSub K := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨P, hDP⟩ := hD.exists_le_sylow
  let P0 := (isPGroup_uSub hK).toSylow (not_two_dvd_index_uSub hK hn)
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq (SpecialLinearGroup (Fin 2) K) P0 P
  refine ⟨g⁻¹, fun d hd => ?_⟩
  have h1 : d ∈ ((g • P0 : Sylow 2 _) : Subgroup (SpecialLinearGroup (Fin 2) K)) := by
    rw [hg]
    exact hDP hd
  rw [Sylow.coe_subgroup_smul, Subgroup.mem_pointwise_smul_iff_inv_smul_mem] at h1
  have h2 : (MulAut.conj g)⁻¹ • d = g⁻¹ * d * g⁻¹⁻¹ := by
    rw [← map_inv, MulAut.smul_def, MulAut.conj_apply]
  rw [h2] at h1
  exact h1

end C10P06

end CFSG.Quasithin.Vol2.Ch10.SecD
