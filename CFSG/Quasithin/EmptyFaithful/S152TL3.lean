module

public import CFSG.Quasithin.EmptyFaithful.S152TBender
public import CFSG.Quasithin.EmptyFaithful.S146yBorelL3

public section

open CFSG.Open CFSG.QuasithinUnique CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.LinearFlag Matrix

namespace CFSG.Quasithin

section Three

variable {K : Type} [Field K] [Finite K] [CharP K 2]

theorem sq_eq_one_of_commute_projectiveSL_three :
    ∀ x : projectiveSL 3 K, (∀ b ∈ projUpperTriangular 3 K, x * b = b * x) → x * x = 1 := by
  intro x hc
  have hUle : projUnitriangular 3 K ≤ projUpperTriangular 3 K :=
    Subgroup.map_mono (unitriangular_le_upperTriangular 3 K)
  have hxN : x ∈ Subgroup.normalizer (projUnitriangular 3 K : Set (projectiveSL 3 K)) := by
    apply Subgroup.centralizer_le_normalizer
    rw [Subgroup.mem_centralizer_iff]
    intro s hs
    exact (hc s (hUle hs)).symm
  rw [normalizer_projUnitriangular (K := K) (n := 3) 2] at hxN
  obtain ⟨M, hM, rfl⟩ := hxN
  have hMT : ∀ i j : Fin 3, (i : ℕ) + 1 = (j : ℕ) →
      (M : Matrix (Fin 3) (Fin 3) K) * single i j (1 : K) =
        single i j (1 : K) * (M : Matrix (Fin 3) (Fin 3) K) := by
    intro i j hij
    have hlt : i < j := by
      rw [Fin.lt_def]
      omega
    have hT := K1.transvection_mem_unitriangular hlt (1 : K)
    have h1 := hc (proj 3 K (SpecialLinearGroup.transvection hlt.ne (1 : K)))
      (Subgroup.mem_map_of_mem _ (unitriangular_le_upperTriangular 3 K hT))
    have h2 : proj 3 K (M * SpecialLinearGroup.transvection hlt.ne (1 : K) * M⁻¹) =
        proj 3 K (SpecialLinearGroup.transvection hlt.ne (1 : K)) := by
      rw [map_mul, map_mul, map_inv, h1]
      group
    have h3 := proj_injOn_unitriangular 3 (conj_mem_unitriangular hM hT) hT h2
    have h4 : M * SpecialLinearGroup.transvection hlt.ne (1 : K) =
        SpecialLinearGroup.transvection hlt.ne (1 : K) * M := by
      calc M * SpecialLinearGroup.transvection hlt.ne (1 : K)
          = (M * SpecialLinearGroup.transvection hlt.ne (1 : K) * M⁻¹) * M := by group
        _ = SpecialLinearGroup.transvection hlt.ne (1 : K) * M := by rw [h3]
    have h5 := congrArg (fun g : SpecialLinearGroup (Fin 3) K => (g : Matrix (Fin 3) (Fin 3) K)) h4
    simp only [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.transvection_coe,
      mul_add, add_mul, mul_one, one_mul] at h5
    exact add_left_cancel h5
  obtain ⟨a, b, hab⟩ := K1.eq_smul_one_add_single_of_commute (n := 3) (by norm_num)
    (M : Matrix (Fin 3) (Fin 3) K) hMT
  have hE : single (⟨0, by omega⟩ : Fin 3) (⟨3 - 1, by omega⟩ : Fin 3) (1 : K) *
      single (⟨0, by omega⟩ : Fin 3) (⟨3 - 1, by omega⟩ : Fin 3) (1 : K) = 0 :=
    single_mul_single_of_ne _ _ _ _ (K1.fin_mk_ne _ _ (by omega)) _
  have hMM : ((M * M : SpecialLinearGroup (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) =
      (a * a) • (1 : Matrix (Fin 3) (Fin 3) K) := by
    rw [show ((M * M : SpecialLinearGroup (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) =
      (M : Matrix (Fin 3) (Fin 3) K) * (M : Matrix (Fin 3) (Fin 3) K) from
      Matrix.SpecialLinearGroup.coe_mul M M, hab]
    simp only [add_mul, mul_add, smul_mul_assoc, mul_smul_comm, one_mul, mul_one, hE, smul_zero,
      add_zero, smul_smul, smul_add]
    have h2 : (2 : K) = 0 := CharTwo.two_eq_zero
    have : a * b + b * a = 0 := by
      rw [mul_comm b a, ← two_mul, h2, zero_mul]
    rw [add_assoc, ← add_smul, this, zero_smul, add_zero]
  have hdet : ((a * a) • (1 : Matrix (Fin 3) (Fin 3) K)).det = 1 := by
    rw [← hMM]
    exact (M * M).2
  have hdet' : (a * a) ^ 3 = 1 := by
    rw [Matrix.det_smul, Matrix.det_one, mul_one, Fintype.card_fin] at hdet
    exact hdet
  have ha : a * a ≠ 0 := by
    intro h0
    rw [h0] at hdet'
    norm_num at hdet'
  have hmem : (M * M : SpecialLinearGroup (Fin 3) K) ∈ scalars 3 K := by
    refine ⟨Units.mk0 (a * a) ha, ?_, ?_⟩
    · exact Units.ext (by simpa [Units.val_pow_eq_pow_val] using hdet')
    · rw [hMM, Matrix.scalar_apply, Matrix.smul_one_eq_diagonal]
      rfl
  show proj 3 K M * proj 3 K M = 1
  rw [← map_mul]
  exact proj_eq_one_iff.mpr hmem

theorem core_all_projectiveSL_three (hK : 4 ≤ Nat.card K) :
    ∀ x : projectiveSL 3 K, (∀ b ∈ projUpperTriangular 3 K, x * b = b * x) → x = 1 :=
  fun x hc => core_projectiveSL_three hK x (sq_eq_one_of_commute_projectiveSL_three x hc) hc

theorem borelCentralizerTrivial_projectiveSL_three (hK : 4 ≤ Nat.card K) :
    BorelCentralizerTrivial (projectiveSL 3 K) := by
  obtain ⟨S, hS⟩ := exists_sylow_projUnitriangular (K := K) 2 (n := 3) (by norm_num)
  have h0 : IsSylowTwoOf (projUnitriangular 3 K) ⊤ := by
    rw [← hS]
    exact K1.isSylowTwoOf_top_iff.mpr ⟨S.isPGroup', S.not_dvd_index⟩
  refine borelCentralizerTrivial_of_core h0 ?_
  rw [normalizer_projUnitriangular (K := K) (n := 3) 2]
  exact core_all_projectiveSL_three hK

end Three

theorem bctFamL3_proof : BCTFamL3 := by
  intro f hf X _ _ h
  obtain ⟨-, K, _, hKfin, hcard, ⟨e⟩⟩ := h
  have : CharP K 2 := finite_field_prime_power_characteristic Nat.prime_two (by omega) hcard
  let e' : X ≃* projectiveSL 3 K := e.trans (K1.statedProjEquivProjectiveSL 3 K)
  have hK4 : 4 ≤ Nat.card K := by
    rw [hcard]
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ f := Nat.pow_le_pow_right (by norm_num) hf
  exact BorelCentralizerTrivial.of_mulEquiv e'.symm (borelCentralizerTrivial_projectiveSL_three hK4)

end CFSG.Quasithin
