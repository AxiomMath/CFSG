module

public import CFSG.Quasithin.EmptyFaithful.S152TBender
public import CFSG.Quasithin.EmptyFaithful.S146yBorelSp

public section

open CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag CFSG.LocalAnalysis.ComponentInitial.SymplecticFour Matrix

namespace CFSG.Quasithin

section Four

variable {K : Type} [Field K] [Finite K] [CharP K 2]

omit [Finite K] in
theorem sq_eq_one_of_commute_statedSp_two :
    ∀ x : StatedSp 2 K, (∀ b ∈ borelSubgroup 2 K, x * b = b * x) → x * x = 1 := by
  intro x hc
  have hxN : x ∈ Subgroup.normalizer (unipotent 2 K : Set (StatedSp 2 K)) := by
    apply Subgroup.centralizer_le_normalizer
    rw [Subgroup.mem_centralizer_iff]
    intro s hs
    exact (hc s (unipotent_le_borelSubgroup hs)).symm
  rw [SymplecticHigher.normalizer_unipotent (r := 2) (K := K)] at hxN
  obtain ⟨A, C, hA, hdet, hC, hx⟩ := mem_borelSubgroup_iff.mp hxN
  have key : ∀ C' : Matrix (Fin 2) (Fin 2) K, C'ᵀ = C' → A⁻¹ * C' * A⁻¹ᵀ = C' := by
    intro C' hC'
    obtain ⟨g, hg, hgc⟩ := exists_mem_unipotent (K := K) (r := 2) isUnitriangular_one hC'
    have h1 := hc g (unipotent_le_borelSubgroup hg)
    have h2 := congrArg (fun y : StatedSp 2 K =>
      ((y : GL (Fin 2 ⊕ Fin 2) K) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K)) h1
    simp only [Subgroup.coe_mul, Units.val_mul, hx, hgc] at h2
    have hd1 : IsUnit ((1 : Matrix (Fin 2) (Fin 2) K).det) := by simp
    rw [blockMat_mul hd1, blockMat_mul hdet] at h2
    obtain ⟨-, h3⟩ := blockMat_inj (by simpa using hdet) h2
    simp only [inv_one, transpose_one, Matrix.one_mul, Matrix.mul_one] at h3
    have h4 : C' + C = C + A⁻¹ * C' * A⁻¹ᵀ := h3
    rw [add_comm C' C] at h4
    exact (add_left_cancel h4).symm
  have h2 : (2 : K) = 0 := CharTwo.two_eq_zero
  have hone : ∀ b : K, b * b = 1 → b = 1 := fun b hb => by
    have : (b - 1) ^ 2 = 0 := by linear_combination hb + (1 - b) * h2
    exact sub_eq_zero.mp (pow_eq_zero_iff (two_ne_zero)|>.mp this)
  set B : Matrix (Fin 2) (Fin 2) K := A⁻¹ with hB
  have hBup : B.IsUpperTriangular := isUpperTriangular_inv hA hdet
  have hB10 : B 1 0 = 0 := hBup (show (0 : Fin 2) < 1 by decide)
  have hsym0 : (!![1, 0; 0, 0] : Matrix (Fin 2) (Fin 2) K)ᵀ = !![1, 0; 0, 0] := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp
  have hsym1 : (!![0, 0; 0, 1] : Matrix (Fin 2) (Fin 2) K)ᵀ = !![0, 0; 0, 1] := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp
  have e0 := congrFun₂ (key _ hsym0) 0 0
  have e1 := congrFun₂ (key _ hsym1) 0 0
  have e2 := congrFun₂ (key _ hsym1) 1 1
  simp [Matrix.mul_apply, Fin.sum_univ_two] at e0 e1 e2
  have hB00 : B 0 0 = 1 := hone _ e0
  have hB01 : B 0 1 = 0 := by simpa using e1
  have hB11 : B 1 1 = 1 := hone _ e2
  have hBone : B = 1 := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [hB00, hB01, hB10, hB11]
  have hA1 : A = 1 := by
    have := Matrix.mul_nonsing_inv A hdet
    rw [← hB, hBone, Matrix.mul_one] at this
    exact this
  subst hA1
  have hd1 : IsUnit ((1 : Matrix (Fin 2) (Fin 2) K).det) := by simp
  apply Subtype.ext
  apply Units.ext
  simp only [Subgroup.coe_mul, Units.val_mul, hx, Subgroup.coe_one, Units.val_one]
  rw [blockMat_mul hd1]
  simp only [inv_one, transpose_one, Matrix.one_mul, Matrix.mul_one]
  rw [CharTwo.add_self_eq_zero, ← blockMat_one]

theorem core_all_statedSp_two (hK : 4 ≤ Nat.card K) :
    ∀ x : StatedSp 2 K, (∀ b ∈ borelSubgroup 2 K, x * b = b * x) → x = 1 :=
  fun x hc => core_statedSp_two hK x (sq_eq_one_of_commute_statedSp_two x hc) hc

theorem borelCentralizerTrivial_statedSp_two (hK : 4 ≤ Nat.card K) :
    BorelCentralizerTrivial (StatedSp 2 K) := by
  obtain ⟨-, ⟨S, hS⟩, -, -, -, -, -, -, -⟩ :=
    unique_symplectic_four_Sylow_center (K := K) (Nat.card K) rfl
  have h0 : IsSylowTwoOf (unipotent 2 K) ⊤ := by
    rw [← hS]
    exact K1.isSylowTwoOf_top_iff.mpr ⟨S.isPGroup', S.not_dvd_index⟩
  refine borelCentralizerTrivial_of_core h0 ?_
  rw [SymplecticHigher.normalizer_unipotent (r := 2) (K := K)]
  exact core_all_statedSp_two hK

end Four

theorem bctFamSp4_proof : BCTFamSp4 := by
  intro f hf X _ _ h
  obtain ⟨-, K, _, hKfin, hcard, ⟨e⟩⟩ := h
  have : CharP K 2 := finite_field_prime_power_characteristic Nat.prime_two (by omega) hcard
  let e' : X ≃* StatedSp 2 K := e.trans statedSpEquivProj.symm
  have hK4 : 4 ≤ Nat.card K := by
    rw [hcard]
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ f := Nat.pow_le_pow_right (by norm_num) hf
  exact BorelCentralizerTrivial.of_mulEquiv e'.symm (borelCentralizerTrivial_statedSp_two hK4)

end CFSG.Quasithin
