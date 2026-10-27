module

public import CFSG.Quasithin.Vol2.Ch3E213MOLB1

public section

namespace CFSG.Quasithin.Ch3E213M.OLB

open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Disconnected.AschTight.S19K
open scoped MatrixGroups

theorem three_eq_zero_gf3 : (3 : GaloisField 3 1) = 0 := by
  have := CharP.cast_eq_zero (GaloisField 3 1) 3
  exact_mod_cast this

theorem ne_zero_or_ne_zero {M : Matrix (Fin 3) (Fin 3) (GaloisField 3 1)}
    (hne : ¬ (M 0 1 = 0 ∧ M 1 0 = 0 ∧ M 0 0 = M 1 1)) :
    (1 + M) * Matrix.single 0 1 1 * (1 - M) ≠ 0 ∨
      (1 + M) * Matrix.single 1 0 1 * (1 - M) ≠ 0 := by
  by_contra hcon
  push Not at hcon
  obtain ⟨h₁, h₂⟩ := hcon
  have n₁ := fun i j => congrFun (congrFun h₁ i) j
  have n₂ := fun i j => congrFun (congrFun h₂ i) j
  have a := n₁ 1 0
  have b := n₁ 0 1
  have c := n₂ 0 1
  have d := n₂ 1 0
  simp [Matrix.mul_apply, Fin.sum_univ_three, Matrix.single_apply, Matrix.one_apply] at a b c d
  apply hne
  refine ⟨c, a, ?_⟩
  rcases b with hb | hb <;> rcases d with hd | hd
  · linear_combination hb - hd
  · exact absurd (by linear_combination hb + hd) two_ne_zero_gf3
  · exact absurd (by linear_combination hb + hd) two_ne_zero_gf3
  · linear_combination hb - hd

theorem eq_one_or_eq_rootInv {X : Type} [Group X] {K : Subgroup X}
    (ι : SL(3, GaloisField 3 1) ≃* K) {P : Subgroup X} (hP : IsPGroup 2 P)
    (hPz : P ≤ Subgroup.centralizer
      ({(ι (Models.rootInv (GaloisField 3 1) (n := 3) (by norm_num)) : X)} : Set X))
    (hPn : Subgroup.centralizer
      ({(ι (Models.rootInv (GaloisField 3 1) (n := 3) (by norm_num)) : X)} : Set X) ≤
      Subgroup.normalizer (P : Set X))
    {x : SL(3, GaloisField 3 1)} (hxP : (ι x : X) ∈ P) (hx2 : x * x = 1) :
    x = 1 ∨ x = Models.rootInv (GaloisField 3 1) (n := 3) (by norm_num) := by
  set z₀ := Models.rootInv (GaloisField 3 1) (n := 3) (by norm_num) with hz₀
  have hxz : x * z₀ = z₀ * x := by
    have h1 := Subgroup.mem_centralizer_singleton_iff.mp (hPz hxP)
    apply ι.injective
    apply Subtype.ext
    simpa [map_mul] using h1
  obtain ⟨g02, g12, g20, g21⟩ := isBlockDiag_of_commute_rootInv hxz
  set M := ((x : SL(3, GaloisField 3 1)) : Matrix (Fin 3) (Fin 3) (GaloisField 3 1)) with hM
  have hM2 : M * M = 1 := by
    have h1 := congrArg (fun y : SL(3, GaloisField 3 1) =>
      (y : Matrix (Fin 3) (Fin 3) (GaloisField 3 1))) hx2
    simpa using h1
  by_contra hne
  push Not at hne
  have hns : ¬ (M 0 1 = 0 ∧ M 1 0 = 0 ∧ M 0 0 = M 1 1) := by
    rintro ⟨h01, h10, h0011⟩
    have hdet : M 0 0 * M 0 0 * M 2 2 = 1 := by
      have h1 := x.2
      rw [Matrix.det_fin_three, ← hM, h01, h10, g02, g12, g20, g21, ← h0011] at h1
      linear_combination h1
    have hl0 : M 0 0 ≠ 0 := fun h => by
      rw [h] at hdet
      simp at hdet
    have hm : M 2 2 = 1 := by
      rw [sq_eq_one_of_ne_zero hl0, one_mul] at hdet
      exact hdet
    rcases eq_zero_or_one_or_neg_one (M 0 0) with h | h | h
    · exact hl0 h
    · apply hne.1
      apply Subtype.ext
      rw [Matrix.SpecialLinearGroup.coe_one, ← hM]
      ext i j
      fin_cases i <;> fin_cases j <;> simp [h01, h10, g02, g12, g20, g21, ← h0011, h, hm]
    · apply hne.2
      apply Subtype.ext
      rw [coe_rootInv_three, ← hM]
      ext i j
      fin_cases i <;> fin_cases j <;> simp [h01, h10, g02, g12, g20, g21, ← h0011, h, hm]
  have key : ∀ E : Matrix (Fin 3) (Fin 3) (GaloisField 3 1), (∀ j, E 2 j = 0) →
      (∀ i, E i 2 = 0) → (1 + M) * E * (1 - M) ≠ 0 → False := by
    intro E hE₁ hE₂ hN0
    set N := (1 + M) * E * (1 - M) with hNdef
    have hMM : (1 - M) * (1 + M) = 0 := by
      have h1 : (1 - M) * (1 + M) = 1 - M * M := by noncomm_ring
      rw [h1, hM2, sub_self]
    have hNN : N * N = 0 := by
      calc N * N = (1 + M) * E * ((1 - M) * (1 + M)) * E * (1 - M) := by
            simp only [hNdef, Matrix.mul_assoc]
        _ = 0 := by rw [hMM]; simp
    have hMN : M * N = N := by
      have h1 : M * (1 + M) = 1 + M := by rw [mul_add, mul_one, hM2, add_comm]
      rw [hNdef, ← Matrix.mul_assoc, ← Matrix.mul_assoc, h1]
    have hNM : N * M = -N := by
      have h1 : (1 - M) * M = -(1 - M) := by
        rw [sub_mul, one_mul, hM2, neg_sub]
      rw [hNdef, Matrix.mul_assoc, h1, Matrix.mul_neg]
    have h3 : N + N + N = 0 := by
      ext i j
      simp only [Matrix.add_apply, Matrix.zero_apply]
      linear_combination (N i j) * three_eq_zero_gf3
    have h3N : (1 + N) * (1 + N) * (1 + N) = 1 := by
      have h1 : (1 + N) * (1 + N) * (1 + N) =
          1 + (N + N + N) + (N * N + N * N + N * N) + N * N * N := by noncomm_ring
      rw [h1, h3, hNN]
      simp
    have hdet : (1 + N).det = 1 := by
      have h1 := congrArg Matrix.det h3N
      rw [Matrix.det_mul, Matrix.det_mul, Matrix.det_one] at h1
      rcases eq_zero_or_one_or_neg_one (1 + N).det with h | h | h
      · rw [h] at h1
        simp at h1
      · exact h
      · rw [h] at h1
        exact absurd (by linear_combination -h1) two_ne_zero_gf3
    set r : SL(3, GaloisField 3 1) := ⟨1 + N, hdet⟩ with hr
    have hrcoe : ((r : SL(3, GaloisField 3 1)) : Matrix (Fin 3) (Fin 3) (GaloisField 3 1)) =
        1 + N := rfl
    have hr3 : r * r * r = 1 := Subtype.ext (by
      rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul, hrcoe, h3N,
        Matrix.SpecialLinearGroup.coe_one])
    have hr1 : r ≠ 1 := fun h => hN0 (by
      have h1 := congrArg (fun y : SL(3, GaloisField 3 1) =>
        (y : Matrix (Fin 3) (Fin 3) (GaloisField 3 1))) h
      simp only [hrcoe, Matrix.SpecialLinearGroup.coe_one] at h1
      calc N = 1 + N - 1 := by abel
        _ = 0 := by rw [h1, sub_self])
    have hxr : x * r * x * r = 1 := Subtype.ext (by
      simp only [Matrix.SpecialLinearGroup.coe_mul, hrcoe, Matrix.SpecialLinearGroup.coe_one]
      rw [← hM]
      have h1 : M * (1 + N) * M * (1 + N) = (M * M + M * N * M) * (1 + N) := by noncomm_ring
      have h2 : (1 + -N) * (1 + N) = 1 := by
        have h4 : (1 + -N) * (1 + N) = 1 - N * N := by noncomm_ring
        rw [h4, hNN, sub_zero]
      rw [h1, hM2, hMN, hNM, h2])
    have hrow : ∀ j, N 2 j = 0 := by
      intro j
      simp [hNdef, Matrix.mul_apply, Fin.sum_univ_three, Matrix.one_apply, g20, g21, hE₁]
    have hcol : ∀ i, N i 2 = 0 := by
      intro i
      simp [hNdef, Matrix.mul_apply, Fin.sum_univ_three, Matrix.one_apply, g02, g12, hE₂]
    have hrz : r * z₀ = z₀ * r := Subtype.ext (by
      simp only [Matrix.SpecialLinearGroup.coe_mul, hrcoe, hz₀, coe_rootInv_three]
      ext i j
      fin_cases i <;> fin_cases j <;>
        simp [Matrix.mul_apply, Fin.sum_univ_three, Matrix.one_apply, hrow, hcol])
    have hrC : (ι r : X) ∈ Subgroup.centralizer ({(ι z₀ : X)} : Set X) := by
      rw [Subgroup.mem_centralizer_singleton_iff, ← Subgroup.coe_mul, ← Subgroup.coe_mul,
        ← map_mul, ← map_mul, hrz]
    have hxinv : x⁻¹ = x := inv_eq_of_mul_eq_one_right hx2
    have hrinv : r⁻¹ = r * r := inv_eq_of_mul_eq_one_right (by rw [← mul_assoc]; exact hr3)
    have hcomm : x * r * x⁻¹ * r⁻¹ = r := by
      rw [hxinv, hrinv]
      calc x * r * x * (r * r) = (x * r * x * r) * r := by group
        _ = r := by rw [hxr, one_mul]
    have hrP : (ι r : X) ∈ P := by
      have h1 : (ι x : X) * ((ι r : X) * (ι x : X)⁻¹ * (ι r : X)⁻¹) ∈ P :=
        P.mul_mem hxP ((Subgroup.mem_normalizer_iff.mp (hPn hrC) _).mp (P.inv_mem hxP))
      have h2 : (ι x : X) * ((ι r : X) * (ι x : X)⁻¹ * (ι r : X)⁻¹) = (ι r : X) := by
        have h4 := congrArg (fun y : SL(3, GaloisField 3 1) => ((ι y : K) : X)) hcomm
        simp only [map_mul, map_inv, Subgroup.coe_mul, Subgroup.coe_inv] at h4
        calc (ι x : X) * ((ι r : X) * (ι x : X)⁻¹ * (ι r : X)⁻¹) =
            (ι x : X) * (ι r : X) * (ι x : X)⁻¹ * (ι r : X)⁻¹ := by group
          _ = (ι r : X) := h4
      rwa [h2] at h1
    obtain ⟨k, hk⟩ := hP ⟨_, hrP⟩
    have hk' : r ^ 2 ^ k = 1 := by
      apply ι.injective
      apply Subtype.ext
      have h1 := congrArg Subtype.val hk
      simpa using h1
    have hr3' : r ^ 3 = 1 := by rw [pow_succ, pow_two, hr3]
    have hcop : Nat.Coprime 3 (2 ^ k) := Nat.Coprime.pow_right k (by norm_num)
    have h1 := Nat.dvd_gcd (orderOf_dvd_of_pow_eq_one hr3') (orderOf_dvd_of_pow_eq_one hk')
    rw [hcop.gcd_eq_one, Nat.dvd_one, orderOf_eq_one_iff] at h1
    exact hr1 h1
  rcases ne_zero_or_ne_zero hns with h | h
  · exact key _ (fun j => by simp) (fun i => by simp) h
  · exact key _ (fun j => by simp) (fun i => by simp) h

end CFSG.Quasithin.Ch3E213M.OLB
