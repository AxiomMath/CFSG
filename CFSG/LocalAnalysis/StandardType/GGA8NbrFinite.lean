module

public import CFSG.LocalAnalysis.StandardType.GGA8NbrCoordDefs
public import CFSG.LocalAnalysis.StandardType.GGA8NbrInfData

public section

namespace CFSG.StandardType.A8Coord

open Certificates.A8Nbr476 CFSG.StandardType.A8NbrInf Matrix

private lemma a8fin_two_pow_zmod3_add :
    ∀ x y : ZMod 3,
      (2 : ZMod 7) ^ x.val * (2 : ZMod 7) ^ y.val = (2 : ZMod 7) ^ ((x + y).val) := by
  decide +kernel

private lemma a8fin_blk_mul (A B : M3) : blk A * blk B = blk (A * B) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [blk, Matrix.mul_apply, Fin.sum_univ_four, Fin.sum_univ_three]

private lemma a8fin_blk_one : blk (1 : M3) = 1 := by
  decide +kernel

private lemma a8fin_monK3_mul (π₁ π₂ : Equiv.Perm (Fin 3)) (k₁ k₂ : Fin 3 → ZMod 3) :
    a8MonK3 π₁ k₁ * a8MonK3 π₂ k₂ =
      a8MonK3 (π₁.trans π₂) (fun i => k₁ i + k₂ (π₁ i)) := by
  ext i j
  rw [Matrix.mul_apply, Finset.sum_eq_single (π₁ i)]
  · by_cases h : π₂ (π₁ i) = j
    · simp [a8MonK3, Equiv.trans_apply, h, a8fin_two_pow_zmod3_add]
    · simp [a8MonK3, Equiv.trans_apply, h]
  · intro t _ hne
    have h1 : ¬ (π₁ i = t) := fun hh => hne hh.symm
    simp [a8MonK3, h1]
  · intro hnot
    exact (hnot (Finset.mem_univ _)).elim

private lemma a8fin_monK3_one : a8MonK3 (1 : Equiv.Perm (Fin 3)) 0 = 1 := by
  decide +kernel

private lemma a8fin_monK_inv_formula (π : Equiv.Perm (Fin 3)) (k : Fin 3 → ZMod 3) :
    a8MonK π k * a8MonK π.symm (fun j => -(k (π.symm j))) = 1 := by
  have h : a8MonK3 π k * a8MonK3 π.symm (fun j => -(k (π.symm j))) = 1 := by
    rw [a8fin_monK3_mul]
    rw [show π.trans π.symm = 1 from by ext i; simp,
        show (fun i => k i + (fun j => -(k (π.symm j))) (π i)) = 0 from by
          funext i; simp]
    exact a8fin_monK3_one
  simp only [a8MonK]
  rw [a8fin_blk_mul, h, a8fin_blk_one]

theorem a8MonK_mul (π₁ π₂ : Equiv.Perm (Fin 3)) (k₁ k₂ : Fin 3 → ZMod 3) :
    ∃ (π : Equiv.Perm (Fin 3)) (k : Fin 3 → ZMod 3),
      a8MonK π₁ k₁ * a8MonK π₂ k₂ = a8MonK π k := by
  refine ⟨π₁.trans π₂, fun i => k₁ i + k₂ (π₁ i), ?_⟩
  simp only [a8MonK]
  rw [a8fin_blk_mul, a8fin_monK3_mul]

theorem a8MonK_inv (π : Equiv.Perm (Fin 3)) (k : Fin 3 → ZMod 3) :
    ∃ (π' : Equiv.Perm (Fin 3)) (k' : Fin 3 → ZMod 3), a8MonK π k * a8MonK π' k' = 1 := by
  exact ⟨π.symm, fun j => -(k (π.symm j)), a8fin_monK_inv_formula π k⟩

private lemma a8fin_vecMul_blk_zero_cons {v : Fin 4 → ZMod 7} (M : M3)
    (h : vecMul v (blk M) = v) :
    vecMul ![0, v 1, v 2, v 3] (blk M) = ![0, v 1, v 2, v 3] := by
  ext i
  fin_cases i
  · rw [Matrix.vecMul_apply_eq_sum]
    apply Finset.sum_eq_zero
    intro j _
    fin_cases j <;> simp [blk]
  · have h1 := congrFun h 1
    rw [Matrix.vecMul_apply_eq_sum, Fin.sum_univ_four] at h1
    rw [Matrix.vecMul_apply_eq_sum, Fin.sum_univ_four]
    simpa (config := { decide := true }) [blk] using h1
  · have h2 := congrFun h 2
    rw [Matrix.vecMul_apply_eq_sum, Fin.sum_univ_four] at h2
    rw [Matrix.vecMul_apply_eq_sum, Fin.sum_univ_four]
    simpa (config := { decide := true }) [blk] using h2
  · have h3 := congrFun h 3
    rw [Matrix.vecMul_apply_eq_sum, Fin.sum_univ_four] at h3
    rw [Matrix.vecMul_apply_eq_sum, Fin.sum_univ_four]
    simpa (config := { decide := true }) [blk] using h3

private instance a8fin_standardizeQdec (π₁ π₂ : Equiv.Perm (Fin 3)) (k₁ k₂ : Fin 3 → ZMod 3) :
    Decidable (∀ u : ZMod 7 × ZMod 7 × ZMod 7,
      (u.1 ≠ 0 ∧ u.2.1 ≠ 0 ∧ u.2.2 ≠ 0 ∧
       vecMul ![0, u.1, u.2.1, u.2.2] (a8MonK π₁ k₁) = ![0, u.1, u.2.1, u.2.2] ∧
       vecMul ![0, u.1, u.2.1, u.2.2] (a8MonK π₂ k₂) = ![0, u.1, u.2.1, u.2.2]) →
      ∃ (π : Equiv.Perm (Fin 3)) (k : Fin 3 → ZMod 3),
        a8MonK π k * a8MonK π₁ k₁ * a8MonK π.symm (fun j => -(k (π.symm j))) = genK 0 ∧
        a8MonK π k * a8MonK π₂ k₂ * a8MonK π.symm (fun j => -(k (π.symm j))) = genK 1) :=
  Fintype.decidableForallFintype

private lemma a8fin_inv_mul_cancel : ∀ x : ZMod 7, x ≠ 0 → x⁻¹ * x = 1 := by
  decide +kernel

private lemma a8fin_inv_mul_ne_zero : ∀ x y : ZMod 7, x ≠ 0 → y ≠ 0 → x⁻¹ * y ≠ 0 := by
  decide +kernel

private instance a8fin_standardizeCoreQdec (π₁ π₂ : Equiv.Perm (Fin 3)) (k₁ k₂ : Fin 3 → ZMod 3) :
    Decidable (∀ x y : ZMod 7, x ≠ 0 → y ≠ 0 →
      vecMul ![0, 1, x, y] (a8MonK π₁ k₁) = ![0, 1, x, y] →
      vecMul ![0, 1, x, y] (a8MonK π₂ k₂) = ![0, 1, x, y] →
      ∃ (π : Equiv.Perm (Fin 3)) (k : Fin 3 → ZMod 3),
        a8MonK π k * a8MonK π₁ k₁ * a8MonK π.symm (fun j => -(k (π.symm j))) = genK 0 ∧
        a8MonK π k * a8MonK π₂ k₂ * a8MonK π.symm (fun j => -(k (π.symm j))) = genK 1) :=
  Fintype.decidableForallFintype

private lemma a8fin_standardize_core :
    ∀ (π₁ : Equiv.Perm (Fin 3)) (k₁ : Fin 3 → ZMod 3), a8MonK π₁ k₁ * a8MonK π₁ k₁ = 1 →
      ∀ (π₂ : Equiv.Perm (Fin 3)) (k₂ : Fin 3 → ZMod 3), a8MonK π₂ k₂ * a8MonK π₂ k₂ = 1 →
        (a8MonK π₁ k₁ * a8MonK π₂ k₂) ^ 3 = 1 → a8MonK π₁ k₁ * a8MonK π₂ k₂ ≠ 1 →
        ∀ x y : ZMod 7, x ≠ 0 → y ≠ 0 →
          vecMul ![0, 1, x, y] (a8MonK π₁ k₁) = ![0, 1, x, y] →
          vecMul ![0, 1, x, y] (a8MonK π₂ k₂) = ![0, 1, x, y] →
          ∃ (π : Equiv.Perm (Fin 3)) (k : Fin 3 → ZMod 3),
            a8MonK π k * a8MonK π₁ k₁ * a8MonK π.symm (fun j => -(k (π.symm j))) = genK 0 ∧
            a8MonK π k * a8MonK π₂ k₂ * a8MonK π.symm (fun j => -(k (π.symm j))) = genK 1 := by
  decide +kernel

private lemma a8fin_standardize_aux :
    ∀ (π₁ π₂ : Equiv.Perm (Fin 3)) (k₁ k₂ : Fin 3 → ZMod 3),
      (a8MonK π₁ k₁ * a8MonK π₁ k₁ = 1 ∧
       a8MonK π₂ k₂ * a8MonK π₂ k₂ = 1 ∧
       (a8MonK π₁ k₁ * a8MonK π₂ k₂) ^ 3 = 1 ∧
       a8MonK π₁ k₁ * a8MonK π₂ k₂ ≠ 1) →
      ∀ u : ZMod 7 × ZMod 7 × ZMod 7,
        (u.1 ≠ 0 ∧ u.2.1 ≠ 0 ∧ u.2.2 ≠ 0 ∧
         vecMul ![0, u.1, u.2.1, u.2.2] (a8MonK π₁ k₁) = ![0, u.1, u.2.1, u.2.2] ∧
         vecMul ![0, u.1, u.2.1, u.2.2] (a8MonK π₂ k₂) = ![0, u.1, u.2.1, u.2.2]) →
        ∃ (π : Equiv.Perm (Fin 3)) (k : Fin 3 → ZMod 3),
          a8MonK π k * a8MonK π₁ k₁ * a8MonK π.symm (fun j => -(k (π.symm j))) = genK 0 ∧
          a8MonK π k * a8MonK π₂ k₂ * a8MonK π.symm (fun j => -(k (π.symm j))) = genK 1 := by
  rintro π₁ π₂ k₁ k₂ ⟨hg, hh, hgh, hne⟩ ⟨u₁, u₂, u₃⟩ ⟨h₁, h₂, h₃, hvg, hvh⟩
  have hfix : ∀ M : M4, vecMul ![0, u₁, u₂, u₃] M = ![0, u₁, u₂, u₃] →
      vecMul ![0, 1, u₁⁻¹ * u₂, u₁⁻¹ * u₃] M = ![0, 1, u₁⁻¹ * u₂, u₁⁻¹ * u₃] := by
    intro M hM
    have e : (![0, 1, u₁⁻¹ * u₂, u₁⁻¹ * u₃] : Fin 4 → ZMod 7) = u₁⁻¹ • ![0, u₁, u₂, u₃] := by
      simp [a8fin_inv_mul_cancel u₁ h₁]
    rw [e, Matrix.smul_vecMul, hM]
  exact a8fin_standardize_core π₁ k₁ hg π₂ k₂ hh hgh hne _ _ (a8fin_inv_mul_ne_zero u₁ u₂ h₁ h₂)
    (a8fin_inv_mul_ne_zero u₁ u₃ h₁ h₃) (hfix _ hvg) (hfix _ hvh)

theorem a8_standardize {π₁ π₂ : Equiv.Perm (Fin 3)} {k₁ k₂ : Fin 3 → ZMod 3} {v : Fin 4 → ZMod 7}
    (hg : a8MonK π₁ k₁ * a8MonK π₁ k₁ = 1) (hh : a8MonK π₂ k₂ * a8MonK π₂ k₂ = 1)
    (hgh : (a8MonK π₁ k₁ * a8MonK π₂ k₂) ^ 3 = 1) (hne : a8MonK π₁ k₁ * a8MonK π₂ k₂ ≠ 1)
    (hv : ∀ i : Fin 3, v i.succ ≠ 0) (hvg : vecMul v (a8MonK π₁ k₁) = v)
    (hvh : vecMul v (a8MonK π₂ k₂) = v) :
    ∃ (π π' : Equiv.Perm (Fin 3)) (k k' : Fin 3 → ZMod 3),
      a8MonK π k * a8MonK π' k' = 1 ∧
        a8MonK π k * a8MonK π₁ k₁ * a8MonK π' k' = genK 0 ∧
        a8MonK π k * a8MonK π₂ k₂ * a8MonK π' k' = genK 1 := by
  obtain ⟨π, k, h0, h1⟩ := a8fin_standardize_aux π₁ π₂ k₁ k₂
    ⟨hg, hh, hgh, hne⟩
    (v 1, v 2, v 3)
    ⟨by simpa using hv 0, by simpa using hv 1, by simpa using hv 2,
      a8fin_vecMul_blk_zero_cons (a8MonK3 π₁ k₁) hvg,
      a8fin_vecMul_blk_zero_cons (a8MonK3 π₂ k₂) hvh⟩
  exact ⟨π, π.symm, k, fun j => -(k (π.symm j)), a8fin_monK_inv_formula π k, h0, h1⟩

theorem a8_fixed_genK {v : Fin 4 → ZMod 7} (h0 : vecMul v (genK 0) = v)
    (h1 : vecMul v (genK 1) = v) : v 1 = v 2 ∧ v 2 = v 3 := by
  constructor
  · have h := congrFun h0 2
    rw [Matrix.vecMul_apply_eq_sum, Fin.sum_univ_four] at h
    simpa [genK] using h
  · have h := congrFun h1 3
    rw [Matrix.vecMul_apply_eq_sum, Fin.sum_univ_four] at h
    simpa [genK] using h

@[expose] def a8Dscal (u : ZMod 7) : M4 := Matrix.diagonal ![1, u, u, u]

private lemma a8fin_dscal_mul_inv : ∀ u : ZMod 7, u ≠ 0 → a8Dscal u * a8Dscal u⁻¹ = 1 := by
  decide +kernel

theorem a8Dscal_comm (u : ZMod 7) (π : Equiv.Perm (Fin 3)) (k : Fin 3 → ZMod 3) :
    a8Dscal u * a8MonK π k = a8MonK π k * a8Dscal u := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [a8Dscal, a8MonK, blk, a8MonK3, Matrix.mul_apply, Fin.sum_univ_four, mul_comm]

theorem a8Dscal_mul_inv {u : ZMod 7} (hu : u ≠ 0) : a8Dscal u * a8Dscal u⁻¹ = 1 :=
  a8fin_dscal_mul_inv u hu

theorem a8PermMat_relations :
    a8PermMat (Equiv.swap 1 2) * a8PermMat (Equiv.swap 1 2) = 1 ∧
      a8PermMat (Equiv.swap 2 3) * a8PermMat (Equiv.swap 2 3) = 1 ∧
      (a8PermMat (Equiv.swap 1 2) * a8PermMat (Equiv.swap 2 3)) ^ 3 = 1 ∧
      a8PermMat (Equiv.swap 1 2) * a8PermMat (Equiv.swap 2 3) ≠ 1 := by
  decide +kernel

theorem a8_intertwiner {P : M4} (h₁ : genK 0 * P = P * a8PermMat (Equiv.swap 1 2))
    (h₂ : genK 1 * P = P * a8PermMat (Equiv.swap 2 3)) :
    P = a8P (P 0 0) (P 0 1) (P 1 0) (P 1 1) (P 1 2) := by
  have e01 : P 0 2 = P 0 1 := by
    have hh := congrFun (congrFun h₁ 0) 1
    simp (config := { decide := true })
      [Matrix.mul_apply, Fin.sum_univ_four, genK, a8PermMat] at hh
    exact hh.symm
  have e02 : P 0 3 = P 0 2 := by
    have hh := congrFun (congrFun h₂ 0) 2
    simp (config := { decide := true })
      [Matrix.mul_apply, Fin.sum_univ_four, genK, a8PermMat] at hh
    exact hh.symm
  have e10 : P 2 0 = P 1 0 := by
    have hh := congrFun (congrFun h₁ 1) 0
    simp (config := { decide := true })
      [Matrix.mul_apply, Fin.sum_univ_four, genK, a8PermMat] at hh
    exact hh
  have e11 : P 2 1 = P 1 2 := by
    have hh := congrFun (congrFun h₁ 1) 1
    simp (config := { decide := true })
      [Matrix.mul_apply, Fin.sum_univ_four, genK, a8PermMat] at hh
    exact hh
  have e12 : P 2 2 = P 1 1 := by
    have hh := congrFun (congrFun h₁ 1) 2
    simp (config := { decide := true })
      [Matrix.mul_apply, Fin.sum_univ_four, genK, a8PermMat] at hh
    exact hh
  have e13 : P 2 3 = P 1 3 := by
    have hh := congrFun (congrFun h₁ 1) 3
    simp (config := { decide := true })
      [Matrix.mul_apply, Fin.sum_univ_four, genK, a8PermMat] at hh
    exact hh
  have e20 : P 3 0 = P 2 0 := by
    have hh := congrFun (congrFun h₂ 2) 0
    simp (config := { decide := true })
      [Matrix.mul_apply, Fin.sum_univ_four, genK, a8PermMat] at hh
    exact hh
  have e21 : P 3 1 = P 2 1 := by
    have hh := congrFun (congrFun h₂ 2) 1
    simp (config := { decide := true })
      [Matrix.mul_apply, Fin.sum_univ_four, genK, a8PermMat] at hh
    exact hh
  have e22 : P 3 2 = P 2 3 := by
    have hh := congrFun (congrFun h₂ 2) 2
    simp (config := { decide := true })
      [Matrix.mul_apply, Fin.sum_univ_four, genK, a8PermMat] at hh
    exact hh
  have e23 : P 3 3 = P 2 2 := by
    have hh := congrFun (congrFun h₂ 2) 3
    simp (config := { decide := true })
      [Matrix.mul_apply, Fin.sum_univ_four, genK, a8PermMat] at hh
    exact hh
  have f13 : P 1 3 = P 1 2 := by
    have hh := congrFun (congrFun h₂ 1) 2
    simp (config := { decide := true })
      [Matrix.mul_apply, Fin.sum_univ_four, genK, a8PermMat] at hh
    exact hh.symm
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [a8P, e01, e02, e10, e11, e12, e13, e20, e21, e22, e23, f13]

private lemma a8fin_psi_wgen01 : ∀ μ : ZMod 7, μ ≠ 0 →
    psi (true, 0, 0, μ) * wgen true 0 * psiInv (true, 0, 0, μ) = !![6, 0, 0; 1, 1, 0; 0, 0, 1] ∧
      psi (true, 0, 0, μ) * wgen true 1 * psiInv (true, 0, 0, μ) =
        !![1, 1, 0; 0, 6, 0; 0, 0, 1] := by
  decide +kernel

private lemma a8fin_genL01_core : ∀ a β : ZMod 7, a * β ≠ 1 →
    basInv (true, a, β, 1) * blk !![6, 0, 0; 1, 1, 0; 0, 0, 1] * bas (true, a, β, 1) = genK 0 ∧
      basInv (true, a, β, 1) * blk !![1, 1, 0; 0, 6, 0; 0, 0, 1] * bas (true, a, β, 1) =
        genK 1 := by
  decide +kernel

private lemma a8fin_genL_zero_one :
    ∀ a β μ : ZMod 7, μ ≠ 0 → a * β ≠ 1 →
      genL (true, a, β, μ) 0 = genK 0 ∧ genL (true, a, β, μ) 1 = genK 1 := by
  intro a β μ hμ hab
  have hψ := a8fin_psi_wgen01 μ hμ
  change basInv (true, a, β, 1) * blk (psi (true, 0, 0, μ) * wgen true 0 * psiInv (true, 0, 0, μ)) *
      bas (true, a, β, 1) = genK 0 ∧
    basInv (true, a, β, 1) * blk (psi (true, 0, 0, μ) * wgen true 1 * psiInv (true, 0, 0, μ)) *
      bas (true, a, β, 1) = genK 1
  rw [hψ.1, hψ.2]
  exact a8fin_genL01_core a β hab

theorem a8_genL_zero_one {a β μ : ZMod 7} (hμ : μ ≠ 0) (hab : a * β ≠ 1) :
    genL (true, a, β, μ) 0 = genK 0 ∧ genL (true, a, β, μ) 1 = genK 1 :=
  a8fin_genL_zero_one a β μ hμ hab

private lemma a8fin_genLInf01_core : ∀ a : ZMod 7, a ≠ 0 →
    basInfInv a * blk !![6, 0, 0; 1, 1, 0; 0, 0, 1] * basInf a = genK 0 ∧
      basInfInv a * blk !![1, 1, 0; 0, 6, 0; 0, 0, 1] * basInf a = genK 1 := by
  decide +kernel

private lemma a8fin_genLInf_zero_one :
    ∀ a μ : ZMod 7, a ≠ 0 → μ ≠ 0 →
      genLInf a μ 0 = genK 0 ∧ genLInf a μ 1 = genK 1 := by
  intro a μ ha hμ
  have hψ := a8fin_psi_wgen01 μ hμ
  unfold genLInf
  rw [hψ.1, hψ.2]
  exact a8fin_genLInf01_core a ha

theorem a8_genLInf_zero_one {a μ : ZMod 7} (ha : a ≠ 0) (hμ : μ ≠ 0) :
    genLInf a μ 0 = genK 0 ∧ genLInf a μ 1 = genK 1 :=
  a8fin_genLInf_zero_one a μ ha hμ

private lemma a8fin_mem_allCases :
    ∀ a β μ : ZMod 7, μ ≠ 0 → a * β ≠ 1 → ((true, a, β, μ) : Case) ∈ allCases := by
  have hv : ∀ x : ZMod 7, x ∈ vals := by decide +kernel
  intro a β μ hμ hab
  simp only [allCases, List.mem_flatMap, List.mem_map, List.mem_filter]
  exact ⟨true, by simp, a, hv a, β, hv β, μ, ⟨hv μ, decide_eq_true ⟨hμ, hab⟩⟩, rfl⟩

theorem a8_mem_allCases {a β μ : ZMod 7} (hμ : μ ≠ 0) (hab : a * β ≠ 1) :
    ((true, a, β, μ) : Case) ∈ allCases :=
  a8fin_mem_allCases a β μ hμ hab

private lemma a8fin_zmod7_cases : ∀ a : ZMod 7,
    a = 0 ∨ a = 1 ∨ a = 2 ∨ a = 3 ∨ a = 4 ∨ a = 5 ∨ a = 6 := by
  decide +kernel

private lemma a8fin_wgen2_eq :
    wgen true 2 = (!![2, 3, 5; 6, 5, 2; 0, 0, 1] : M3) := by
  simp [wgen]

private lemma a8fin_genL2_inline_eq (a β μ : ZMod 7) :
    (basInv (true, a, β, μ) *
        blk (psi (true, a, β, μ) * (!![2, 3, 5; 6, 5, 2; 0, 0, 1] : M3) *
          psiInv (true, a, β, μ)) *
        bas (true, a, β, μ)) =
      genL (true, a, β, μ) 2 := by
  simp [genL, a8fin_wgen2_eq]

private lemma a8fin_genLInf2_inline_eq (a μ : ZMod 7) :
    (basInfInv a *
        blk (psi (true, 0, 0, μ) * (!![2, 3, 5; 6, 5, 2; 0, 0, 1] : M3) *
          psiInv (true, 0, 0, μ)) *
        basInf a) =
      genLInf a μ 2 := by
  simp [genLInf, a8fin_wgen2_eq]

private lemma a8fin_det_a8P (p₁ p₂ u₀ u₁ u₂ : ZMod 7) :
    (a8P p₁ p₂ u₀ u₁ u₂).det = (u₁ - u₂) ^ 2 * (p₁ * (u₁ + 2 * u₂) - 3 * p₂ * u₀) := by
  rw [Matrix.det_succ_row_zero]
  simp [Fin.sum_univ_succ, Matrix.det_fin_three, a8P, Fin.succAbove]
  ring

private lemma a8fin_vecMul_a8P {a p₁ p₂ u₀ u₁ u₂ : ZMod 7}
    (hx : vecMul ![a, 1, 1, 1] (a8P p₁ p₂ u₀ u₁ u₂) = fun _ => 1) :
    u₀ = 5 * (1 - a * p₁) ∧ u₁ = 1 - a * p₂ - 2 * u₂ := by
  have h0 : a * p₁ + u₀ + u₀ + u₀ = 1 := by
    simpa [Matrix.vecMul_apply_eq_sum, Fin.sum_univ_four, a8P] using congrFun hx 0
  have h1 : a * p₂ + u₁ + u₂ + u₂ = 1 := by
    simpa [Matrix.vecMul_apply_eq_sum, Fin.sum_univ_four, a8P] using congrFun hx 1
  constructor
  · calc u₀ = 5 * (a * p₁ + u₀ + u₀ + u₀) - 5 * (a * p₁) - 14 * u₀ := by ring
      _ = 5 * (1 - a * p₁) := by rw [h0, show (14 : ZMod 7) = 0 by decide]; ring
  · calc u₁ = (a * p₂ + u₁ + u₂ + u₂) - a * p₂ - 2 * u₂ := by ring
      _ = 1 - a * p₂ - 2 * u₂ := by rw [h1]

private lemma a8fin_mul_a8PermMat (P : M4) (σ : Equiv.Perm (Fin 4)) :
    P * a8PermMat σ = P.submatrix id σ.symm := by
  ext i j
  rw [Matrix.mul_apply, Finset.sum_eq_single (σ.symm j)]
  · simp [a8PermMat]
  · intro k _ hk
    have : σ k ≠ j := fun h => hk (by rw [← h, Equiv.symm_apply_apply])
    simp [a8PermMat, this]
  · intro h
    exact absurd (Finset.mem_univ _) h

private abbrev a8fin_MulSwap (X P : M4) : Prop :=
  ∀ i j : Fin 4,
    X i 0 * P 0 j + X i 1 * P 1 j + X i 2 * P 2 j + X i 3 * P 3 j = P i (Equiv.swap 0 1 j)

private lemma a8fin_mul_eq_of_mulSwap {X P : M4} (h : a8fin_MulSwap X P) :
    X * P = P * a8PermMat (Equiv.swap 0 1) := by
  ext i j
  rw [a8fin_mul_a8PermMat, Matrix.mul_apply, Fin.sum_univ_four, h i j, Matrix.submatrix_apply,
    id_eq, Equiv.symm_swap]

private abbrev a8fin_Psol (a p₁ p₂ u₂ : ZMod 7) : M4 :=
  a8P p₁ p₂ (5 * (1 - a * p₁)) (1 - a * p₂ - 2 * u₂) u₂

private abbrev a8fin_genL2 (a β μ : ZMod 7) : M4 :=
  basInv (true, a, β, 0) *
    blk (psi (true, 0, 0, μ) * (!![2, 3, 5; 6, 5, 2; 0, 0, 1] : M3) * psiInv (true, 0, 0, μ)) *
    bas (true, a, β, 0)

private abbrev a8fin_genLInf2 (a μ : ZMod 7) : M4 :=
  basInfInv a *
    blk (psi (true, 0, 0, μ) * (!![2, 3, 5; 6, 5, 2; 0, 0, 1] : M3) * psiInv (true, 0, 0, μ)) *
    basInf a

private lemma a8fin_match_core : ∀ a p₁ p₂ u₂ : ZMod 7,
    (1 - a * p₂ - 2 * u₂ - u₂) ^ 2 *
        (p₁ * (1 - a * p₂ - 2 * u₂ + 2 * u₂) - 3 * p₂ * (5 * (1 - a * p₁))) ≠ 0 →
      (∃ β : ZMod 7, (1 - a * p₁ + 3 * (1 - a * p₂)) * β = -(p₁ + 3 * p₂) ∧
        ∃ μ : ZMod 7, (1 - a * p₂ - 3 * u₂) * μ = 6 * (p₁ + β * (1 - a * p₁)) ∧
          μ ≠ 0 ∧ a * β ≠ 1 ∧ a8fin_MulSwap (a8fin_genL2 a β μ) (a8fin_Psol a p₁ p₂ u₂)) ∨
        ∃ μ : ZMod 7, (1 - a * p₂ - 3 * u₂) * μ = 6 * (1 - a * p₁) ∧ μ ≠ 0 ∧ a ≠ 0 ∧
          a8fin_MulSwap (a8fin_genLInf2 a μ) (a8fin_Psol a p₁ p₂ u₂) := by
  decide +kernel

private lemma a8fin_match_gen (a : ZMod 7) :
    ∀ p₁ p₂ u₀ u₁ u₂ : ZMod 7,
      (vecMul ![a, 1, 1, 1] (a8P p₁ p₂ u₀ u₁ u₂) = (fun _ => 1) ∧
       (a8P p₁ p₂ u₀ u₁ u₂).det ≠ 0) →
      (∃ β μ : ZMod 7, μ ≠ 0 ∧ a * β ≠ 1 ∧
          (basInv (true, a, β, μ) *
              blk (psi (true, a, β, μ) * (!![2, 3, 5; 6, 5, 2; 0, 0, 1] : M3) *
                psiInv (true, a, β, μ)) *
              bas (true, a, β, μ)) * a8P p₁ p₂ u₀ u₁ u₂ =
            a8P p₁ p₂ u₀ u₁ u₂ * a8PermMat (Equiv.swap 0 1)) ∨
        (∃ μ : ZMod 7, μ ≠ 0 ∧ a ≠ 0 ∧
          (basInfInv a *
              blk (psi (true, 0, 0, μ) * (!![2, 3, 5; 6, 5, 2; 0, 0, 1] : M3) *
                psiInv (true, 0, 0, μ)) *
              basInf a) * a8P p₁ p₂ u₀ u₁ u₂ =
            a8P p₁ p₂ u₀ u₁ u₂ * a8PermMat (Equiv.swap 0 1)) := by
  rintro p₁ p₂ u₀ u₁ u₂ ⟨hx, hdet⟩
  obtain ⟨rfl, rfl⟩ := a8fin_vecMul_a8P hx
  rw [a8fin_det_a8P] at hdet
  rcases a8fin_match_core a p₁ p₂ u₂ hdet with ⟨β, -, μ, -, hμ, hβ, h⟩ | ⟨μ, -, hμ, ha, h⟩
  · exact Or.inl ⟨β, μ, hμ, hβ, a8fin_mul_eq_of_mulSwap h⟩
  · exact Or.inr ⟨μ, hμ, ha, a8fin_mul_eq_of_mulSwap h⟩

private lemma a8fin_match_aux0 :
    ∀ p₁ p₂ u₀ u₁ u₂ : ZMod 7,
      (vecMul ![0, 1, 1, 1] (a8P p₁ p₂ u₀ u₁ u₂) = (fun _ => 1) ∧
       (a8P p₁ p₂ u₀ u₁ u₂).det ≠ 0) →
      (∃ β μ : ZMod 7, μ ≠ 0 ∧ (0 : ZMod 7) * β ≠ 1 ∧
          (basInv (true, 0, β, μ) *
              blk (psi (true, 0, β, μ) * (!![2, 3, 5; 6, 5, 2; 0, 0, 1] : M3) *
                psiInv (true, 0, β, μ)) *
              bas (true, 0, β, μ)) * a8P p₁ p₂ u₀ u₁ u₂ =
            a8P p₁ p₂ u₀ u₁ u₂ * a8PermMat (Equiv.swap 0 1)) ∨
        (∃ μ : ZMod 7, μ ≠ 0 ∧ (0 : ZMod 7) ≠ 0 ∧
          (basInfInv 0 *
              blk (psi (true, 0, 0, μ) * (!![2, 3, 5; 6, 5, 2; 0, 0, 1] : M3) *
                psiInv (true, 0, 0, μ)) *
              basInf 0) * a8P p₁ p₂ u₀ u₁ u₂ =
            a8P p₁ p₂ u₀ u₁ u₂ * a8PermMat (Equiv.swap 0 1)) :=
  a8fin_match_gen 0

private lemma a8fin_match_aux1 :
    ∀ p₁ p₂ u₀ u₁ u₂ : ZMod 7,
      (vecMul ![1, 1, 1, 1] (a8P p₁ p₂ u₀ u₁ u₂) = (fun _ => 1) ∧
       (a8P p₁ p₂ u₀ u₁ u₂).det ≠ 0) →
      (∃ β μ : ZMod 7, μ ≠ 0 ∧ (1 : ZMod 7) * β ≠ 1 ∧
          (basInv (true, 1, β, μ) *
              blk (psi (true, 1, β, μ) * (!![2, 3, 5; 6, 5, 2; 0, 0, 1] : M3) *
                psiInv (true, 1, β, μ)) *
              bas (true, 1, β, μ)) * a8P p₁ p₂ u₀ u₁ u₂ =
            a8P p₁ p₂ u₀ u₁ u₂ * a8PermMat (Equiv.swap 0 1)) ∨
        (∃ μ : ZMod 7, μ ≠ 0 ∧ (1 : ZMod 7) ≠ 0 ∧
          (basInfInv 1 *
              blk (psi (true, 0, 0, μ) * (!![2, 3, 5; 6, 5, 2; 0, 0, 1] : M3) *
                psiInv (true, 0, 0, μ)) *
              basInf 1) * a8P p₁ p₂ u₀ u₁ u₂ =
            a8P p₁ p₂ u₀ u₁ u₂ * a8PermMat (Equiv.swap 0 1)) :=
  a8fin_match_gen 1

private lemma a8fin_match_aux2 :
    ∀ p₁ p₂ u₀ u₁ u₂ : ZMod 7,
      (vecMul ![2, 1, 1, 1] (a8P p₁ p₂ u₀ u₁ u₂) = (fun _ => 1) ∧
       (a8P p₁ p₂ u₀ u₁ u₂).det ≠ 0) →
      (∃ β μ : ZMod 7, μ ≠ 0 ∧ (2 : ZMod 7) * β ≠ 1 ∧
          (basInv (true, 2, β, μ) *
              blk (psi (true, 2, β, μ) * (!![2, 3, 5; 6, 5, 2; 0, 0, 1] : M3) *
                psiInv (true, 2, β, μ)) *
              bas (true, 2, β, μ)) * a8P p₁ p₂ u₀ u₁ u₂ =
            a8P p₁ p₂ u₀ u₁ u₂ * a8PermMat (Equiv.swap 0 1)) ∨
        (∃ μ : ZMod 7, μ ≠ 0 ∧ (2 : ZMod 7) ≠ 0 ∧
          (basInfInv 2 *
              blk (psi (true, 0, 0, μ) * (!![2, 3, 5; 6, 5, 2; 0, 0, 1] : M3) *
                psiInv (true, 0, 0, μ)) *
              basInf 2) * a8P p₁ p₂ u₀ u₁ u₂ =
            a8P p₁ p₂ u₀ u₁ u₂ * a8PermMat (Equiv.swap 0 1)) :=
  a8fin_match_gen 2

private lemma a8fin_match_aux3 :
    ∀ p₁ p₂ u₀ u₁ u₂ : ZMod 7,
      (vecMul ![3, 1, 1, 1] (a8P p₁ p₂ u₀ u₁ u₂) = (fun _ => 1) ∧
       (a8P p₁ p₂ u₀ u₁ u₂).det ≠ 0) →
      (∃ β μ : ZMod 7, μ ≠ 0 ∧ (3 : ZMod 7) * β ≠ 1 ∧
          (basInv (true, 3, β, μ) *
              blk (psi (true, 3, β, μ) * (!![2, 3, 5; 6, 5, 2; 0, 0, 1] : M3) *
                psiInv (true, 3, β, μ)) *
              bas (true, 3, β, μ)) * a8P p₁ p₂ u₀ u₁ u₂ =
            a8P p₁ p₂ u₀ u₁ u₂ * a8PermMat (Equiv.swap 0 1)) ∨
        (∃ μ : ZMod 7, μ ≠ 0 ∧ (3 : ZMod 7) ≠ 0 ∧
          (basInfInv 3 *
              blk (psi (true, 0, 0, μ) * (!![2, 3, 5; 6, 5, 2; 0, 0, 1] : M3) *
                psiInv (true, 0, 0, μ)) *
              basInf 3) * a8P p₁ p₂ u₀ u₁ u₂ =
            a8P p₁ p₂ u₀ u₁ u₂ * a8PermMat (Equiv.swap 0 1)) :=
  a8fin_match_gen 3

private lemma a8fin_match_aux4 :
    ∀ p₁ p₂ u₀ u₁ u₂ : ZMod 7,
      (vecMul ![4, 1, 1, 1] (a8P p₁ p₂ u₀ u₁ u₂) = (fun _ => 1) ∧
       (a8P p₁ p₂ u₀ u₁ u₂).det ≠ 0) →
      (∃ β μ : ZMod 7, μ ≠ 0 ∧ (4 : ZMod 7) * β ≠ 1 ∧
          (basInv (true, 4, β, μ) *
              blk (psi (true, 4, β, μ) * (!![2, 3, 5; 6, 5, 2; 0, 0, 1] : M3) *
                psiInv (true, 4, β, μ)) *
              bas (true, 4, β, μ)) * a8P p₁ p₂ u₀ u₁ u₂ =
            a8P p₁ p₂ u₀ u₁ u₂ * a8PermMat (Equiv.swap 0 1)) ∨
        (∃ μ : ZMod 7, μ ≠ 0 ∧ (4 : ZMod 7) ≠ 0 ∧
          (basInfInv 4 *
              blk (psi (true, 0, 0, μ) * (!![2, 3, 5; 6, 5, 2; 0, 0, 1] : M3) *
                psiInv (true, 0, 0, μ)) *
              basInf 4) * a8P p₁ p₂ u₀ u₁ u₂ =
            a8P p₁ p₂ u₀ u₁ u₂ * a8PermMat (Equiv.swap 0 1)) :=
  a8fin_match_gen 4

private lemma a8fin_match_aux5 :
    ∀ p₁ p₂ u₀ u₁ u₂ : ZMod 7,
      (vecMul ![5, 1, 1, 1] (a8P p₁ p₂ u₀ u₁ u₂) = (fun _ => 1) ∧
       (a8P p₁ p₂ u₀ u₁ u₂).det ≠ 0) →
      (∃ β μ : ZMod 7, μ ≠ 0 ∧ (5 : ZMod 7) * β ≠ 1 ∧
          (basInv (true, 5, β, μ) *
              blk (psi (true, 5, β, μ) * (!![2, 3, 5; 6, 5, 2; 0, 0, 1] : M3) *
                psiInv (true, 5, β, μ)) *
              bas (true, 5, β, μ)) * a8P p₁ p₂ u₀ u₁ u₂ =
            a8P p₁ p₂ u₀ u₁ u₂ * a8PermMat (Equiv.swap 0 1)) ∨
        (∃ μ : ZMod 7, μ ≠ 0 ∧ (5 : ZMod 7) ≠ 0 ∧
          (basInfInv 5 *
              blk (psi (true, 0, 0, μ) * (!![2, 3, 5; 6, 5, 2; 0, 0, 1] : M3) *
                psiInv (true, 0, 0, μ)) *
              basInf 5) * a8P p₁ p₂ u₀ u₁ u₂ =
            a8P p₁ p₂ u₀ u₁ u₂ * a8PermMat (Equiv.swap 0 1)) :=
  a8fin_match_gen 5

private lemma a8fin_match_aux6 :
    ∀ p₁ p₂ u₀ u₁ u₂ : ZMod 7,
      (vecMul ![6, 1, 1, 1] (a8P p₁ p₂ u₀ u₁ u₂) = (fun _ => 1) ∧
       (a8P p₁ p₂ u₀ u₁ u₂).det ≠ 0) →
      (∃ β μ : ZMod 7, μ ≠ 0 ∧ (6 : ZMod 7) * β ≠ 1 ∧
          (basInv (true, 6, β, μ) *
              blk (psi (true, 6, β, μ) * (!![2, 3, 5; 6, 5, 2; 0, 0, 1] : M3) *
                psiInv (true, 6, β, μ)) *
              bas (true, 6, β, μ)) * a8P p₁ p₂ u₀ u₁ u₂ =
            a8P p₁ p₂ u₀ u₁ u₂ * a8PermMat (Equiv.swap 0 1)) ∨
        (∃ μ : ZMod 7, μ ≠ 0 ∧ (6 : ZMod 7) ≠ 0 ∧
          (basInfInv 6 *
              blk (psi (true, 0, 0, μ) * (!![2, 3, 5; 6, 5, 2; 0, 0, 1] : M3) *
                psiInv (true, 0, 0, μ)) *
              basInf 6) * a8P p₁ p₂ u₀ u₁ u₂ =
            a8P p₁ p₂ u₀ u₁ u₂ * a8PermMat (Equiv.swap 0 1)) :=
  a8fin_match_gen 6

theorem a8_match {a p₁ p₂ u₀ u₁ u₂ : ZMod 7}
    (hx : vecMul ![a, 1, 1, 1] (a8P p₁ p₂ u₀ u₁ u₂) = fun _ => 1)
    (hdet : (a8P p₁ p₂ u₀ u₁ u₂).det ≠ 0) :
    (∃ β μ : ZMod 7, μ ≠ 0 ∧ a * β ≠ 1 ∧
        genL (true, a, β, μ) 2 * a8P p₁ p₂ u₀ u₁ u₂ =
          a8P p₁ p₂ u₀ u₁ u₂ * a8PermMat (Equiv.swap 0 1)) ∨
      (∃ μ : ZMod 7, μ ≠ 0 ∧ a ≠ 0 ∧
        genLInf a μ 2 * a8P p₁ p₂ u₀ u₁ u₂ = a8P p₁ p₂ u₀ u₁ u₂ * a8PermMat (Equiv.swap 0 1)) := by
  rcases a8fin_zmod7_cases a with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · simpa [a8fin_genL2_inline_eq, a8fin_genLInf2_inline_eq] using
      a8fin_match_aux0 p₁ p₂ u₀ u₁ u₂ ⟨hx, hdet⟩
  · simpa [a8fin_genL2_inline_eq, a8fin_genLInf2_inline_eq] using
      a8fin_match_aux1 p₁ p₂ u₀ u₁ u₂ ⟨hx, hdet⟩
  · simpa [a8fin_genL2_inline_eq, a8fin_genLInf2_inline_eq] using
      a8fin_match_aux2 p₁ p₂ u₀ u₁ u₂ ⟨hx, hdet⟩
  · simpa [a8fin_genL2_inline_eq, a8fin_genLInf2_inline_eq] using
      a8fin_match_aux3 p₁ p₂ u₀ u₁ u₂ ⟨hx, hdet⟩
  · simpa [a8fin_genL2_inline_eq, a8fin_genLInf2_inline_eq] using
      a8fin_match_aux4 p₁ p₂ u₀ u₁ u₂ ⟨hx, hdet⟩
  · simpa [a8fin_genL2_inline_eq, a8fin_genLInf2_inline_eq] using
      a8fin_match_aux5 p₁ p₂ u₀ u₁ u₂ ⟨hx, hdet⟩
  · simpa [a8fin_genL2_inline_eq, a8fin_genLInf2_inline_eq] using
      a8fin_match_aux6 p₁ p₂ u₀ u₁ u₂ ⟨hx, hdet⟩

end CFSG.StandardType.A8Coord

end
