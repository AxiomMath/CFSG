module

public import CFSG.LocalAnalysis.StandardType.GGA8NbrFinite
public import CFSG.LocalAnalysis.StandardType.GGA8NbrInfDataB
public import CFSG.LocalAnalysis.StandardType.GGA8NbrCoordDefsB

public section

namespace CFSG.StandardType.A8Coord

open Certificates.A8Nbr476 CFSG.StandardType.A8NbrInf CFSG.StandardType.A8NbrInfB Matrix

private lemma a8bf_mul_four (A B : M4) :
    A * B = Matrix.of fun i j => A i 0 * B 0 j + A i 1 * B 1 j + A i 2 * B 2 j + A i 3 * B 3 j := by
  ext i j
  simp [Matrix.mul_apply, Fin.sum_univ_four]

private lemma a8bf_mul_three (A B : M3) :
    A * B = Matrix.of fun i j => A i 0 * B 0 j + A i 1 * B 1 j + A i 2 * B 2 j := by
  ext i j
  simp [Matrix.mul_apply, Fin.sum_univ_three]

private lemma a8bf_mul_signThree (M : M4) :
    M * a8SignThree = Matrix.of fun i j => M i j * ![1, 1, 1, -1] j := by
  ext i j
  simp [a8SignThree, Matrix.mul_diagonal]

private lemma a8bf_psi_wgen_zero_one :
    ∀ μ : ZMod 7, μ ≠ 0 →
      psi (false, 0, 0, μ) * wgen false 0 * psiInv (false, 0, 0, μ) =
          !![6, 0, 0; 1, 1, 0; 0, 0, 1] ∧
        psi (false, 0, 0, μ) * wgen false 1 * psiInv (false, 0, 0, μ) =
          !![1, 1, 0; 0, 6, 0; 0, 0, 1] := by
  decide +kernel

private lemma a8bf_bas_conj_zero_one :
    ∀ a β : ZMod 7, a * β ≠ 1 →
      basInv (false, a, β, 0) * blk !![6, 0, 0; 1, 1, 0; 0, 0, 1] * bas (false, a, β, 0) =
          genK 0 ∧
        basInv (false, a, β, 0) * blk !![1, 1, 0; 0, 6, 0; 0, 0, 1] * bas (false, a, β, 0) =
          genK 1 := by
  simp only [a8bf_mul_four]
  decide +kernel

private lemma a8bf_genL_zero_one :
    ∀ a β μ : ZMod 7, μ ≠ 0 → a * β ≠ 1 →
      genL (false, a, β, μ) 0 = genK 0 ∧ genL (false, a, β, μ) 1 = genK 1 := by
  intro a β μ hμ hab
  obtain ⟨h0, h1⟩ := a8bf_psi_wgen_zero_one μ hμ
  obtain ⟨k0, k1⟩ := a8bf_bas_conj_zero_one a β hab
  exact ⟨(congrArg (fun Y => basInv (false, a, β, μ) * blk Y * bas (false, a, β, μ)) h0).trans k0,
    (congrArg (fun Y => basInv (false, a, β, μ) * blk Y * bas (false, a, β, μ)) h1).trans k1⟩

theorem a8B_genL_zero_one {a β μ : ZMod 7} (hμ : μ ≠ 0) (hab : a * β ≠ 1) :
    genL (false, a, β, μ) 0 = genK 0 ∧ genL (false, a, β, μ) 1 = genK 1 :=
  a8bf_genL_zero_one a β μ hμ hab

private lemma a8bf_basInf_conj_zero_one :
    ∀ a : ZMod 7, a ≠ 0 →
      basInfInv a * blk !![6, 0, 0; 1, 1, 0; 0, 0, 1] * basInf a = genK 0 ∧
        basInfInv a * blk !![1, 1, 0; 0, 6, 0; 0, 0, 1] * basInf a = genK 1 := by
  simp only [a8bf_mul_four]
  decide +kernel

private lemma a8bf_genLInfB_zero_one :
    ∀ a μ : ZMod 7, a ≠ 0 → μ ≠ 0 →
      genLInfB a μ 0 = genK 0 ∧ genLInfB a μ 1 = genK 1 := by
  intro a μ ha hμ
  obtain ⟨h0, h1⟩ := a8bf_psi_wgen_zero_one μ hμ
  obtain ⟨k0, k1⟩ := a8bf_basInf_conj_zero_one a ha
  exact ⟨(congrArg (fun Y => basInfInv a * blk Y * basInf a) h0).trans k0,
    (congrArg (fun Y => basInfInv a * blk Y * basInf a) h1).trans k1⟩

theorem a8B_genLInfB_zero_one {a μ : ZMod 7} (ha : a ≠ 0) (hμ : μ ≠ 0) :
    genLInfB a μ 0 = genK 0 ∧ genLInfB a μ 1 = genK 1 :=
  a8bf_genLInfB_zero_one a μ ha hμ

private lemma a8bf_mem_vals : ∀ x : ZMod 7, x ∈ vals := by
  decide

private lemma a8bf_mem_allCases :
    ∀ a β μ : ZMod 7, μ ≠ 0 → a * β ≠ 1 → ((false, a, β, μ) : Case) ∈ allCases := by
  intro a β μ hμ hab
  simp only [allCases, List.mem_flatMap, List.mem_map, List.mem_filter]
  exact ⟨false, by simp, a, a8bf_mem_vals a, β, a8bf_mem_vals β, μ,
    ⟨a8bf_mem_vals μ, by simp [hμ, hab]⟩, rfl⟩

theorem a8B_mem_allCases {a β μ : ZMod 7} (hμ : μ ≠ 0) (hab : a * β ≠ 1) :
    ((false, a, β, μ) : Case) ∈ allCases :=
  a8bf_mem_allCases a β μ hμ hab

private lemma a8bf_wgen2_eq :
    wgen false 2 = (!![1, 0, 0; 0, 1, 0; 0, 0, 6] : M3) := by
  simp [wgen]

private lemma a8bf_genL2_inline_eq (a β μ : ZMod 7) :
    (basInv (false, a, β, μ) *
        blk (psi (false, a, β, μ) * (!![1, 0, 0; 0, 1, 0; 0, 0, 6] : M3) *
          psiInv (false, a, β, μ)) *
        bas (false, a, β, μ)) =
      genL (false, a, β, μ) 2 := by
  simp [genL, a8bf_wgen2_eq]

private lemma a8bf_genLInfB2_inline_eq (a μ : ZMod 7) :
    (basInfInv a *
        blk (psi (false, 0, 0, μ) * (!![1, 0, 0; 0, 1, 0; 0, 0, 6] : M3) *
          psiInv (false, 0, 0, μ)) *
        basInf a) =
      genLInfB a μ 2 := by
  simp [genLInfB, a8bf_wgen2_eq]

private lemma a8bf_zmod7_cases : ∀ a : ZMod 7,
    a = 0 ∨ a = 1 ∨ a = 2 ∨ a = 3 ∨ a = 4 ∨ a = 5 ∨ a = 6 := by
  decide +kernel

private lemma a8bf_det_a8P (p₁ p₂ u₀ u₁ u₂ : ZMod 7) :
    (a8P p₁ p₂ u₀ u₁ u₂).det = (u₁ - u₂) ^ 2 * (p₁ * (u₁ + 2 * u₂) - 3 * p₂ * u₀) := by
  rw [Matrix.det_succ_row_zero, Fin.sum_univ_succ, Fin.sum_univ_succ, Fin.sum_univ_succ,
    Fin.sum_univ_one]
  simp only [Matrix.det_fin_three, Matrix.submatrix_apply, Fin.succAbove, Fin.castSucc, Fin.succ]
  simp [a8P]
  ring

private lemma a8bf_inv_three : ∀ x u : ZMod 7, x + 3 * u = 1 → u = 5 * (1 - x) := by
  decide

private lemma a8bf_solve {a p₁ p₂ u₀ u₁ u₂ : ZMod 7}
    (hx : vecMul ![a, 1, 1, 1] (a8P p₁ p₂ u₀ u₁ u₂) = Pi.single 0 1) :
    u₀ = 5 * (1 - a * p₁) ∧ u₁ = -(a * p₂) - 2 * u₂ := by
  have h0 := congrFun hx 0
  have h1 := congrFun hx 1
  simp [vecMul, dotProduct, Fin.sum_univ_four, a8P] at h0 h1
  exact ⟨a8bf_inv_three _ _ (by linear_combination h0), by linear_combination h1⟩

private lemma a8bf_match_key :
    ∀ a p₁ p₂ u₂ : ZMod 7,
      (a8P p₁ p₂ (5 * (1 - a * p₁)) (-(a * p₂) - 2 * u₂) u₂).det ≠ 0 →
      (∃ β : ZMod 7, p₁ + β * (1 - a * p₁) = 0 ∧
        ∃ μ : ZMod 7, μ * (-(a * p₂) - 3 * u₂) = p₂ * (1 - a * β) ∧ μ ≠ 0 ∧ a * β ≠ 1 ∧
          (basInv (false, a, β, μ) *
              blk (psi (false, a, β, μ) * (!![1, 0, 0; 0, 1, 0; 0, 0, 6] : M3) *
                psiInv (false, a, β, μ)) *
              bas (false, a, β, μ)) * a8P p₁ p₂ (5 * (1 - a * p₁)) (-(a * p₂) - 2 * u₂) u₂ =
            a8P p₁ p₂ (5 * (1 - a * p₁)) (-(a * p₂) - 2 * u₂) u₂ * a8SignThree) ∨
        (∃ μ : ZMod 7, μ * (-(a * p₂) - 3 * u₂) = -(a * p₂) ∧ μ ≠ 0 ∧ a ≠ 0 ∧
          (basInfInv a *
              blk (psi (false, 0, 0, μ) * (!![1, 0, 0; 0, 1, 0; 0, 0, 6] : M3) *
                psiInv (false, 0, 0, μ)) *
              basInf a) * a8P p₁ p₂ (5 * (1 - a * p₁)) (-(a * p₂) - 2 * u₂) u₂ =
            a8P p₁ p₂ (5 * (1 - a * p₁)) (-(a * p₂) - 2 * u₂) u₂ * a8SignThree) := by
  simp only [a8bf_det_a8P, a8bf_mul_signThree]
  simp only [a8bf_mul_four, a8bf_mul_three]
  decide +kernel

private lemma a8bf_match_aux0 :
    ∀ p₁ p₂ u₀ u₁ u₂ : ZMod 7,
      (vecMul ![0, 1, 1, 1] (a8P p₁ p₂ u₀ u₁ u₂) = Pi.single 0 1 ∧
       (a8P p₁ p₂ u₀ u₁ u₂).det ≠ 0) →
      (∃ β μ : ZMod 7, μ ≠ 0 ∧ (0 : ZMod 7) * β ≠ 1 ∧
          (basInv (false, 0, β, μ) *
              blk (psi (false, 0, β, μ) * (!![1, 0, 0; 0, 1, 0; 0, 0, 6] : M3) *
                psiInv (false, 0, β, μ)) *
              bas (false, 0, β, μ)) * a8P p₁ p₂ u₀ u₁ u₂ =
            a8P p₁ p₂ u₀ u₁ u₂ * a8SignThree) ∨
        (∃ μ : ZMod 7, μ ≠ 0 ∧ (0 : ZMod 7) ≠ 0 ∧
          (basInfInv 0 *
              blk (psi (false, 0, 0, μ) * (!![1, 0, 0; 0, 1, 0; 0, 0, 6] : M3) *
                psiInv (false, 0, 0, μ)) *
              basInf 0) * a8P p₁ p₂ u₀ u₁ u₂ =
            a8P p₁ p₂ u₀ u₁ u₂ * a8SignThree) := by
  intro p₁ p₂ u₀ u₁ u₂ ⟨hx, hdet⟩
  obtain ⟨rfl, rfl⟩ := a8bf_solve hx
  exact (a8bf_match_key 0 p₁ p₂ u₂ hdet).imp (fun ⟨β, _, μ, _, h⟩ => ⟨β, μ, h⟩)
    fun ⟨μ, _, h⟩ => ⟨μ, h⟩

private lemma a8bf_match_aux1 :
    ∀ p₁ p₂ u₀ u₁ u₂ : ZMod 7,
      (vecMul ![1, 1, 1, 1] (a8P p₁ p₂ u₀ u₁ u₂) = Pi.single 0 1 ∧
       (a8P p₁ p₂ u₀ u₁ u₂).det ≠ 0) →
      (∃ β μ : ZMod 7, μ ≠ 0 ∧ (1 : ZMod 7) * β ≠ 1 ∧
          (basInv (false, 1, β, μ) *
              blk (psi (false, 1, β, μ) * (!![1, 0, 0; 0, 1, 0; 0, 0, 6] : M3) *
                psiInv (false, 1, β, μ)) *
              bas (false, 1, β, μ)) * a8P p₁ p₂ u₀ u₁ u₂ =
            a8P p₁ p₂ u₀ u₁ u₂ * a8SignThree) ∨
        (∃ μ : ZMod 7, μ ≠ 0 ∧ (1 : ZMod 7) ≠ 0 ∧
          (basInfInv 1 *
              blk (psi (false, 0, 0, μ) * (!![1, 0, 0; 0, 1, 0; 0, 0, 6] : M3) *
                psiInv (false, 0, 0, μ)) *
              basInf 1) * a8P p₁ p₂ u₀ u₁ u₂ =
            a8P p₁ p₂ u₀ u₁ u₂ * a8SignThree) := by
  intro p₁ p₂ u₀ u₁ u₂ ⟨hx, hdet⟩
  obtain ⟨rfl, rfl⟩ := a8bf_solve hx
  exact (a8bf_match_key 1 p₁ p₂ u₂ hdet).imp (fun ⟨β, _, μ, _, h⟩ => ⟨β, μ, h⟩)
    fun ⟨μ, _, h⟩ => ⟨μ, h⟩

private lemma a8bf_match_aux2 :
    ∀ p₁ p₂ u₀ u₁ u₂ : ZMod 7,
      (vecMul ![2, 1, 1, 1] (a8P p₁ p₂ u₀ u₁ u₂) = Pi.single 0 1 ∧
       (a8P p₁ p₂ u₀ u₁ u₂).det ≠ 0) →
      (∃ β μ : ZMod 7, μ ≠ 0 ∧ (2 : ZMod 7) * β ≠ 1 ∧
          (basInv (false, 2, β, μ) *
              blk (psi (false, 2, β, μ) * (!![1, 0, 0; 0, 1, 0; 0, 0, 6] : M3) *
                psiInv (false, 2, β, μ)) *
              bas (false, 2, β, μ)) * a8P p₁ p₂ u₀ u₁ u₂ =
            a8P p₁ p₂ u₀ u₁ u₂ * a8SignThree) ∨
        (∃ μ : ZMod 7, μ ≠ 0 ∧ (2 : ZMod 7) ≠ 0 ∧
          (basInfInv 2 *
              blk (psi (false, 0, 0, μ) * (!![1, 0, 0; 0, 1, 0; 0, 0, 6] : M3) *
                psiInv (false, 0, 0, μ)) *
              basInf 2) * a8P p₁ p₂ u₀ u₁ u₂ =
            a8P p₁ p₂ u₀ u₁ u₂ * a8SignThree) := by
  intro p₁ p₂ u₀ u₁ u₂ ⟨hx, hdet⟩
  obtain ⟨rfl, rfl⟩ := a8bf_solve hx
  exact (a8bf_match_key 2 p₁ p₂ u₂ hdet).imp (fun ⟨β, _, μ, _, h⟩ => ⟨β, μ, h⟩)
    fun ⟨μ, _, h⟩ => ⟨μ, h⟩

private lemma a8bf_match_aux3 :
    ∀ p₁ p₂ u₀ u₁ u₂ : ZMod 7,
      (vecMul ![3, 1, 1, 1] (a8P p₁ p₂ u₀ u₁ u₂) = Pi.single 0 1 ∧
       (a8P p₁ p₂ u₀ u₁ u₂).det ≠ 0) →
      (∃ β μ : ZMod 7, μ ≠ 0 ∧ (3 : ZMod 7) * β ≠ 1 ∧
          (basInv (false, 3, β, μ) *
              blk (psi (false, 3, β, μ) * (!![1, 0, 0; 0, 1, 0; 0, 0, 6] : M3) *
                psiInv (false, 3, β, μ)) *
              bas (false, 3, β, μ)) * a8P p₁ p₂ u₀ u₁ u₂ =
            a8P p₁ p₂ u₀ u₁ u₂ * a8SignThree) ∨
        (∃ μ : ZMod 7, μ ≠ 0 ∧ (3 : ZMod 7) ≠ 0 ∧
          (basInfInv 3 *
              blk (psi (false, 0, 0, μ) * (!![1, 0, 0; 0, 1, 0; 0, 0, 6] : M3) *
                psiInv (false, 0, 0, μ)) *
              basInf 3) * a8P p₁ p₂ u₀ u₁ u₂ =
            a8P p₁ p₂ u₀ u₁ u₂ * a8SignThree) := by
  intro p₁ p₂ u₀ u₁ u₂ ⟨hx, hdet⟩
  obtain ⟨rfl, rfl⟩ := a8bf_solve hx
  exact (a8bf_match_key 3 p₁ p₂ u₂ hdet).imp (fun ⟨β, _, μ, _, h⟩ => ⟨β, μ, h⟩)
    fun ⟨μ, _, h⟩ => ⟨μ, h⟩

private lemma a8bf_match_aux4 :
    ∀ p₁ p₂ u₀ u₁ u₂ : ZMod 7,
      (vecMul ![4, 1, 1, 1] (a8P p₁ p₂ u₀ u₁ u₂) = Pi.single 0 1 ∧
       (a8P p₁ p₂ u₀ u₁ u₂).det ≠ 0) →
      (∃ β μ : ZMod 7, μ ≠ 0 ∧ (4 : ZMod 7) * β ≠ 1 ∧
          (basInv (false, 4, β, μ) *
              blk (psi (false, 4, β, μ) * (!![1, 0, 0; 0, 1, 0; 0, 0, 6] : M3) *
                psiInv (false, 4, β, μ)) *
              bas (false, 4, β, μ)) * a8P p₁ p₂ u₀ u₁ u₂ =
            a8P p₁ p₂ u₀ u₁ u₂ * a8SignThree) ∨
        (∃ μ : ZMod 7, μ ≠ 0 ∧ (4 : ZMod 7) ≠ 0 ∧
          (basInfInv 4 *
              blk (psi (false, 0, 0, μ) * (!![1, 0, 0; 0, 1, 0; 0, 0, 6] : M3) *
                psiInv (false, 0, 0, μ)) *
              basInf 4) * a8P p₁ p₂ u₀ u₁ u₂ =
            a8P p₁ p₂ u₀ u₁ u₂ * a8SignThree) := by
  intro p₁ p₂ u₀ u₁ u₂ ⟨hx, hdet⟩
  obtain ⟨rfl, rfl⟩ := a8bf_solve hx
  exact (a8bf_match_key 4 p₁ p₂ u₂ hdet).imp (fun ⟨β, _, μ, _, h⟩ => ⟨β, μ, h⟩)
    fun ⟨μ, _, h⟩ => ⟨μ, h⟩

private lemma a8bf_match_aux5 :
    ∀ p₁ p₂ u₀ u₁ u₂ : ZMod 7,
      (vecMul ![5, 1, 1, 1] (a8P p₁ p₂ u₀ u₁ u₂) = Pi.single 0 1 ∧
       (a8P p₁ p₂ u₀ u₁ u₂).det ≠ 0) →
      (∃ β μ : ZMod 7, μ ≠ 0 ∧ (5 : ZMod 7) * β ≠ 1 ∧
          (basInv (false, 5, β, μ) *
              blk (psi (false, 5, β, μ) * (!![1, 0, 0; 0, 1, 0; 0, 0, 6] : M3) *
                psiInv (false, 5, β, μ)) *
              bas (false, 5, β, μ)) * a8P p₁ p₂ u₀ u₁ u₂ =
            a8P p₁ p₂ u₀ u₁ u₂ * a8SignThree) ∨
        (∃ μ : ZMod 7, μ ≠ 0 ∧ (5 : ZMod 7) ≠ 0 ∧
          (basInfInv 5 *
              blk (psi (false, 0, 0, μ) * (!![1, 0, 0; 0, 1, 0; 0, 0, 6] : M3) *
                psiInv (false, 0, 0, μ)) *
              basInf 5) * a8P p₁ p₂ u₀ u₁ u₂ =
            a8P p₁ p₂ u₀ u₁ u₂ * a8SignThree) := by
  intro p₁ p₂ u₀ u₁ u₂ ⟨hx, hdet⟩
  obtain ⟨rfl, rfl⟩ := a8bf_solve hx
  exact (a8bf_match_key 5 p₁ p₂ u₂ hdet).imp (fun ⟨β, _, μ, _, h⟩ => ⟨β, μ, h⟩)
    fun ⟨μ, _, h⟩ => ⟨μ, h⟩

private lemma a8bf_match_aux6 :
    ∀ p₁ p₂ u₀ u₁ u₂ : ZMod 7,
      (vecMul ![6, 1, 1, 1] (a8P p₁ p₂ u₀ u₁ u₂) = Pi.single 0 1 ∧
       (a8P p₁ p₂ u₀ u₁ u₂).det ≠ 0) →
      (∃ β μ : ZMod 7, μ ≠ 0 ∧ (6 : ZMod 7) * β ≠ 1 ∧
          (basInv (false, 6, β, μ) *
              blk (psi (false, 6, β, μ) * (!![1, 0, 0; 0, 1, 0; 0, 0, 6] : M3) *
                psiInv (false, 6, β, μ)) *
              bas (false, 6, β, μ)) * a8P p₁ p₂ u₀ u₁ u₂ =
            a8P p₁ p₂ u₀ u₁ u₂ * a8SignThree) ∨
        (∃ μ : ZMod 7, μ ≠ 0 ∧ (6 : ZMod 7) ≠ 0 ∧
          (basInfInv 6 *
              blk (psi (false, 0, 0, μ) * (!![1, 0, 0; 0, 1, 0; 0, 0, 6] : M3) *
                psiInv (false, 0, 0, μ)) *
              basInf 6) * a8P p₁ p₂ u₀ u₁ u₂ =
            a8P p₁ p₂ u₀ u₁ u₂ * a8SignThree) := by
  intro p₁ p₂ u₀ u₁ u₂ ⟨hx, hdet⟩
  obtain ⟨rfl, rfl⟩ := a8bf_solve hx
  exact (a8bf_match_key 6 p₁ p₂ u₂ hdet).imp (fun ⟨β, _, μ, _, h⟩ => ⟨β, μ, h⟩)
    fun ⟨μ, _, h⟩ => ⟨μ, h⟩

theorem a8B_match {a p₁ p₂ u₀ u₁ u₂ : ZMod 7}
    (hx : vecMul ![a, 1, 1, 1] (a8P p₁ p₂ u₀ u₁ u₂) = Pi.single 0 1)
    (hdet : (a8P p₁ p₂ u₀ u₁ u₂).det ≠ 0) :
    (∃ β μ : ZMod 7, μ ≠ 0 ∧ a * β ≠ 1 ∧
        genL (false, a, β, μ) 2 * a8P p₁ p₂ u₀ u₁ u₂ = a8P p₁ p₂ u₀ u₁ u₂ * a8SignThree) ∨
      (∃ μ : ZMod 7, μ ≠ 0 ∧ a ≠ 0 ∧
        genLInfB a μ 2 * a8P p₁ p₂ u₀ u₁ u₂ = a8P p₁ p₂ u₀ u₁ u₂ * a8SignThree) := by
  rcases a8bf_zmod7_cases a with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · simpa [a8bf_genL2_inline_eq, a8bf_genLInfB2_inline_eq] using
      a8bf_match_aux0 p₁ p₂ u₀ u₁ u₂ ⟨hx, hdet⟩
  · simpa [a8bf_genL2_inline_eq, a8bf_genLInfB2_inline_eq] using
      a8bf_match_aux1 p₁ p₂ u₀ u₁ u₂ ⟨hx, hdet⟩
  · simpa [a8bf_genL2_inline_eq, a8bf_genLInfB2_inline_eq] using
      a8bf_match_aux2 p₁ p₂ u₀ u₁ u₂ ⟨hx, hdet⟩
  · simpa [a8bf_genL2_inline_eq, a8bf_genLInfB2_inline_eq] using
      a8bf_match_aux3 p₁ p₂ u₀ u₁ u₂ ⟨hx, hdet⟩
  · simpa [a8bf_genL2_inline_eq, a8bf_genLInfB2_inline_eq] using
      a8bf_match_aux4 p₁ p₂ u₀ u₁ u₂ ⟨hx, hdet⟩
  · simpa [a8bf_genL2_inline_eq, a8bf_genLInfB2_inline_eq] using
      a8bf_match_aux5 p₁ p₂ u₀ u₁ u₂ ⟨hx, hdet⟩
  · simpa [a8bf_genL2_inline_eq, a8bf_genLInfB2_inline_eq] using
      a8bf_match_aux6 p₁ p₂ u₀ u₁ u₂ ⟨hx, hdet⟩

end CFSG.StandardType.A8Coord

end