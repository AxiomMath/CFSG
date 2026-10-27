module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.TenFive.Invol.MatrixHeis
import CFSG.HardMathSupport.Lang.UnitaryAutomorphisms.LinFrame

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.TenFive.Three

open Matrix
open CFSG.GH74.GLS.IVK.Proofs2.Lemma41dL3 (Heis)
open CFSG.LocalAnalysis.ComponentInitial.LinearFlag (projectiveSL proj)

variable {K : Type} [Field K] {n : ℕ}

private theorem exists_pairing_vectors {w₁ w₂ φ₁ φ₂ : Fin n → K}
    (hw : LinearIndependent K ![w₁, w₂]) (hφ : LinearIndependent K ![φ₁, φ₂])
    (h11 : φ₁ ⬝ᵥ w₁ = 0) (h12 : φ₁ ⬝ᵥ w₂ = 0) :
    ∃ v₁ χ : Fin n → K, φ₁ ⬝ᵥ v₁ = 1 ∧ φ₂ ⬝ᵥ v₁ = 0 ∧ χ ⬝ᵥ w₁ = 0 ∧ χ ⬝ᵥ w₂ = 1 ∧
      χ ⬝ᵥ v₁ = 0 := by
  classical
  obtain ⟨v₁, hv₁⟩ :=
    CFSG.HardMathSupport.Lang.UnitaryAutomorphisms.exists_dotProduct_eq ![φ₁, φ₂] hφ ![1, 0]
  have hφ₁v₁ : φ₁ ⬝ᵥ v₁ = 1 := by
    rw [dotProduct_comm]
    simpa using hv₁ 0
  have hφ₂v₁ : φ₂ ⬝ᵥ v₁ = 0 := by
    rw [dotProduct_comm]
    simpa using hv₁ 1
  have hwv : LinearIndependent K ![w₁, w₂, v₁] := by
    rw [Fintype.linearIndependent_iff]
    intro g hg
    have hsum : g 0 • w₁ + g 1 • w₂ + g 2 • v₁ = 0 := by
      simpa [Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one,
        Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons] using hg
    have hg2 : g 2 = 0 := by
      have h : φ₁ ⬝ᵥ (g 0 • w₁ + g 1 • w₂ + g 2 • v₁) = 0 := by
        simp [hsum]
      simpa [dotProduct_add, dotProduct_smul, smul_eq_mul, h11, h12, hφ₁v₁] using h
    have hpair : g 0 • w₁ + g 1 • w₂ = 0 := by
      simpa [hg2] using hsum
    obtain ⟨hg0, hg1⟩ := LinearIndependent.pair_iff.mp hw (g 0) (g 1) hpair
    intro i
    fin_cases i
    · exact hg0
    · exact hg1
    · exact hg2
  obtain ⟨χ, hχ⟩ :=
    CFSG.HardMathSupport.Lang.UnitaryAutomorphisms.exists_dotProduct_eq ![w₁, w₂, v₁] hwv
      ![0, 1, 0]
  exact ⟨v₁, χ, hφ₁v₁, hφ₂v₁, by simpa using hχ 0, by simpa using hχ 1, by simpa using hχ 2⟩

private theorem vecMulVec_heis_facts {w₁ w₂ v₁ φ₁ φ₂ χ : Fin n → K}
    (h11 : φ₁ ⬝ᵥ w₁ = 0) (h12 : φ₁ ⬝ᵥ w₂ = 0) (h21 : φ₂ ⬝ᵥ w₁ = 0)
    (h22 : φ₂ ⬝ᵥ w₂ = 0) (hφ₁v₁ : φ₁ ⬝ᵥ v₁ = 1) (hφ₂v₁ : φ₂ ⬝ᵥ v₁ = 0)
    (hχw₁ : χ ⬝ᵥ w₁ = 0) (hχw₂ : χ ⬝ᵥ w₂ = 1) :
    vecMulVec w₁ φ₁ * vecMulVec w₁ φ₁ = 0 ∧
      vecMulVec v₁ φ₂ * vecMulVec v₁ φ₂ = 0 ∧
      vecMulVec v₁ φ₂ * vecMulVec w₁ φ₁ = 0 ∧
      vecMulVec w₁ φ₁ * vecMulVec v₁ φ₂ = vecMulVec w₁ φ₂ ∧
      vecMulVec w₁ χ * vecMulVec w₁ χ = 0 ∧
      vecMulVec w₂ φ₂ * vecMulVec w₂ φ₂ = 0 ∧
      vecMulVec w₂ φ₂ * vecMulVec w₁ χ = 0 ∧
      vecMulVec w₁ χ * vecMulVec w₂ φ₂ = vecMulVec w₁ φ₂ ∧
      vecMulVec w₁ φ₁ * vecMulVec w₂ φ₂ = 0 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    simp [Matrix.vecMulVec_mul_vecMulVec, Matrix.vecMulVec_zero, h11, h12, h21, h22,
      hφ₁v₁, hφ₂v₁, hχw₁, hχw₂]

private theorem vecMulVec_cross_facts {w₁ w₂ v₁ φ₁ φ₂ χ : Fin n → K}
    (h11 : φ₁ ⬝ᵥ w₁ = 0) (h12 : φ₁ ⬝ᵥ w₂ = 0) (h21 : φ₂ ⬝ᵥ w₁ = 0)
    (h22 : φ₂ ⬝ᵥ w₂ = 0) (hφ₂v₁ : φ₂ ⬝ᵥ v₁ = 0) (hχw₁ : χ ⬝ᵥ w₁ = 0)
    (hχv₁ : χ ⬝ᵥ v₁ = 0) :
    (∀ i j : Fin 3, (![vecMulVec w₁ φ₁, vecMulVec v₁ φ₂, vecMulVec w₁ φ₂] :
        Fin 3 → Matrix (Fin n) (Fin n) K) i *
      (![vecMulVec w₁ χ, vecMulVec w₂ φ₂, vecMulVec w₁ φ₂] :
        Fin 3 → Matrix (Fin n) (Fin n) K) j = 0) ∧
    (∀ i j : Fin 3, (![vecMulVec w₁ χ, vecMulVec w₂ φ₂, vecMulVec w₁ φ₂] :
        Fin 3 → Matrix (Fin n) (Fin n) K) i *
      (![vecMulVec w₁ φ₁, vecMulVec v₁ φ₂, vecMulVec w₁ φ₂] :
        Fin 3 → Matrix (Fin n) (Fin n) K) j = 0) := by
  constructor
  · intro i j
    fin_cases i <;> fin_cases j <;>
      simp [Matrix.vecMulVec_mul_vecMulVec, Matrix.vecMulVec_zero, h11, h12, h21, h22]
  · intro i j
    fin_cases i <;> fin_cases j <;>
      simp [Matrix.vecMulVec_mul_vecMulVec, Matrix.vecMulVec_zero, h21, hφ₂v₁, hχw₁, hχv₁]

private theorem fin3_linComb_mul_linComb_eq_zero {A B : Fin 3 → Matrix (Fin n) (Fin n) K}
    (h : ∀ i j, A i * B j = 0) (c d : Fin 3 → K) :
    (∑ i, c i • A i) * (∑ j, d j • B j) = 0 := by
  rw [Fintype.sum_mul_sum]
  refine Finset.sum_eq_zero fun i _ => Finset.sum_eq_zero fun j _ => ?_
  rw [Matrix.smul_mul, Matrix.mul_smul, h i j]
  simp

theorem exists_heis_pair_projectiveSL {w₁ w₂ φ₁ φ₂ : Fin n → K}
    (hw : LinearIndependent K ![w₁, w₂]) (hφ : LinearIndependent K ![φ₁, φ₂])
    (h11 : φ₁ ⬝ᵥ w₁ = 0) (h12 : φ₁ ⬝ᵥ w₂ = 0) (h21 : φ₂ ⬝ᵥ w₁ = 0) (h22 : φ₂ ⬝ᵥ w₂ = 0) :
    ∃ ι₁ ι₂ : Heis K →* projectiveSL n K, Function.Injective ι₁ ∧ Function.Injective ι₂ ∧
      (∀ x y, Commute (ι₁ x) (ι₂ y)) ∧ (∀ c : K, ι₁ ⟨0, 0, c⟩ = ι₂ ⟨0, 0, c⟩) ∧
      ∀ (a b : K) (N : Matrix (Fin n) (Fin n) K) (hN2 : N * N = 0),
        N = a • vecMulVec w₁ φ₁ + b • vecMulVec w₂ φ₂ →
          proj n K (unipSL N hN2) ∈ ι₁.range ⊔ ι₂.range := by
  classical
  obtain ⟨v₁, χ, hφ₁v₁, hφ₂v₁, hχw₁, hχw₂, hχv₁⟩ := exists_pairing_vectors hw hφ h11 h12
  let N₁ : Matrix (Fin n) (Fin n) K := vecMulVec w₁ φ₁
  let N₂ : Matrix (Fin n) (Fin n) K := vecMulVec v₁ φ₂
  let N₃ : Matrix (Fin n) (Fin n) K := vecMulVec w₁ χ
  let N₄ : Matrix (Fin n) (Fin n) K := vecMulVec w₂ φ₂
  let P : Matrix (Fin n) (Fin n) K := vecMulVec w₁ φ₂
  obtain ⟨h11', h22', h21', h12', h33', h44', h43', h34', h14'⟩ :=
    vecMulVec_heis_facts h11 h12 h21 h22 hφ₁v₁ hφ₂v₁ hχw₁ hχw₂
  obtain ⟨hAB, hBA⟩ := vecMulVec_cross_facts h11 h12 h21 h22 hφ₂v₁ hχw₁ hχv₁
  have hsq1 : N₁ * N₁ = 0 := h11'
  have hsq2 : N₂ * N₂ = 0 := h22'
  have hsq21 : N₂ * N₁ = 0 := h21'
  have hprod1 : N₁ * N₂ = P := h12'
  have hsq3 : N₃ * N₃ = 0 := h33'
  have hsq4 : N₄ * N₄ = 0 := h44'
  have hsq43 : N₄ * N₃ = 0 := h43'
  have hprod2 : N₃ * N₄ = P := h34'
  have h14 : N₁ * N₄ = 0 := h14'
  have hAB' : ∀ i j : Fin 3, (![N₁, N₂, P] : Fin 3 → Matrix (Fin n) (Fin n) K) i *
      (![N₃, N₄, P] : Fin 3 → Matrix (Fin n) (Fin n) K) j = 0 := hAB
  have hBA' : ∀ i j : Fin 3, (![N₃, N₄, P] : Fin 3 → Matrix (Fin n) (Fin n) K) i *
      (![N₁, N₂, P] : Fin 3 → Matrix (Fin n) (Fin n) K) j = 0 := hBA
  have hw₁0 : w₁ ≠ 0 := by
    have h := hw.ne_zero 0
    simpa using h
  have hφ₂0 : φ₂ ≠ 0 := by
    have h := hφ.ne_zero 1
    simpa using h
  have hPne : P ≠ 0 := Matrix.vecMulVec_ne_zero hw₁0 hφ₂0
  have hPne1 : N₁ * N₂ ≠ 0 := by
    rw [hprod1]
    exact hPne
  have hPne2 : N₃ * N₄ ≠ 0 := by
    rw [hprod2]
    exact hPne
  obtain ⟨φ, hφmat, hφinj⟩ := exists_heisSL N₁ N₂ hsq1 hsq2 hsq21
  obtain ⟨ψ, hψmat, hψinj⟩ := exists_heisSL N₃ N₄ hsq3 hsq4 hsq43
  have hφP : ∀ x : Heis K, (φ x : Matrix (Fin n) (Fin n) K) =
      1 + (x.a • N₁ + x.b • N₂ + x.c • P) := by
    intro x
    rw [hφmat x, hprod1]
  have hψP : ∀ y : Heis K, (ψ y : Matrix (Fin n) (Fin n) K) =
      1 + (y.a • N₃ + y.b • N₄ + y.c • P) := by
    intro y
    rw [hψmat y, hprod2]
  have hX : ∀ x : Heis K, x.a • N₁ + x.b • N₂ + x.c • P =
      ∑ i, (![x.a, x.b, x.c] : Fin 3 → K) i • ![N₁, N₂, P] i := by
    intro x
    rw [Fin.sum_univ_three]
    simp
  have hY : ∀ y : Heis K, y.a • N₃ + y.b • N₄ + y.c • P =
      ∑ i, (![y.a, y.b, y.c] : Fin 3 → K) i • ![N₃, N₄, P] i := by
    intro y
    rw [Fin.sum_univ_three]
    simp
  have hmul : ∀ x y : Heis K,
      (x.a • N₁ + x.b • N₂ + x.c • P) * (y.a • N₃ + y.b • N₄ + y.c • P) = 0 := by
    intro x y
    rw [hX x, hY y]
    exact fin3_linComb_mul_linComb_eq_zero hAB' _ _
  have hmul' : ∀ x y : Heis K,
      (y.a • N₃ + y.b • N₄ + y.c • P) * (x.a • N₁ + x.b • N₂ + x.c • P) = 0 := by
    intro x y
    rw [hX x, hY y]
    exact fin3_linComb_mul_linComb_eq_zero hBA' _ _
  have hcomm : ∀ x y : Heis K, φ x * ψ y = ψ y * φ x := by
    intro x y
    let X : Matrix (Fin n) (Fin n) K := x.a • N₁ + x.b • N₂ + x.c • P
    let Y : Matrix (Fin n) (Fin n) K := y.a • N₃ + y.b • N₄ + y.c • P
    have hXY : X * Y = 0 := hmul x y
    have hYX : Y * X = 0 := hmul' x y
    have h1 : (1 + X) * (1 + Y) = 1 + X + Y := by
      rw [Matrix.mul_add, Matrix.mul_one, Matrix.add_mul, Matrix.one_mul, hXY, add_zero]
    have h2 : (1 + Y) * (1 + X) = 1 + Y + X := by
      rw [Matrix.mul_add, Matrix.mul_one, Matrix.add_mul, Matrix.one_mul, hYX, add_zero]
    apply Subtype.ext
    rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul, hφP x, hψP y]
    change (1 + X) * (1 + Y) = (1 + Y) * (1 + X)
    rw [h1, h2]
    abel
  refine ⟨(proj n K).comp φ, (proj n K).comp ψ, hφinj hPne1, hψinj hPne2, ?_, ?_, ?_⟩
  · intro x y
    simpa only [MonoidHom.comp_apply] using
      Commute.map ((commute_iff_eq (φ x) (ψ y)).mpr (hcomm x y)) (proj n K)
  · intro c
    have hcen : φ ⟨0, 0, c⟩ = ψ ⟨0, 0, c⟩ := by
      apply Subtype.ext
      rw [hφP, hψP]
      simp
    show proj n K (φ ⟨0, 0, c⟩) = proj n K (ψ ⟨0, 0, c⟩)
    rw [hcen]
  · intro a b N hN2 hN
    have hNdef : N = a • N₁ + b • N₄ := by
      rw [hN]
    have hmat : (1 : Matrix (Fin n) (Fin n) K) + (a • N₁ + b • N₄) =
        (1 + a • N₁) * (1 + b • N₄) := by
      simp only [Matrix.add_mul, Matrix.mul_add, Matrix.one_mul, Matrix.mul_one,
        Matrix.smul_mul, Matrix.mul_smul, h14, smul_zero, add_zero]
      abel
    have hunip : unipSL N hN2 = φ ⟨a, 0, 0⟩ * ψ ⟨0, b, 0⟩ := by
      apply Subtype.ext
      rw [coe_unipSL, Matrix.SpecialLinearGroup.coe_mul, hφP, hψP, hNdef]
      simpa only [zero_smul, zero_add, add_zero] using hmat
    rw [hunip, map_mul]
    exact Subgroup.mul_mem_sup ⟨⟨a, 0, 0⟩, rfl⟩ ⟨⟨0, b, 0⟩, rfl⟩

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.TenFive.Three
