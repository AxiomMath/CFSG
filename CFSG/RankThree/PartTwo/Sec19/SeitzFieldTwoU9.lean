module

public import CFSG.RankThree.PartTwo.Sec19.Item19Res6ProofSeitz

public section

namespace CFSG.RankThree.PartTwo.Sec19

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo
open Matrix CFSG.LocalAnalysis.ComponentInitial CFSG.ClassicalGroups.UnitaryFlag
open CFSG.RankThree.PartTwo.KFacts
open CFSG.GH74.GLS.IVK (fixedField mem_fixedField_iff fixedField_apply)
open Item19Res6Proof

variable {K : Type} [Field K]

theorem closure_fixSet_eq_top_of_field_gen {p f : ℕ}
    (h : UnitaryFieldData p f K) (hQ : p ^ f % 3 = 2) (hq : 2 < p ^ f) (hQ8 : p ^ f ≠ 8)
    (D : Subgroup (MulAut (unitarySU p f K 3))) (hD3 : ∀ φ ∈ D, φ ^ 3 = 1)
    {φ : MulAut (unitarySU p f K 3)} (hφD : φ ∈ D) (hφ : φ ∉ (suConj h).range)
    {y : MulAut (unitarySU p f K 3)} (hyD : y ∈ D) (hy1 : y ≠ 1)
    (hy : y ∈ (suConj h).range) :
    Subgroup.closure (CFSG.LocalAnalysis.RankThreeTheoremC.SL3CoverGen.fixSet D) = ⊤ := by
  classical
  have := h.finite
  obtain ⟨B, hB⟩ := hy
  obtain ⟨ψ, hψdef⟩ : ∃ ψ : MulAut (unitarySU p f K 3), ψ = φ * y := ⟨_, rfl⟩
  have hψD : ψ ∈ D := hψdef ▸ D.mul_mem hφD hyD
  have hψ : ψ ∉ (suConj h).range := by
    rintro ⟨C, hC⟩
    apply hφ
    refine ⟨C * B⁻¹, ?_⟩
    rw [map_mul, map_inv, hB, hC, hψdef, mul_inv_cancel_right]
  obtain ⟨σ, hσ, H, hφH⟩ := eq_conj_suField_of_not_mem hq (hD3 φ hφD) hφ
  have hσ3 : σ ^ 3 = 1 := by rw [← hσ]; exact pow_orderOf_eq_one σ
  obtain ⟨σ', hσ', H', hψH'⟩ := eq_conj_suField_of_not_mem hq (hD3 ψ hψD) hψ
  obtain ⟨e₀, hfe, he₀, hkcard⟩ := exists_card_fixedField_of_orderOf_eq_three h hσ
  have h₀ : UnitaryFieldData p e₀ (fixedField σ) := ⟨h.prime, he₀, hkcard⟩
  have hbar := bar_coe_fixedField h hfe h₀
  have hk : ∀ x, x ∈ fixedField σ ↔ σ x = x := mem_fixedField_iff σ
  have hk' : ∀ x, x ∈ fixedField σ ↔ σ' x = x := by
    intro x
    rw [hk]
    rcases Sec14.Item148Rank.ringAut_eq_or_mul_eq_one148 h.prime (by have := h.one_le; omega)
      h.card hσ hσ' with h1 | h1
    · rw [h1]
    · have h2 : σ' = σ⁻¹ := eq_inv_of_mul_eq_one_left h1
      have hinv : ∀ y, σ⁻¹ (σ y) = y := fun y => by simp
      have hinv' : ∀ y, σ (σ⁻¹ y) = y := fun y => by simp
      rw [h2]
      constructor
      · intro hx
        calc σ⁻¹ x = σ⁻¹ (σ x) := by rw [hx]
          _ = x := hinv x
      · intro hx
        calc σ x = σ (σ⁻¹ x) := by rw [hx]
          _ = x := hinv' x
  have hq0 : p ^ e₀ ≠ 2 := by
    intro h2
    apply hQ8
    rw [hfe, pow_mul', h2]
    norm_num
  have hφ1 : φ ≠ 1 := fun h1 => hφ ⟨1, by rw [map_one, h1]⟩
  have hψ1 : ψ ≠ 1 := fun h1 => hψ ⟨1, by rw [map_one, h1]⟩
  have hY : ∀ g : unitarySU p f K 3,
      (∀ i j, ((g : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) i j ∈ fixedField σ) →
        suConj h H g ∈ Subgroup.closure
          (CFSG.LocalAnalysis.RankThreeTheoremC.SL3CoverGen.fixSet D) := by
    intro g hg
    refine Subgroup.subset_closure ⟨φ, hφD, hφ1, ?_⟩
    rw [hφH]
    exact conj_suField_fix H σ g fun i j => (hk _).1 (hg i j)
  have hY' : ∀ g : unitarySU p f K 3,
      (∀ i j, ((g : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) i j ∈ fixedField σ) →
        suConj h H' g ∈ Subgroup.closure
          (CFSG.LocalAnalysis.RankThreeTheoremC.SL3CoverGen.fixSet D) := by
    intro g hg
    refine Subgroup.subset_closure ⟨ψ, hψD, hψ1, ?_⟩
    rw [hψH']
    exact conj_suField_fix H' σ' g fun i j => (hk' _).1 (hg i j)
  refine eq_top_of_two_conj_su h h₀ hbar hfe hq0 H H' hY hY' ?_
  intro hall
  apply hy1
  have hcomm : ∀ g : unitarySU p f K 3,
      (∀ i j, ((g : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) i j ∈ fixedField σ) →
        (B : GL (Fin 3) K) * ((H : GL (Fin 3) K) * (g : GL (Fin 3) K) * (H : GL (Fin 3) K)⁻¹) =
          ((H : GL (Fin 3) K) * (g : GL (Fin 3) K) * (H : GL (Fin 3) K)⁻¹) * (B : GL (Fin 3) K) := by
    intro g hg
    have hx1 : φ (suConj h H g) = suConj h H g := by
      rw [hφH]
      exact conj_suField_fix H σ g fun i j => (hk _).1 (hg i j)
    have hxH' : suConj h H g = suConj h H' (suConj h (H'⁻¹ * H) g) := by
      rw [← MulAut.mul_apply, ← map_mul, mul_inv_cancel_left]
    have hx2 : ψ (suConj h H g) = suConj h H g := by
      rw [hxH', hψH']
      exact conj_suField_fix H' σ' _ fun i j => (hk' _).1 (hall g hg i j)
    have h3 : y (suConj h H g) = suConj h H g := by
      have h4 : φ (y (suConj h H g)) = φ (suConj h H g) := by
        rw [hx1]
        rw [hψdef, MulAut.mul_apply] at hx2
        exact hx2
      exact φ.injective h4
    rw [← hB] at h3
    have h5 := congrArg (fun x : unitarySU p f K 3 => ((x : unitarySU p f K 3) : GL (Fin 3) K)) h3
    simp only [coe_suConj, Subgroup.coe_mul, Subgroup.coe_inv] at h5
    calc (B : GL (Fin 3) K) * ((H : GL (Fin 3) K) * (g : GL (Fin 3) K) * (H : GL (Fin 3) K)⁻¹)
        = (B : GL (Fin 3) K) * ((H : GL (Fin 3) K) * (g : GL (Fin 3) K) * (H : GL (Fin 3) K)⁻¹) *
            (B : GL (Fin 3) K)⁻¹ * (B : GL (Fin 3) K) := by group
      _ = ((H : GL (Fin 3) K) * (g : GL (Fin 3) K) * (H : GL (Fin 3) K)⁻¹) * (B : GL (Fin 3) K) := by
          rw [h5]
  set M : Matrix (Fin 3) (Fin 3) K := (((H : GL (Fin 3) K)⁻¹ * (B : GL (Fin 3) K) *
    (H : GL (Fin 3) K) : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) with hM
  have hMcomm : ∀ g : unitarySU p f K 3,
      (∀ i j, ((g : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) i j ∈ fixedField σ) →
        M * ((g : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) =
          ((g : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) * M := by
    intro g hg
    have h1 := hcomm g hg
    have h2 : ((H : GL (Fin 3) K)⁻¹ * (B : GL (Fin 3) K) * (H : GL (Fin 3) K)) *
        (g : GL (Fin 3) K) = (g : GL (Fin 3) K) *
          ((H : GL (Fin 3) K)⁻¹ * (B : GL (Fin 3) K) * (H : GL (Fin 3) K)) := by
      calc ((H : GL (Fin 3) K)⁻¹ * (B : GL (Fin 3) K) * (H : GL (Fin 3) K)) * (g : GL (Fin 3) K)
          = (H : GL (Fin 3) K)⁻¹ * ((B : GL (Fin 3) K) * ((H : GL (Fin 3) K) *
            (g : GL (Fin 3) K) * (H : GL (Fin 3) K)⁻¹)) * (H : GL (Fin 3) K) := by group
        _ = (H : GL (Fin 3) K)⁻¹ * (((H : GL (Fin 3) K) * (g : GL (Fin 3) K) *
            (H : GL (Fin 3) K)⁻¹) * (B : GL (Fin 3) K)) * (H : GL (Fin 3) K) := by rw [h1]
        _ = (g : GL (Fin 3) K) * ((H : GL (Fin 3) K)⁻¹ * (B : GL (Fin 3) K) *
            (H : GL (Fin 3) K)) := by group
    have h3 := congrArg Units.val h2
    simp only [Units.val_mul] at h3
    rw [hM, Units.val_mul, Units.val_mul]
    exact h3
  have hK3 : 3 ∣ Nat.card K - 1 := by
    rw [h.card]
    have hpow : p ^ (2 * f) = (p ^ f) ^ 2 := by rw [pow_mul']
    rw [hpow]
    have h1 : (p ^ f) ^ 2 % 3 = 1 := by rw [Nat.pow_mod, hQ]
    have h2 : 1 ≤ (p ^ f) ^ 2 := Nat.one_le_pow _ _ (by omega)
    omega
  obtain ⟨ω, hω⟩ := Item19Res5Proof.exists_isPrimitiveRoot_three hK3
  have hω3 : ω ^ 3 = 1 := hω.pow_eq_one
  have hωk : ω ∈ fixedField σ := (hk ω).2 (ringEquiv_fix_of_cube hσ3 hω3)
  have hωN : h.norm ω = 1 := by
    rw [UnitaryFieldData.norm, bar_eq_of_cube h hQ hω3, ← pow_succ']
    exact hω3
  have hω2N : h.norm (ω ^ 2) = 1 := by
    rw [UnitaryFieldData.norm, map_pow, bar_eq_of_cube h hQ hω3, ← pow_mul, ← pow_add]
    calc ω ^ (2 + 2 * 2) = (ω ^ 3) ^ 2 := by ring
      _ = 1 := by rw [hω3, one_pow]
  obtain ⟨Dω, hDω⟩ := exists_diag_mem h ![ω, ω ^ 2, 1]
    (by
      intro i
      fin_cases i
      · exact hωN
      · exact hω2N
      · show h.norm 1 = 1
        simp [UnitaryFieldData.norm])
    (by
      show ω * ω ^ 2 * 1 = 1
      linear_combination hω3)
  have hDωk : ∀ i j, ((Dω : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) i j ∈ fixedField σ := by
    intro i j
    rw [hDω]
    by_cases hij : i = j
    · subst hij
      fin_cases i <;> simp [hωk, (fixedField σ).one_mem, (fixedField σ).pow_mem hωk]
    · rw [diagonal_apply_ne _ hij]
      exact (fixedField σ).zero_mem
  have hE : ∃ g : unitarySU p f K 3, ((g : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) =
      swapMat K := ⟨⟨swapGL K, swapGL_mem_unitarySU h⟩, rfl⟩
  have hE' : ∃ g : unitarySU p f K 3, ((g : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) =
      swapMat' K := ⟨⟨swapGL' K, swapGL'_mem_unitarySU h⟩, rfl⟩
  obtain ⟨gE, hgE⟩ := hE
  obtain ⟨gE', hgE'⟩ := hE'
  have h1 := hMcomm Dω hDωk
  have h2 := hMcomm gE (by rw [hgE]; exact swapMat_mem)
  have h3 := hMcomm gE' (by rw [hgE']; exact swapMat'_mem)
  rw [hDω] at h1
  rw [hgE] at h2
  rw [hgE'] at h3
  obtain ⟨c0, hMs⟩ : ∃ c0 : K, M = c0 • (1 : Matrix (Fin 3) (Fin 3) K) :=
    ⟨_, eq_smul_one_of_commute M hω h1 h2 h3⟩
  have hBm : ((B : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) = c0 • 1 := by
    have e1 : (B : GL (Fin 3) K) = (H : GL (Fin 3) K) * ((H : GL (Fin 3) K)⁻¹ *
        (B : GL (Fin 3) K) * (H : GL (Fin 3) K)) * (H : GL (Fin 3) K)⁻¹ := by group
    rw [e1, Units.val_mul, Units.val_mul, ← hM, hMs, Matrix.mul_smul, Matrix.mul_one,
      Matrix.smul_mul, Units.mul_inv]
  have hBcomm : ∀ X : GL (Fin 3) K, (B : GL (Fin 3) K) * X = X * (B : GL (Fin 3) K) := by
    intro X
    apply Units.ext
    rw [Units.val_mul, Units.val_mul, hBm, Matrix.smul_mul, Matrix.one_mul, Matrix.mul_smul,
      Matrix.mul_one]
  have hB1 : suConj h B = 1 := by
    refine MulEquiv.ext (fun x => ?_)
    apply Subtype.ext
    rw [MulAut.one_apply, coe_suConj, Subgroup.coe_inv, hBcomm, mul_inv_cancel_right]
  rw [← hB]
  exact hB1

end CFSG.RankThree.PartTwo.Sec19
