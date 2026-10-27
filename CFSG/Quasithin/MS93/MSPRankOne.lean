module

public import CFSG.Quasithin.MS93.MSPLeviQ

public section

namespace CFSG.Quasithin.MS93.MSP

open Matrix CFSG.Assembly.LowTwoRank CFSG.LocalAnalysis.ComponentInitial
open CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag

variable {F : Type} [Field F]

section CharTwo

variable [CharP F 2]

theorem qe_conj_of_fix {k : Sp4 F} (hk : mat k *ᵥ e₁ F = e₁ F) (x y s : F) :
    k * qe x y s * k⁻¹ = qe (levMat k 0 0 * x + levMat k 0 1 * y)
      (levMat k 1 0 * x + levMat k 1 1 * y) s := by
  rw [qe, qw_conj hk (by simp)]
  have h0 : mat k (.inr 0) (.inl 1) = 0 := by
    rw [mat_apply_eq]; exact mulVec_inr_zero_of_fix hk (by simp)
  have h1 : mat k (.inr 0) (.inr 1) = 0 := by
    rw [mat_apply_eq]; exact mulVec_inr_zero_of_fix hk (by simp)
  have hv : mat k *ᵥ (x • e₂ F + y • f₂ F) =
      ((levMat k 0 0 * x + levMat k 0 1 * y) • e₂ F + (levMat k 1 0 * x + levMat k 1 1 * y) •
        f₂ F) + ((mat k *ᵥ (x • e₂ F + y • f₂ F)) (.inl 0)) • e₁ F := by
    refine ext4 ?_ ?_ ?_ ?_
    · simp
    · simp [levMat, mulVec_add, mulVec_smul]
      ring
    · simp [mulVec_add, mulVec_smul, h0, h1]
    · simp [levMat, mulVec_add, mulVec_smul]
      ring
  rw [hv, qw_add_e₁ (by simp)]
  rfl

theorem Q₂_le_of_qe_mem {H : Subgroup (Sp4 F)} (hq : ∃ l : F, l ≠ 0 ∧ l ≠ 1) {β s₀ c : F}
    (hβ : β ≠ 0) (hc : c ≠ 0) (h₀ : qe β 0 s₀ ∈ H)
    (hconjE : ∀ a x y s, qe x y s ∈ H → qe (x + a * y) y s ∈ H)
    (hconjt : ∀ x y s, qe x y s ∈ H → qe x (y + c * x) s ∈ H) : Q₂ F ≤ H := by
  have hcβ : c * β ≠ 0 := mul_ne_zero hc hβ
  have hmul : ∀ x y s x' y' s', qe x y s ∈ H → qe x' y' s' ∈ H →
      qe (x + x') (y + y') (s + s' + x * y' + x' * y) ∈ H := fun x y s x' y' s' h h' => by
    rw [← qe_mul]
    exact mul_mem h h'
  have hA : qe 0 (c * β) (c * β ^ 2) ∈ H := by
    have := hmul _ _ _ _ _ _ h₀ (hconjt _ _ _ h₀)
    convert this using 1
    clear hconjE hconjt hmul this h₀
    refine qe_congr ?_ ?_ ?_ <;> grind
  have hB : ∀ x, qe x 0 (x * c * β) ∈ H := by
    intro x
    have := hmul _ _ _ _ _ _ hA (hconjE (x / (c * β)) _ _ _ hA)
    convert this using 1
    have hx : x / (c * β) * (c * β) = x := div_mul_cancel₀ x hcβ
    clear hconjE hconjt hmul this hA h₀
    rw [hx]
    refine qe_congr ?_ ?_ ?_ <;> grind
  have hC : ∀ y, qe 0 y (y ^ 2 / c) ∈ H := by
    intro y
    have h1 := hB (y / c)
    have := hmul _ _ _ _ _ _ h1 (hconjt _ _ _ h1)
    convert this using 1
    have hy : c * (y / c) = y := mul_div_cancel₀ y hc
    have hy2 : y / c * c * β * (y / c * c * β) = y ^ 2 / c * (c * β ^ 2) := by
      field_simp
    clear hconjE hconjt hmul this hA h₀ hB h1
    refine qe_congr ?_ ?_ ?_
    · grind
    · rw [hy]; ring
    · rw [hy]
      field_simp
      grind
  have hD : ∀ a y, transv (e₁ F) (a * y * (c * β + y)) ∈ H := by
    intro a y
    have h1 := hconjE a _ _ _ (hC y)
    have h2 := hmul _ _ _ _ _ _ (hB (a * y)) (hC y)
    have := hmul _ _ _ _ _ _ h1 h2
    rw [← qe_zero_zero]
    convert this using 1
    clear hconjE hconjt hmul this hA h₀ hB hC h1 h2
    refine qe_congr ?_ ?_ ?_ <;> grind
  obtain ⟨l, hl0, hl1⟩ := hq
  have hy0 : l * (c * β) * (c * β + l * (c * β)) ≠ 0 := by
    have hl1' : 1 + l ≠ 0 := fun h => hl1 (by grind)
    have : l * (c * β) * (c * β + l * (c * β)) = l * (1 + l) * (c * β) ^ 2 := by ring
    rw [this]
    exact mul_ne_zero (mul_ne_zero hl0 hl1') (pow_ne_zero 2 hcβ)
  have hX : ∀ r : F, transv (e₁ F) r ∈ H := fun r => by
    have := hD (r / (l * (c * β) * (c * β + l * (c * β)))) (l * (c * β))
    rwa [mul_assoc, div_mul_cancel₀ _ hy0] at this
  intro g hg
  obtain ⟨x, y, s, rfl⟩ := exists_eq_qe_of_mem_Q₂ hg
  have h1 := hmul _ _ _ _ _ _ (hB x) (hC y)
  have h2 := hmul _ _ _ _ _ _ h1 (show qe 0 0 (s - (x * c * β + y ^ 2 / c + x * y)) ∈ H by
    rw [qe_zero_zero]
    exact hX _)
  convert h2 using 1
  refine qe_congr ?_ ?_ ?_ <;> ring

@[expose] def sl2Up (a : F) : Matrix.SpecialLinearGroup (Fin 2) F :=
  ⟨!![1, a; 0, 1], by simp [det_fin_two]⟩

@[expose] def sl2Low (c : F) : Matrix.SpecialLinearGroup (Fin 2) F :=
  ⟨!![1, 0; c, 1], by simp [det_fin_two]⟩

end CharTwo

end CFSG.Quasithin.MS93.MSP
