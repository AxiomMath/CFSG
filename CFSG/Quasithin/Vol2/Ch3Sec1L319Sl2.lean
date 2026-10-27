module

public import CFSG.LinearAlgebra.SL2MinimalFaithfulMatrix
public import Mathlib.Order.CompletePartialOrder

public section

namespace CFSG.Quasithin.H13.L319

open Matrix CFSG.SL2MinimalFaithful

private def wElt (K : Type) [Field K] : SpecialLinearGroup (Fin 2) K :=
  ⟨!![0, 1; -1, 0], by simp [Matrix.det_fin_two]⟩

private def lElt (K : Type) [Field K] : SpecialLinearGroup (Fin 2) K :=
  ⟨!![1, 0; 1, 1], by simp [Matrix.det_fin_two]⟩

private theorem coe_wElt (K : Type) [Field K] :
    ((wElt K : SpecialLinearGroup (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) = !![0, 1; -1, 0] :=
  rfl

private theorem coe_lElt (K : Type) [Field K] :
    ((lElt K : SpecialLinearGroup (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) = !![1, 0; 1, 1] :=
  rfl

private theorem lower_left_eq_zero {K : Type} [Field K] (z : SpecialLinearGroup (Fin 2) K)
    {r : K} (h : z * unipotent (1 : K) * z⁻¹ = unipotent r) :
    (z : Matrix (Fin 2) (Fin 2) K) 1 0 = 0 := by
  have key : ((z * unipotent (1 : K) * z⁻¹ : SpecialLinearGroup (Fin 2) K) :
      Matrix (Fin 2) (Fin 2) K) 1 0 =
      -((z : Matrix (Fin 2) (Fin 2) K) 1 0 * (z : Matrix (Fin 2) (Fin 2) K) 1 0) := by
    simp [coe_unipotent, Matrix.mul_apply, Fin.sum_univ_two, Matrix.adjugate_fin_two] <;> ring
  have h10 : ((z * unipotent (1 : K) * z⁻¹ : SpecialLinearGroup (Fin 2) K) :
      Matrix (Fin 2) (Fin 2) K) 1 0 =
      ((unipotent r : SpecialLinearGroup (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) 1 0 := by
    rw [h]
  have hr : ((unipotent r : SpecialLinearGroup (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) 1 0 = 0 := by
    simp [coe_unipotent]
  rw [key, hr] at h10
  have hcc : (z : Matrix (Fin 2) (Fin 2) K) 1 0 * (z : Matrix (Fin 2) (Fin 2) K) 1 0 = 0 := by
    linear_combination -h10
  exact mul_self_eq_zero.mp hcc

private theorem lower_left_wElt_conj {K : Type} [Field K] (z : SpecialLinearGroup (Fin 2) K) :
    ((wElt K * z * (wElt K)⁻¹ : SpecialLinearGroup (Fin 2) K) :
      Matrix (Fin 2) (Fin 2) K) 1 0 = -(z : Matrix (Fin 2) (Fin 2) K) 0 1 := by
  dsimp only [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_inv, coe_wElt]
  simp only [Matrix.adjugate_fin_two, Matrix.mul_apply, Fin.sum_univ_two, Matrix.of_apply,
    Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
    Matrix.empty_val', Matrix.cons_val_fin_one, Matrix.head_fin_const]
  ring

private theorem lower_left_lElt_conj {K : Type} [Field K] (z : SpecialLinearGroup (Fin 2) K) :
    ((lElt K * z * (lElt K)⁻¹ : SpecialLinearGroup (Fin 2) K) :
      Matrix (Fin 2) (Fin 2) K) 1 0 =
      (z : Matrix (Fin 2) (Fin 2) K) 0 0 + (z : Matrix (Fin 2) (Fin 2) K) 1 0 -
        (z : Matrix (Fin 2) (Fin 2) K) 0 1 - (z : Matrix (Fin 2) (Fin 2) K) 1 1 := by
  dsimp only [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_inv, coe_lElt]
  simp only [Matrix.adjugate_fin_two, Matrix.mul_apply, Fin.sum_univ_two, Matrix.of_apply,
    Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
    Matrix.empty_val', Matrix.cons_val_fin_one, Matrix.head_fin_const]
  ring

theorem sl2_normal_le_normalizer_sylow {K : Type} [Field K] [Finite K] [CharP K 2]
    (E S : Subgroup (Matrix.SpecialLinearGroup (Fin 2) K)) (hE : E.Normal)
    (hS : Nat.card S = Nat.card K)
    (hES : E ≤ Subgroup.normalizer (S : Set (Matrix.SpecialLinearGroup (Fin 2) K))) : E = ⊥ := by
  letI := Fintype.ofFinite K
  obtain ⟨n, -, hn⟩ := FiniteField.card K 2
  have hcard : Nat.card K = 2 ^ (n : ℕ) := by rw [Nat.card_eq_fintype_card, hn]
  obtain ⟨g, hg⟩ := exists_conj_unipotent_mem Nat.prime_two hcard hS
  have hSmem : ∀ s ∈ S, ∃ t : K, s = g * unipotent t * g⁻¹ := by
    let ψ : K → S := fun t => ⟨g * unipotent t * g⁻¹, hg t⟩
    have hinj : Function.Injective ψ := by
      intro t t' h
      have h' : g * unipotent t * g⁻¹ = g * unipotent t' * g⁻¹ := congrArg Subtype.val h
      exact unipotent_injective (mul_left_cancel (mul_right_cancel h'))
    intro s hs
    obtain ⟨t, ht⟩ := (hinj.bijective_of_nat_card_le hS.le).2 ⟨s, hs⟩
    exact ⟨t, (congrArg Subtype.val ht).symm⟩
  have hconj : ∀ z ∈ E, ∃ r : K, z * unipotent (1 : K) * z⁻¹ = unipotent r := by
    intro z hz
    have hx : g * z * g⁻¹ ∈ E := hE.conj_mem z hz g
    have hmem : g * z * g⁻¹ * (g * unipotent (1 : K) * g⁻¹) * (g * z * g⁻¹)⁻¹ ∈ S :=
      (Subgroup.mem_normalizer_iff.mp (hES hx) (g * unipotent (1 : K) * g⁻¹)).mp (hg 1)
    obtain ⟨r, hr⟩ := hSmem _ hmem
    refine ⟨r, ?_⟩
    have key : g * (z * unipotent (1 : K) * z⁻¹) * g⁻¹ = g * unipotent r * g⁻¹ := by
      rw [← hr]
      group
    exact mul_left_cancel (mul_right_cancel key)
  have hlow : ∀ z ∈ E, (z : Matrix (Fin 2) (Fin 2) K) 1 0 = 0 := by
    intro z hz
    obtain ⟨r, hr⟩ := hconj z hz
    exact lower_left_eq_zero z hr
  rw [eq_bot_iff]
  intro γ hγ
  rw [Subgroup.mem_bot]
  have h10 : (γ : Matrix (Fin 2) (Fin 2) K) 1 0 = 0 := hlow γ hγ
  have h01 : (γ : Matrix (Fin 2) (Fin 2) K) 0 1 = 0 := by
    have h := hlow _ (hE.conj_mem γ hγ (wElt K))
    rw [lower_left_wElt_conj] at h
    exact neg_eq_zero.mp h
  have h00 : (γ : Matrix (Fin 2) (Fin 2) K) 0 0 = (γ : Matrix (Fin 2) (Fin 2) K) 1 1 := by
    have h := hlow _ (hE.conj_mem γ hγ (lElt K))
    rw [lower_left_lElt_conj] at h
    linear_combination h - h10 + h01
  have hdet : (γ : Matrix (Fin 2) (Fin 2) K) 0 0 * (γ : Matrix (Fin 2) (Fin 2) K) 1 1 = 1 := by
    have h := Matrix.SpecialLinearGroup.det_coe γ
    rw [Matrix.det_fin_two, h01, h10] at h
    linear_combination h
  have h2 : (2 : K) = 0 := CharTwo.two_eq_zero
  have hsq : ((γ : Matrix (Fin 2) (Fin 2) K) 0 0 - 1) * ((γ : Matrix (Fin 2) (Fin 2) K) 0 0 - 1)
      = 0 := by
    linear_combination (γ : Matrix (Fin 2) (Fin 2) K) 0 0 * h00 + hdet +
      (1 - (γ : Matrix (Fin 2) (Fin 2) K) 0 0) * h2
  have ha : (γ : Matrix (Fin 2) (Fin 2) K) 0 0 = 1 := by
    linear_combination mul_self_eq_zero.mp hsq
  have hd : (γ : Matrix (Fin 2) (Fin 2) K) 1 1 = 1 := by
    linear_combination ha - h00
  apply Matrix.SpecialLinearGroup.ext
  intro i j
  fin_cases i <;> fin_cases j <;>
    simp [h10, h01, ha, hd, Matrix.SpecialLinearGroup.coe_one]

end CFSG.Quasithin.H13.L319
