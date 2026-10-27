module

public import CFSG.Quasithin.EmptyFaithful.SzN27Sp4A
public import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.L2_5_7FinSp4

public section

namespace CFSG.Quasithin.SzN27.Sp4

open CFSG.ComponentClassification.UnbalancedCatalog.SpChain
open CFSG.QuasithinUnique.Setup.X7b (uElt_inj uElt_zero_eq_one radA1 radA2 mem_antiUnipotentCenter_iff_central)
open CFSG.QuasithinUnique.Fin257
open CFSG.QuasithinUnique.Fin257.Sp4
open Matrix

variable {K : Type} [Field K] [CharP K 2]

theorem exists_unip_dSp_of_upper {g : antiSp K}
    (hg : ∀ i j : Fin 4, j < i → glMat (g : GL (Fin 4) K) i j = 0) :
    ∃ (u : antiSp K) (s t : Kˣ), u ∈ antiUnipotent K ∧ g = u * dSp s t ∧
      (s : K) = glMat (g : GL (Fin 4) K) 0 0 ∧ (t : K) = glMat (g : GL (Fin 4) K) 1 1 := by
  have s03 := symp_entry g 0 3
  have s12 := symp_entry g 1 2
  norm_num at s03 s12
  have h10 := hg 1 0 (by decide)
  have h20 := hg 2 0 (by decide)
  have h21 := hg 2 1 (by decide)
  have h30 := hg 3 0 (by decide)
  have h31 := hg 3 1 (by decide)
  have h32 := hg 3 2 (by decide)
  rw [h10, h20, h30] at s03
  rw [h21, h31, h32] at s12
  simp only [zero_mul, mul_zero, add_zero, zero_add] at s03 s12
  have hs : glMat (g : GL (Fin 4) K) 0 0 ≠ 0 := by
    intro h
    rw [h] at s03
    simp at s03
  have ht : glMat (g : GL (Fin 4) K) 1 1 ≠ 0 := by
    intro h
    rw [h] at s12
    simp at s12
  let s : Kˣ := Units.mk0 _ hs
  let t : Kˣ := Units.mk0 _ ht
  refine ⟨g * (dSp s t)⁻¹, s, t, ?_, (inv_mul_cancel_right g _).symm, rfl, rfl⟩
  rw [mem_antiUnipotent_iff_upper]
  have hgl : glMat ((g * (dSp s t)⁻¹ : antiSp K) : GL (Fin 4) K) =
      glMat (g : GL (Fin 4) K) * dSpMat s⁻¹ t⁻¹ := by
    rw [glMat_mul, dSp_inv, glMat_dSp]
  rw [hgl]
  have e33 : glMat (g : GL (Fin 4) K) 3 3 * (s : K) = 1 := by
    rw [mul_comm]
    exact s03
  have e22 : glMat (g : GL (Fin 4) K) 2 2 * (t : K) = 1 := by
    rw [mul_comm]
    exact s12
  refine ⟨fun i j hij => ?_, fun i => ?_⟩
  · fin_cases i <;> fin_cases j <;>
      first
        | exact absurd hij (by decide)
        | simp [dSpMat, Matrix.mul_diagonal, h10, h20, h21, h30, h31, h32]
  · fin_cases i
    · simp [dSpMat, Matrix.mul_diagonal, s, hs]
    · simp [dSpMat, Matrix.mul_diagonal, t, ht]
    · simpa [dSpMat, Matrix.mul_diagonal] using e22
    · simpa [dSpMat, Matrix.mul_diagonal] using e33

omit [CharP K 2] in
theorem mul_eq_mul_of_conj {g x x' : antiSp K} (h : g * x * g⁻¹ = x') : g * x = x' * g := by
  rw [← h]
  group

theorem upper_of_mem_normalizer [Finite K] {g : antiSp K}
    (hg : g ∈ Subgroup.normalizer (antiUnipotent K : Set (antiSp K))) :
    ∀ i j : Fin 4, j < i → glMat (g : GL (Fin 4) K) i j = 0 := by
  obtain ⟨c1, c2⟩ := fixes_radicals (K := K) g hg
  obtain ⟨a', b', c', hA2⟩ := (c2 (uElt 1 0 0 0)).mp ⟨1, 0, 0, rfl⟩
  obtain ⟨b₂, c₂, d₂, hA1⟩ := (c1 (uElt 0 0 0 1)).mp ⟨0, 0, 1, rfl⟩
  obtain ⟨b₃, c₃, d₃, hA3⟩ := (c1 (uElt 0 1 0 0)).mp ⟨1, 0, 0, rfl⟩
  have key : ∀ {x x' : antiSp K} (h : g * x = x' * g) {a b c d a' b' c' d' : K},
      x = uElt a b c d → x' = uElt a' b' c' d' → ∀ i j : Fin 4,
        (glMat (g : GL (Fin 4) K) * uMat a b c d) i j = (uMat a' b' c' d' * glMat (g : GL (Fin 4) K)) i j := by
    intro x x' h a b c d a' b' c' d' hx hx' i j
    have h1 := congrArg (fun m : antiSp K => glMat (m : GL (Fin 4) K)) h
    simp only [Subgroup.coe_mul, Units.val_mul, hx, hx', glMat_uElt] at h1
    rw [h1]
  have E2 := key (mul_eq_mul_of_conj hA2) rfl rfl
  have E3 := key (mul_eq_mul_of_conj hA1) rfl rfl
  have E4 := key (mul_eq_mul_of_conj hA3) rfl rfl
  have e31 := E2 3 1
  have e33 := E2 3 3
  have f22 := E3 2 2
  have f32 := E3 3 2
  have g22 := E4 2 2
  simp [Matrix.mul_apply, Fin.sum_univ_four, uMat] at e31 e33 f22 f32 g22
  have h30 : glMat (g : GL (Fin 4) K) 3 0 = 0 := by linear_combination e31
  have h32 : glMat (g : GL (Fin 4) K) 3 2 = 0 := by linear_combination e33
  have h21 : glMat (g : GL (Fin 4) K) 2 1 = 0 := by linear_combination f22
  have h31 : glMat (g : GL (Fin 4) K) 3 1 = 0 := by linear_combination f32
  have h20 : glMat (g : GL (Fin 4) K) 2 0 = 0 := by linear_combination g22
  have s02 := symp_entry g 0 2
  have s12 := symp_entry g 1 2
  norm_num at s02 s12
  rw [h32, h20, h30] at s02
  rw [h21, h31, h32] at s12
  simp only [zero_mul, mul_zero, add_zero, zero_add] at s02 s12
  have h22 : glMat (g : GL (Fin 4) K) 2 2 ≠ 0 := by
    intro h
    rw [h] at s12
    simp at s12
  have h10 : glMat (g : GL (Fin 4) K) 1 0 = 0 := (mul_eq_zero.mp s02).resolve_right h22
  intro i j hij
  fin_cases i <;> fin_cases j <;> first
    | exact absurd hij (by decide)
    | assumption

theorem exists_unip_dSp_of_mem_normalizer [Finite K] {g : antiSp K}
    (hg : g ∈ Subgroup.normalizer (antiUnipotent K : Set (antiSp K))) :
    ∃ (u : antiSp K) (s t : Kˣ), u ∈ antiUnipotent K ∧ g = u * dSp s t ∧
      (s : K) = glMat (g : GL (Fin 4) K) 0 0 ∧ (t : K) = glMat (g : GL (Fin 4) K) 1 1 :=
  exists_unip_dSp_of_upper (upper_of_mem_normalizer hg)

end CFSG.Quasithin.SzN27.Sp4
