module

public import Mathlib.Data.Nat.Totient
public import Mathlib.Data.Sym.Sym2.Init
public import Mathlib.Tactic.NormNum.GCD

public section

namespace CFSG.RankThree.PartTwo.Sec8.Hering611

theorem exists_retraction_of_fixed_le {B : Type*} [CommGroup B] (σ : MulAut B) (hσ : σ ^ 8 = 1)
    {m m' : ℕ} (hm : ∀ b : B, b ^ m = 1) (hmm' : 8 * m' ≡ 1 [MOD m])
    (Z' : Subgroup B) (hfix : ∀ z ∈ Z', σ z = z) (hfix' : ∀ b : B, σ b = b → b ∈ Z') :
    ∃ ρ : B →* Z', (∀ z : Z', ρ (z : B) = z) ∧ ∀ b : B, ρ (σ b) = ρ b := by
  have h8 : ∀ b : B, (σ ^ 8) b = b := fun b => by simp [hσ]
  obtain ⟨N, hN⟩ : ∃ N : B →* B, ∀ b, N b = ∏ j ∈ Finset.range 8, (σ ^ j) b :=
    ⟨MonoidHom.mk' (fun b => ∏ j ∈ Finset.range 8, (σ ^ j) b)
      (fun a b => by simp only [map_mul, Finset.prod_mul_distrib]), fun b => rfl⟩
  have hσN : ∀ b, σ (N b) = N b := by
    intro b
    have key : ∀ j : ℕ, σ ((σ ^ j) b) = (σ ^ (j + 1)) b := fun j => by
      rw [pow_succ', MulAut.mul_apply]
    have h1 := Finset.prod_range_succ (fun j => (σ ^ j) b) 8
    have h2 := Finset.prod_range_succ' (fun j => (σ ^ j) b) 8
    simp only [h8, pow_zero, MulAut.one_apply] at h1 h2
    rw [hN, map_prod]
    simp only [key]
    exact (mul_right_cancel (h1.symm.trans h2)).symm
  have hNZ : ∀ b : B, N b ∈ Z' := fun b => hfix' _ (hσN b)
  have hpowZ : ∀ z ∈ Z', ∀ j : ℕ, (σ ^ j) z = z := by
    intro z hz j
    induction j with
    | zero => simp
    | succ k ih => rw [pow_succ', MulAut.mul_apply, ih, hfix z hz]
  have hNσ : ∀ b, N (σ b) = N b := by
    intro b
    have key : ∀ j : ℕ, (σ ^ j) (σ b) = σ ((σ ^ j) b) := fun j => by
      rw [← MulAut.mul_apply, ← MulAut.mul_apply, ← pow_succ, ← pow_succ']
    rw [hN, hN]
    simp only [key]
    rw [← map_prod]
    have h := hσN b
    rwa [hN] at h
  refine ⟨MonoidHom.mk' (fun b => (⟨(N b) ^ m', Z'.pow_mem (hNZ b) m'⟩ : Z'))
    (fun a b => Subtype.ext ?_), fun z => Subtype.ext ?_, fun b => Subtype.ext ?_⟩
  · simp only [map_mul, mul_pow, Subgroup.coe_mul]
  · show (N (z : B)) ^ m' = (z : B)
    have hz8 : N (z : B) = (z : B) ^ 8 := by
      rw [hN]
      simp [hpowZ _ z.2]
    rw [hz8, ← pow_mul]
    exact (pow_eq_pow_of_modEq hmm' (hm (z : B))).trans (pow_one _)
  · show (N (σ b)) ^ m' = (N b) ^ m'
    rw [hNσ b]

end CFSG.RankThree.PartTwo.Sec8.Hering611
