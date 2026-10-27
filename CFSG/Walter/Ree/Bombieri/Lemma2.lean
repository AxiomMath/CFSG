module

public import CFSG.Walter.Ree.Bombieri.Resultant

public section

namespace CFSG.Walter.Ree.Bombieri

namespace Elim

open MvPolynomial

@[expose] def qExpr (ε : ℤ) : PE :=
  (PE.var 2 * PE.var 1 ^ 2 + 1) * (PE.var 1 * PE.var 0 ^ 2 + 1) -
    (PE.var 2 * PE.var 1 - PE.const ε) * (PE.var 1 * PE.var 0 - PE.const ε) ^ 2

@[expose] noncomputable def varsA : ℕ → A5 := fun i => if h : i < 5 then X ⟨i, h⟩ else 0

noncomputable def Qε (ε : ℤ) : A5 := (qExpr ε).eval varsA fun _ => 0

noncomputable def fPoly : A5 := Qε 0 * Qε 1 * Qε (-1)

noncomputable def H : A5 := fPoly * H0

@[expose] def dH : Fin 5 → ℕ := ![53814, 44697, 18471, 7524, 1368]

theorem degreeOf_Qε_le (ε : ℤ) (i : Fin 5) :
    (Qε ε).degreeOf i ≤ (qExpr ε).degB (fun j => if j = i.val then 1 else 0) (fun _ => 0) := by
  refine PE.degreeOf_eval_le i (fun j => ?_) (fun _ => by simp) _
  simp only [varsA]
  split_ifs with h1 h2 h2
  · subst h2; simp
  · rw [degreeOf_X]; split_ifs with h3
    · exact absurd (congrArg Fin.val h3).symm h2
    · exact le_refl 0
  · simp
  · simp

theorem H_degreeOf (i : Fin 5) : H.degreeOf i ≤ dH i := by
  refine (degreeOf_mul_le _ _ _).trans ?_
  refine (add_le_add ((degreeOf_mul_le _ _ _).trans (add_le_add ((degreeOf_mul_le _ _ _).trans
    (add_le_add (degreeOf_Qε_le 0 i) (degreeOf_Qε_le 1 i))) (degreeOf_Qε_le (-1) i)))
    (H0_degreeOf i)).trans ?_
  fin_cases i <;> simp [dH0, dH, qExpr] <;> decide

variable {K : Type*} [Field K] [CharP K 3]

theorem evA5_Qε (zs : Fin 5 → K) (ε : ℤ) :
    evA5 zs (Qε ε) = (zs 2 * zs 1 ^ 2 + 1) * (zs 1 * zs 0 ^ 2 + 1) -
      (zs 2 * zs 1 - ε) * (zs 1 * zs 0 - ε) ^ 2 := by
  rw [Qε, PE.map_eval]
  simp [qExpr, varsA, evA5_X]

theorem evA5_H (zs : Fin 5 → K) :
    evA5 zs H = evA5 zs (Qε 0) * evA5 zs (Qε 1) * evA5 zs (Qε (-1)) * evA5 zs H0 := by
  simp [H, fPoly, map_mul]

variable [Fintype K]

theorem lemma2 {σ : K ≃+* K} {a s : ℕ} (hB1 : ∀ x : K, (σ x * x) ^ a = x ^ 2)
    (hB2 : ∀ x : K, (σ x * x ^ 2) ^ s = x)
    (hC : ∀ p ∈ ESigma K σ, thompsonT a p.1 p.2.1 p.2.2 = 0) (z : K) :
    evA5 (fun i => (σ ^ (i : ℕ)) z) H = 0 := by
  have hsurj : Function.Surjective fun x : K => x ^ s := fun x => ⟨_, hB2 x⟩
  have hinj : Function.Injective fun x : K => x ^ s := Finite.injective_iff_surjective.mpr hsurj
  set c := 1 + σ z * z ^ 2
  set y := c ^ s
  have hy : σ y * y ^ 2 = c := hinj (hB2 y)
  set u := σ z * z - σ y * y
  set zs : Fin 5 → K := fun i => (σ ^ (i : ℕ)) z
  have hz0 : zs 0 = z := by simp [zs]
  have hz1 : zs 1 = σ z := by simp [zs]
  have hz2 : zs 2 = σ (σ z) := by simp [zs]
  rw [evA5_H]
  by_cases hu : u ^ 3 = u
  ·
    have hQ (ε : ℤ) (he : u = ε) : evA5 zs (Qε ε) = 0 := by
      rw [evA5_Qε, hz0, hz1, hz2]
      have h1 : σ z * z ^ 2 + 1 = σ y * y ^ 2 := by rw [hy]; ring
      have h2 : σ z * z - ε = σ y * y := by rw [← he]; ring
      have h1' : σ (σ z) * σ z ^ 2 + 1 = σ (σ y) * σ y ^ 2 := by
        simpa using congrArg σ h1
      have h2' : σ (σ z) * σ z - ε = σ (σ y) * σ y := by
        simpa using congrArg σ h2
      rw [h1, h1', h2, h2']
      ring
    have h3 : (u - 0) * (u - 1) * (u - (-1)) = 0 := by linear_combination hu
    rcases mul_eq_zero.mp h3 with h | h
    · rcases mul_eq_zero.mp h with h | h
      · rw [hQ 0 (by simpa using sub_eq_zero.mp h)]; ring
      · rw [hQ 1 (by simpa using sub_eq_zero.mp h)]; ring
    · rw [hQ (-1) (by simpa using sub_eq_zero.mp h)]; ring
  ·
    have hp : (z, y, u) ∈ ESigma K σ := ⟨by simp only; rw [hy]; ring, rfl, hu⟩
    rw [H0_eval_eq_zero hB1 hC hp, mul_zero]

end Elim

end CFSG.Walter.Ree.Bombieri
