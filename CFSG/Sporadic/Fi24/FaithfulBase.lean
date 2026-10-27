
module

public import CFSG.Sporadic.Fi24.OrbitBase

public section

namespace CFSG.Sporadic.Fi24

open CFSG.F3.Native Native Matrix CFSG.Sporadic.Th CFSG.Sporadic.Th.Native

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

section Proj

variable {r : ℕ} (R : Matrix (Fin r) (Fin 781) (ZMod 3)) (F : Matrix (Fin 781) (Fin 781) (ZMod 3))
  (S : Matrix (Fin r) (Fin r) (ZMod 3))

theorem proj_unique (hSK : S * (R * F * Rᵀ) = 1) {Z₁ Z₂ : Matrix (Fin 781) (Fin 781) (ZMod 3)}
    {X₁ X₂ : Matrix (Fin r) (Fin 781) (ZMod 3)} (h₁ : Z₁ = Rᵀ * X₁) (h₂ : Z₂ = Rᵀ * X₂)
    (e₁ : R * F * (1 - Z₁) = 0) (e₂ : R * F * (1 - Z₂) = 0) : Z₁ = Z₂ := by
  have e1' : R * F * Z₁ = R * F := by
    rw [Matrix.mul_sub, Matrix.mul_one, sub_eq_zero] at e₁; exact e₁.symm
  have e2' : R * F * Z₂ = R * F := by
    rw [Matrix.mul_sub, Matrix.mul_one, sub_eq_zero] at e₂; exact e₂.symm
  have hK : R * F * Rᵀ * X₁ = R * F * Rᵀ * X₂ := by
    rw [Matrix.mul_assoc (R * F), ← h₁, e1', Matrix.mul_assoc (R * F), ← h₂, e2']
  have hX : X₁ = X₂ := by
    calc X₁ = S * (R * F * Rᵀ) * X₁ := by rw [hSK, Matrix.one_mul]
      _ = S * (R * F * Rᵀ * X₁) := by rw [Matrix.mul_assoc]
      _ = S * (R * F * Rᵀ * X₂) := by rw [hK]
      _ = X₂ := by rw [← Matrix.mul_assoc, hSK, Matrix.one_mul]
  rw [h₁, h₂, hX]

theorem proj_eq (hKS : (R * F * Rᵀ) * S = 1) : R * F * (1 - Rᵀ * (S * (R * F))) = 0 := by
  rw [Matrix.mul_sub, Matrix.mul_one]
  calc R * F - R * F * (Rᵀ * (S * (R * F))) = R * F - ((R * F * Rᵀ) * S) * (R * F) := by
        simp only [Matrix.mul_assoc]
    _ = 0 := by rw [hKS, Matrix.one_mul, sub_self]

theorem commute_proj (hSK : S * (R * F * Rᵀ) = 1) (hKS : (R * F * Rᵀ) * S = 1)
    {g g' : Matrix (Fin 781) (Fin 781) (ZMod 3)} (hgg : g * g' = 1) (hg'g : g' * g = 1)
    (hF : gᵀ * F * g = F) {M M' : Matrix (Fin r) (Fin r) (ZMod 3)} (hM : g * Rᵀ = Rᵀ * M)
    (hM' : g' * Rᵀ = Rᵀ * M') :
    g * (Rᵀ * (S * (R * F))) = (Rᵀ * (S * (R * F))) * g := by
  set Z := Rᵀ * (S * (R * F))
  have hFg : F * g = g'ᵀ * F := by
    calc F * g = (g * g')ᵀ * F * g := by rw [hgg, Matrix.transpose_one, Matrix.one_mul]
      _ = g'ᵀ * (gᵀ * F * g) := by rw [Matrix.transpose_mul]; simp only [Matrix.mul_assoc]
      _ = g'ᵀ * F := by rw [hF]
  have hRFg : R * F * g = M'ᵀ * (R * F) := by
    have : R * g'ᵀ = M'ᵀ * R := by
      have := congrArg Matrix.transpose hM'
      rwa [Matrix.transpose_mul, Matrix.transpose_mul, Matrix.transpose_transpose] at this
    rw [Matrix.mul_assoc, hFg, ← Matrix.mul_assoc, this, Matrix.mul_assoc]
  have key : g * Z * g' = Z := by
    refine proj_unique R F S hSK (X₁ := M * (S * (R * F)) * g') (X₂ := S * (R * F)) ?_ rfl ?_
      (proj_eq R F S hKS)
    · simp only [Z]
      rw [← Matrix.mul_assoc g, hM]; simp only [Matrix.mul_assoc]
    · have e : g * (1 - Z) * g' = 1 - g * Z * g' := by
        rw [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one, hgg]
      calc R * F * (1 - g * Z * g') = R * F * (g * (1 - Z) * g') := by rw [e]
        _ = (R * F * g) * (1 - Z) * g' := by simp only [Matrix.mul_assoc]
        _ = M'ᵀ * (R * F * (1 - Z)) * g' := by rw [hRFg]; simp only [Matrix.mul_assoc]
        _ = 0 := by rw [proj_eq R F S hKS]; simp
  calc g * Z = g * Z * (g' * g) := by rw [hg'g, Matrix.mul_one]
    _ = (g * Z * g') * g := by simp only [Matrix.mul_assoc]
    _ = Z * g := by rw [key]

end Proj

theorem matW_rows_eq (X : Array W) : (fun i : Fin 253 => vecW (rowW X i.val)) = matW 253 781 X := by
  funext i j; rfl

theorem chainBase_lt : ∀ h < 6, chainBase[h]! < nPts := by decide

theorem chainBase_size : chainBase.size = 6 := rfl

theorem baseForms_get {h : ℕ} (hh : h < 6) :
    (baseForms orb)[h]! = (form chainBase[h]!).rows := by
  unfold baseForms
  rw [getElem!_pos _ h (by simp [chainBase_size, hh]), Array.getElem_map,
    getElem!_pos chainBase h (by rw [chainBase_size]; exact hh)]

end CFSG.Sporadic.Fi24
