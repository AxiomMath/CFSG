module

public import CFSG.RankThree.PartOne.N143X.Weights

public section

namespace CFSG.RankThree.PartOne.F106.NAD

open Matrix Module CFSG.RankThree.PartOne.N143X

section Matrices

variable {L : Type*} [Field L]

theorem commute_of_commute_diagonal {m : Fin 3 → L} (hm : Function.Injective m)
    {A B : Matrix (Fin 3) (Fin 3) L} (hA : A * diagonal m = diagonal m * A)
    (hB : B * diagonal m = diagonal m * B) : A * B = B * A := by
  have hdiag : ∀ C : Matrix (Fin 3) (Fin 3) L, C * diagonal m = diagonal m * C →
      C = diagonal (fun i => C i i) := by
    intro C hC
    ext i j
    have h := congrFun (congrFun hC i) j
    rw [Matrix.mul_diagonal, Matrix.diagonal_mul] at h
    by_cases hij : i = j
    · subst hij
      simp
    · have h0 : C i j * (m j - m i) = 0 := by linear_combination h
      rcases mul_eq_zero.1 h0 with h1 | h1
      · simp [h1, Matrix.diagonal_apply_ne _ hij]
      · exact absurd (hm (sub_eq_zero.1 h1).symm) hij
  rw [hdiag A hA, hdiag B hB, Matrix.diagonal_mul_diagonal, Matrix.diagonal_mul_diagonal]
  congr 1
  funext i
  exact mul_comm _ _

theorem commute_of_commute_regular [IsAlgClosed L] {ω : L} (hω3 : ω ^ 3 = 1) (hω1 : ω ≠ 1)
    {X G : Matrix (Fin 3) (Fin 3) L} (hX : IsUnit X) (hG : IsUnit G)
    (hXG : G * X = ω • (X * G)) {A B : Matrix (Fin 3) (Fin 3) L} (hA : A * X = X * A)
    (hB : B * X = X * B) : A * B = B * A := by
  classical
  obtain ⟨μ, hμ⟩ := Module.End.exists_eigenvalue (Matrix.toLin' X)
  obtain ⟨v, hv⟩ := hμ.exists_hasEigenvector
  have hXv : X *ᵥ v = μ • v := by
    simpa [Matrix.toLin'_apply] using Module.End.mem_eigenspace_iff.1 hv.1
  have hv0 : v ≠ 0 := hv.2
  have hXinj := Matrix.mulVec_injective_iff_isUnit.2 hX
  have hGinj := Matrix.mulVec_injective_iff_isUnit.2 hG
  have hμ0 : μ ≠ 0 := by
    rintro rfl
    apply hv0
    apply hXinj
    rw [hXv, zero_smul, Matrix.mulVec_zero]
  have hω0 : ω ≠ 0 := by
    rintro rfl
    simp at hω3
  have hXG' : X * G = (ω ^ 2) • (G * X) := by
    rw [hXG, smul_smul, ← pow_succ, hω3, one_smul]
  have hshift : ∀ (u : Fin 3 → L) (c : L), X *ᵥ u = c • u →
      X *ᵥ (G *ᵥ u) = (ω ^ 2 * c) • (G *ᵥ u) := by
    intro u c hu
    rw [Matrix.mulVec_mulVec, hXG', Matrix.smul_mulVec, ← Matrix.mulVec_mulVec, hu,
      Matrix.mulVec_smul, smul_smul]
  have hX1 := hshift v μ hXv
  have hX2 := hshift (G *ᵥ v) (ω ^ 2 * μ) hX1
  have hω4 : ω ^ 2 * (ω ^ 2 * μ) = ω * μ := by
    have : ω ^ 2 * (ω ^ 2 * μ) = ω ^ 3 * ω * μ := by ring
    rw [this, hω3]
    ring
  rw [hω4] at hX2
  let w : Fin 3 → (Fin 3 → L) := ![v, G *ᵥ v, G *ᵥ (G *ᵥ v)]
  let m : Fin 3 → L := ![μ, ω ^ 2 * μ, ω * μ]
  have hω2 : ω ^ 2 ≠ 1 := by
    intro h
    apply hω1
    have : ω ^ 3 = ω := by rw [pow_succ, h, one_mul]
    rw [← this, hω3]
  have hne1 : ω ^ 2 * μ ≠ μ := fun h => hω2 (by
    have := mul_right_cancel₀ hμ0 (h.trans (one_mul μ).symm)
    exact this)
  have hne2 : ω * μ ≠ μ := fun h => hω1 (mul_right_cancel₀ hμ0 (h.trans (one_mul μ).symm))
  have hne3 : ω * μ ≠ ω ^ 2 * μ := fun h => hω1 (by
    have := mul_right_cancel₀ hμ0 h
    have h' : ω * (ω - 1) = 0 := by linear_combination -this
    rcases mul_eq_zero.1 h' with h0 | h0
    · exact absurd h0 hω0
    · exact (sub_eq_zero.1 h0))
  have hm : Function.Injective m := by
    intro i j h
    fin_cases i <;> fin_cases j
    · rfl
    · exact absurd h.symm hne1
    · exact absurd h.symm hne2
    · exact absurd h hne1
    · rfl
    · exact absurd h.symm hne3
    · exact absurd h hne2
    · exact absurd h hne3
    · rfl
  have hGv : G *ᵥ v ≠ 0 := fun h => hv0 (hGinj (h.trans (Matrix.mulVec_zero G).symm))
  have hGGv : G *ᵥ (G *ᵥ v) ≠ 0 := fun h => hGv (hGinj (h.trans (Matrix.mulVec_zero G).symm))
  have hev : ∀ i, Module.End.HasEigenvector (Matrix.toLin' X) (m i) (w i) := by
    intro i
    rw [Module.End.hasEigenvector_iff, Module.End.mem_eigenspace_iff, Matrix.toLin'_apply]
    fin_cases i
    · exact ⟨hXv, hv0⟩
    · exact ⟨hX1, hGv⟩
    · exact ⟨hX2, hGGv⟩
  have hli : LinearIndependent L w :=
    Module.End.eigenvectors_linearIndependent' (Matrix.toLin' X) m hm w hev
  let W : Matrix (Fin 3) (Fin 3) L := Matrix.of fun i j => w j i
  have hW : IsUnit W := Matrix.linearIndependent_cols_iff_isUnit.1 hli
  have hWdet : IsUnit W.det := (Matrix.isUnit_iff_isUnit_det W).1 hW
  have hWW : W * W⁻¹ = 1 := Matrix.mul_nonsing_inv W hWdet
  have hWW' : W⁻¹ * W = 1 := Matrix.nonsing_inv_mul W hWdet
  have hXW : X * W = W * diagonal m := by
    ext i j
    rw [Matrix.mul_diagonal]
    have := congrFun (show X *ᵥ w j = m j • w j by
      have := (hev j).1
      rwa [Module.End.mem_eigenspace_iff, Matrix.toLin'_apply] at this) i
    simpa [W, Matrix.mul_apply, Matrix.mulVec, dotProduct, mul_comm] using this
  have hWX : W⁻¹ * X = diagonal m * W⁻¹ := by
    calc W⁻¹ * X = W⁻¹ * X * (W * W⁻¹) := by rw [hWW, Matrix.mul_one]
      _ = W⁻¹ * (X * W) * W⁻¹ := by simp only [Matrix.mul_assoc]
      _ = W⁻¹ * (W * diagonal m) * W⁻¹ := by rw [hXW]
      _ = diagonal m * W⁻¹ := by
        rw [← Matrix.mul_assoc W⁻¹ W, hWW', Matrix.one_mul]
  have hconj : ∀ C : Matrix (Fin 3) (Fin 3) L, C * X = X * C →
      (W⁻¹ * C * W) * diagonal m = diagonal m * (W⁻¹ * C * W) := by
    intro C hC
    calc (W⁻¹ * C * W) * diagonal m = W⁻¹ * C * (W * diagonal m) := by
          rw [Matrix.mul_assoc]
      _ = W⁻¹ * C * (X * W) := by rw [hXW]
      _ = W⁻¹ * (C * X) * W := by simp only [Matrix.mul_assoc]
      _ = W⁻¹ * (X * C) * W := by rw [hC]
      _ = (W⁻¹ * X) * C * W := by simp only [Matrix.mul_assoc]
      _ = diagonal m * (W⁻¹ * C * W) := by rw [hWX]; simp only [Matrix.mul_assoc]
  have hAB := commute_of_commute_diagonal hm (hconj A hA) (hconj B hB)
  have hrecover : ∀ C : Matrix (Fin 3) (Fin 3) L, C = W * (W⁻¹ * C * W) * W⁻¹ := by
    intro C
    calc C = (W * W⁻¹) * C * (W * W⁻¹) := by rw [hWW, Matrix.one_mul, Matrix.mul_one]
      _ = W * (W⁻¹ * C * W) * W⁻¹ := by simp only [Matrix.mul_assoc]
  calc A * B = (W * (W⁻¹ * A * W) * W⁻¹) * (W * (W⁻¹ * B * W) * W⁻¹) := by
        rw [← hrecover A, ← hrecover B]
    _ = W * ((W⁻¹ * A * W) * (W⁻¹ * B * W)) * W⁻¹ := by
        calc _ = W * (W⁻¹ * A * W) * (W⁻¹ * W) * (W⁻¹ * B * W) * W⁻¹ := by
              simp only [Matrix.mul_assoc]
          _ = _ := by rw [hWW', Matrix.mul_one]; simp only [Matrix.mul_assoc]
    _ = W * ((W⁻¹ * B * W) * (W⁻¹ * A * W)) * W⁻¹ := by rw [hAB]
    _ = (W * (W⁻¹ * B * W) * W⁻¹) * (W * (W⁻¹ * A * W) * W⁻¹) := by
        calc _ = W * (W⁻¹ * B * W) * (W⁻¹ * W) * (W⁻¹ * A * W) * W⁻¹ := by
              rw [hWW', Matrix.mul_one]; simp only [Matrix.mul_assoc]
          _ = _ := by simp only [Matrix.mul_assoc]
    _ = B * A := by rw [← hrecover A, ← hrecover B]

end Matrices

section Group

variable {K : Type} [Field K]

theorem isUnit_mapL {ι : Type} [Fintype ι] [DecidableEq ι] (L : Type) [Field L] [Algebra K L]
    (g : GL ι K) : IsUnit (mapL L g) :=
  ⟨⟨mapL L g, mapL L g⁻¹, by rw [← mapL_mul, mul_inv_cancel, mapL_one],
    by rw [← mapL_mul, inv_mul_cancel, mapL_one]⟩, rfl⟩

theorem commute_of_regular {P : Type} [Group P] (ρ : P →* GL (Fin 3) K)
    (hρ : Function.Injective ρ) {ω : K} (hω3 : ω ^ 3 = 1) (hω1 : ω ≠ 1) {x g : P}
    (hxg : ((ρ g : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) *
      ((ρ x : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) =
      ω • (((ρ x : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) *
        ((ρ g : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K)))
    {a b : P} (ha : a * x = x * a) (hb : b * x = x * b) : a * b = b * a := by
  let L := AlgebraicClosure K
  have hXG : mapL L (ρ g) * mapL L (ρ x) = algebraMap K L ω • (mapL L (ρ x) * mapL L (ρ g)) := by
    have := congrArg (fun M : Matrix (Fin 3) (Fin 3) K => M.map (algebraMap K L)) hxg
    simpa only [mapL, Matrix.map_mul, Matrix.map_smul' (algebraMap K L) ω _ (map_mul _)] using this
  have hcomm : ∀ c : P, c * x = x * c →
      mapL L (ρ c) * mapL L (ρ x) = mapL L (ρ x) * mapL L (ρ c) := by
    intro c hc
    rw [← mapL_mul, ← mapL_mul, ← map_mul, ← map_mul, hc]
  have h := commute_of_commute_regular (L := L) (ω := algebraMap K L ω)
    (by rw [← map_pow, hω3, map_one])
    (fun h => hω1 ((algebraMap K L).injective (h.trans (map_one _).symm)))
    (isUnit_mapL L (ρ x)) (isUnit_mapL L (ρ g)) hXG (hcomm a ha) (hcomm b hb)
  rw [← mapL_mul, ← mapL_mul, ← map_mul, ← map_mul] at h
  exact hρ (mapL_injective L h)

end Group

end CFSG.RankThree.PartOne.F106.NAD
