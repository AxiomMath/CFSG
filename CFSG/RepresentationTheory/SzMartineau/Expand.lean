module

public import CFSG.RepresentationTheory.SzMartineau.Relations
public import CFSG.RepresentationTheory.SzMartineau.Cocycle
public import CFSG.RepresentationTheory.SzMartineau.SzTwo
public import Mathlib.Algebra.CharP.Two
public import Mathlib.Tactic.FinCases
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Ring

public section

open scoped CharTwo

namespace CFSG.RepresentationTheory.SzMartineau

open CFSG.Open CFSG.RankThree.GF2n.SzExplicit CFSG.CGT.PushingUpLit.SolKNA Matrix

section Generic

variable {G R : Type*} [Group G] [Ring R] {φ ψ : G →* R} {Y : G → R}

theorem IsTwistedCocycle.apply_conj (hY : IsTwistedCocycle φ ψ Y) {g : G} (hg : Y g = 0)
    (h : G) : Y (g * h * g⁻¹) = φ g * Y h * ψ g⁻¹ := by
  have hg' : Y g⁻¹ = 0 := by
    rw [hY.map_inv, hg, mul_zero, zero_mul, neg_zero]
  rw [show g * h * g⁻¹ = g * (h * g⁻¹) from mul_assoc g h g⁻¹, hY, hY, hg, hg']
  simp [mul_assoc]

end Generic

variable {a c : ℕ} {Y : ↥(Sz a) → Matrix (Fin 4) (Fin 4) (F a)}

theorem IsTwistedCocycle.apply_rootSz_unit (hY : IsTwistedCocycle (natHom a) (twHom a c) Y)
    (hT : ∀ x, Y (torusSz a x) = 0) (x : (F a)ˣ) :
    Y (rootSz a x 0) = torusMat a x * Y (rootSz a 1 0) * torusMat a (x ^ 2 ^ c)⁻¹ := by
  have hroot : torusSz a x * rootSz a 1 0 * (torusSz a x)⁻¹ = rootSz a x 0 := by
    rw [torusSz_mul_rootSz]
    simp
  have hxinv : (torusSz a x)⁻¹ = torusSz a x⁻¹ := by
    apply inv_eq_of_mul_eq_one_right
    rw [torusSz_mul_torusSz, mul_inv_cancel, torusSz_one]
  rw [← hroot]
  have hconj := hY.apply_conj (g := torusSz a x) (hT x) (rootSz a 1 0)
  simpa only [hxinv, natHom_torusSz, twHom_torusSz, inv_pow] using hconj

theorem IsTwistedCocycle.apply_rootSz_zero_one (hY : IsTwistedCocycle (natHom a) (twHom a c) Y) :
    Y (rootSz a 0 1) = rootMat a 1 0 * Y (rootSz a 1 0) + Y (rootSz a 1 0) * rootMat a 1 0 := by
  have hsq : rootSz a 1 0 * rootSz a 1 0 = rootSz a 0 1 := by
    rw [rootSz_mul_rootSz]
    simp
  rw [← hsq, hY, natHom_rootSz, twHom_rootSz_one_zero]

theorem IsTwistedCocycle.apply_rootSz_zero_unit (hY : IsTwistedCocycle (natHom a) (twHom a c) Y)
    (hT : ∀ x, Y (torusSz a x) = 0) (y : (F a)ˣ) :
    Y (rootSz a 0 ((y : F a) ^ (1 + 2 ^ (a + 1)))) =
      torusMat a y * Y (rootSz a 0 1) * torusMat a (y ^ 2 ^ c)⁻¹ := by
  have hroot : torusSz a y * rootSz a 0 1 * (torusSz a y)⁻¹ =
      rootSz a 0 ((y : F a) ^ (1 + 2 ^ (a + 1))) := by
    rw [torusSz_mul_rootSz]
    simp
  have hyinv : (torusSz a y)⁻¹ = torusSz a y⁻¹ := by
    apply inv_eq_of_mul_eq_one_right
    rw [torusSz_mul_torusSz, mul_inv_cancel, torusSz_one]
  rw [← hroot]
  have hconj := hY.apply_conj (g := torusSz a y) (hT y) (rootSz a 0 1)
  simpa only [hyinv, natHom_torusSz, twHom_torusSz, inv_pow] using hconj

theorem IsTwistedCocycle.apply_rootSz (hY : IsTwistedCocycle (natHom a) (twHom a c) Y)
    (α β : F a) :
    Y (rootSz a α β) = rootMat a α 0 * Y (rootSz a 0 β) +
      Y (rootSz a α 0) * rootMat a 0 (β ^ 2 ^ c) := by
  have hroot : rootSz a α 0 * rootSz a 0 β = rootSz a α β := by
    rw [rootSz_mul_rootSz]
    simp
  rw [← hroot, hY (rootSz a α 0) (rootSz a 0 β), natHom_rootSz, twHom_rootSz]
  simp

theorem IsTwistedCocycle.apply_rootSz_add (hY : IsTwistedCocycle (natHom a) (twHom a c) Y)
    (α γ : F a) :
    rootMat a α 0 * Y (rootSz a γ 0) + Y (rootSz a α 0) * rootMat a (γ ^ 2 ^ c) 0 =
      rootMat a (α + γ) 0 * Y (rootSz a 0 (α * γ ^ 2 ^ (a + 1))) +
        Y (rootSz a (α + γ) 0) * rootMat a 0 ((α * γ ^ 2 ^ (a + 1)) ^ 2 ^ c) := by
  have hrel : rootSz a α 0 * rootSz a γ 0 =
      rootSz a (α + γ) 0 * rootSz a 0 (α * γ ^ 2 ^ (a + 1)) := by
    rw [rootSz_mul_rootSz, rootSz_mul_rootSz]
    simp
  calc rootMat a α 0 * Y (rootSz a γ 0) + Y (rootSz a α 0) * rootMat a (γ ^ 2 ^ c) 0
      = Y (rootSz a α 0 * rootSz a γ 0) := by
        rw [hY (rootSz a α 0) (rootSz a γ 0), natHom_rootSz, twHom_rootSz]
        simp
    _ = Y (rootSz a (α + γ) 0 * rootSz a 0 (α * γ ^ 2 ^ (a + 1))) := by rw [hrel]
    _ = rootMat a (α + γ) 0 * Y (rootSz a 0 (α * γ ^ 2 ^ (a + 1))) +
          Y (rootSz a (α + γ) 0) * rootMat a 0 ((α * γ ^ 2 ^ (a + 1)) ^ 2 ^ c) := by
        rw [hY (rootSz a (α + γ) 0) (rootSz a 0 (α * γ ^ 2 ^ (a + 1))), natHom_rootSz,
          twHom_rootSz]
        simp

theorem IsTwistedCocycle.eq_zero_of_normalized (hY : IsTwistedCocycle (natHom a) (twHom a c) Y)
    (hT : ∀ x, Y (torusSz a x) = 0) (hw : Y (w a) = 0) (h1 : Y (rootSz a 1 0) = 0)
    (g : ↥(Sz a)) : Y g = 0 := by
  have h00 : rootSz a 0 0 = 1 := Subtype.ext (Units.ext rootMat_zero_zero)
  have hα : ∀ α : F a, Y (rootSz a α 0) = 0 := by
    intro α
    rcases eq_or_ne α 0 with hα | hα
    · subst hα
      rw [h00, hY.map_one]
    · have h := hY.apply_rootSz_unit hT (Units.mk0 α hα)
      rw [Units.val_mk0] at h
      rw [h1, mul_zero, zero_mul] at h
      exact h
  have hβ : ∀ β : F a, Y (rootSz a 0 β) = 0 := by
    intro β
    rcases eq_or_ne β 0 with hβ | hβ
    · subst hβ
      rw [h00, hY.map_one]
    · obtain ⟨y, hy⟩ := exists_pow_one_add_theta (a := a) β
      have hy0 : y ≠ 0 := by
        rintro rfl
        rw [zero_pow (by positivity : 1 + 2 ^ (a + 1) ≠ 0)] at hy
        exact hβ hy.symm
      have h01 : Y (rootSz a 0 1) = 0 := by
        rw [hY.apply_rootSz_zero_one, h1, mul_zero, zero_mul, add_zero]
      have h := hY.apply_rootSz_zero_unit hT (Units.mk0 y hy0)
      rw [Units.val_mk0] at h
      rw [← hy]
      simpa [h01] using h
  have hαβ : ∀ α β : F a, Y (rootSz a α β) = 0 := by
    intro α β
    rw [hY.apply_rootSz α β, hα α, hβ β, mul_zero, zero_mul, add_zero]
  let S : Set (GL (Fin 4) (F a)) :=
    {A | (A : Matrix (Fin 4) (Fin 4) (F a)) ∈ SzGenerators a}
  have hSH : S ⊆ Sz a := fun _ hs => Subgroup.subset_closure hs
  have hH : Sz a ≤ Subgroup.closure S := le_refl _
  refine IsTwistedCocycle.eq_zero_of_le_closure (H := Sz a) (S := S) hSH hH hY ?_ g
  intro s hs
  obtain hroot | htorus | hW := cases_of_mem_szGenerators (a := a) hs (hSH hs)
  · obtain ⟨α, β, h⟩ := hroot
    rw [h, hαβ α β]
  · obtain ⟨x, h⟩ := htorus
    rw [h, hT x]
  · rw [hW, hw]

theorem eq_of_szJ_mul_eq {K : Type*} [CommRing K] [CharP K 2] {X : Matrix (Fin 4) (Fin 4) K}
    (hX : szJ * X = X * szJ) (i j : Fin 4) : X (Fin.rev i) (Fin.rev j) = X i j := by
  have h := congrFun (congrFun hX (Fin.rev i)) j
  fin_cases i <;> fin_cases j <;>
    simpa [szJ, Matrix.mul_apply, Matrix.vecMul_apply, dotProduct, Fin.sum_univ_four] using h.symm

theorem szX₀_mul_add_mul_szX₀ {K : Type*} [CommRing K] [CharP K 2]
    {X : Matrix (Fin 4) (Fin 4) K} (hX : szJ * X = X * szJ) :
    szX₀ * X + X * szX₀ =
      !![X 0 3 + X 1 0, X 0 0 + X 0 2 + X 1 1, X 1 2, X 0 1 + X 0 2 + X 1 3;
         X 0 3 + X 1 3, X 0 2 + X 1 0 + X 1 2, X 0 1, X 0 0 + X 1 1 + X 1 2;
         X 0 3, X 0 2 + X 1 3, X 0 1 + X 1 2, X 0 0 + X 1 1 + X 1 2 + X 1 3;
         0, X 0 3, X 0 2, X 0 1 + X 0 2 + X 0 3] := by
  have e03 : X 3 0 = X 0 3 := by simpa using eq_of_szJ_mul_eq hX 0 3
  have e02 : X 3 1 = X 0 2 := by simpa using eq_of_szJ_mul_eq hX 0 2
  have e01 : X 3 2 = X 0 1 := by simpa using eq_of_szJ_mul_eq hX 0 1
  have e00 : X 3 3 = X 0 0 := by simpa using eq_of_szJ_mul_eq hX 0 0
  have e13 : X 2 0 = X 1 3 := by simpa using eq_of_szJ_mul_eq hX 1 3
  have e12 : X 2 1 = X 1 2 := by simpa using eq_of_szJ_mul_eq hX 1 2
  have e11 : X 2 2 = X 1 1 := by simpa using eq_of_szJ_mul_eq hX 1 1
  have e10 : X 2 3 = X 1 0 := by simpa using eq_of_szJ_mul_eq hX 1 0
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [szX₀, Matrix.mul_apply, Matrix.vecMul_apply, dotProduct, Fin.sum_univ_four,
      e03, e02, e01, e00, e13, e12, e11, e10] <;>
    ring_nf <;>
    simp [CharTwo.two_eq_zero]

end CFSG.RepresentationTheory.SzMartineau
