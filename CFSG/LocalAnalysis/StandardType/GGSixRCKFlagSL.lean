module

public import CFSG.LocalAnalysis.StandardType.GGSixRCKFlagCore
public import Mathlib.LinearAlgebra.Transvection.Basic
public import Mathlib.LinearAlgebra.SpecialLinearGroup

public section

namespace CFSG.StandardType.RCKFlag

open CFSG.Assembly CFSG.Blueprint CFSG.StandardType CFSG.StandardType.RCKC1 CFSG.Open Matrix

private lemma rckFlagSL_transvection
    {F : Type*} [Field F] {ι : Type*} [Fintype ι] [DecidableEq ι]
    (r : Matrix.SpecialLinearGroup ι F)
    (N : (ι → F) →ₗ[F] (ι → F)) (W H : Submodule F (ι → F))
    (hNr : Matrix.toLin' (r : Matrix ι ι F) = N + 1)
    (hW : LinearMap.range N = W) (hH : LinearMap.ker N = H) (hWH : W ≤ H)
    (p : (ι → F) →ₗ[F] W) (s : W →ₗ[F] (ι → F))
    (hp : ∀ w : W, p (w : ι → F) = w) (hs : ∀ w : W, N (s w) = (w : ι → F))
    (f : W →ₗ[F] F) (u : W) (hfu : f u = 0) :
    ∃ g : Matrix.SpecialLinearGroup ι F,
      g ∈ Subgroup.centralizer ({r} : Set (Matrix.SpecialLinearGroup ι F)) ∧
      ∀ x : W, (Matrix.SpecialLinearGroup.toGL g : Matrix ι ι F).mulVec (x : ι → F)
        = (x : ι → F) + f x • (u : ι → F) := by
  let φ : (ι → F) →ₗ[F] F := f.comp p
  let ψ : (ι → F) →ₗ[F] F := φ.comp N
  have huN : N (u : ι → F) = 0 := by
    have : (u : ι → F) ∈ LinearMap.ker N := by rw [hH]; exact hWH u.2
    simpa using this
  have hNN : ∀ y : ι → F, N (N y) = 0 := by
    intro y
    have hy : N y ∈ LinearMap.ker N := by
      rw [hH]
      exact hWH (by rw [← hW]; exact LinearMap.mem_range_self N y)
    simpa using hy
  have hφu : φ (u : ι → F) = 0 := by simp [φ, hp u, hfu]
  have hψsu : ψ (s u) = 0 := by simp [ψ, hs u, hφu]
  let A : (ι → F) →ₗ[F] (ι → F) := φ.smulRight (u : ι → F)
  let B : (ι → F) →ₗ[F] (ι → F) := ψ.smulRight (s u)
  have hAN : A * N = ψ.smulRight (u : ι → F) := by
    apply LinearMap.ext; intro y
    simp [A, ψ, φ, LinearMap.smulRight_apply]
  have hNA : N * A = 0 := by
    apply LinearMap.ext; intro y
    simp [A, LinearMap.smulRight_apply, huN]
  have hBN : B * N = 0 := by
    apply LinearMap.ext; intro y
    simp [B, ψ, hNN y, LinearMap.smulRight_apply]
  have hNB : N * B = ψ.smulRight (u : ι → F) := by
    apply LinearMap.ext; intro y
    simp [B, LinearMap.smulRight_apply, hs u]
  let GA : _root_.SpecialLinearGroup F (ι → F) :=
    ⟨LinearEquiv.transvection hφu, by simp⟩
  let GB : _root_.SpecialLinearGroup F (ι → F) :=
    ⟨LinearEquiv.transvection hψsu, by simp⟩
  let G : _root_.SpecialLinearGroup F (ι → F) := GA * GB
  have hGA : ((GA : (ι → F) ≃ₗ[F] (ι → F)) : (ι → F) →ₗ[F] (ι → F)) = 1 + A := by
    change (LinearEquiv.transvection hφu : (ι → F) →ₗ[F] (ι → F)) = 1 + A
    rw [LinearEquiv.transvection.coe_toLinearMap]
    ext y
    simp [A, LinearMap.transvection.apply, LinearMap.smulRight_apply]
  have hGB : ((GB : (ι → F) ≃ₗ[F] (ι → F)) : (ι → F) →ₗ[F] (ι → F)) = 1 + B := by
    change (LinearEquiv.transvection hψsu : (ι → F) →ₗ[F] (ι → F)) = 1 + B
    rw [LinearEquiv.transvection.coe_toLinearMap]
    ext y
    simp [B, LinearMap.transvection.apply, LinearMap.smulRight_apply]
  have hG : (G : (ι → F) →ₗ[F] (ι → F)) = (1 + A) * (1 + B) := by
    have h1 : (G : (ι → F) →ₗ[F] (ι → F))
        = ((GA : (ι → F) ≃ₗ[F] (ι → F)) : (ι → F) →ₗ[F] (ι → F)) *
          ((GB : (ι → F) ≃ₗ[F] (ι → F)) : (ι → F) →ₗ[F] (ι → F)) := by
      simp [G, _root_.SpecialLinearGroup.coe_mul, LinearEquiv.coe_toLinearMap_mul]
    rw [h1, hGA, hGB]
  have hGN : (G : (ι → F) →ₗ[F] (ι → F)) * N = N * (G : (ι → F) →ₗ[F] (ι → F)) := by
    rw [hG]
    have h1 : (1 + B) * N = N := by rw [add_mul, one_mul, hBN, add_zero]
    have h2 : (1 + A) * N = N + ψ.smulRight (u : ι → F) := by
      rw [add_mul, one_mul, hAN]
    have h3 : N * (1 + A) = N := by rw [mul_add, mul_one, hNA, add_zero]
    have h4 : N * (1 + B) = N + ψ.smulRight (u : ι → F) := by rw [mul_add, mul_one, hNB]
    rw [mul_assoc, h1, h2, ← mul_assoc, h3, h4]
  have hR : (Matrix.SpecialLinearGroup.toLin'_equiv r : (ι → F) →ₗ[F] (ι → F)) =
      N + 1 := by
    change (Matrix.SpecialLinearGroup.toLin' r : (ι → F) →ₗ[F] (ι → F)) = N + 1
    rw [Matrix.SpecialLinearGroup.toLin'_to_linearMap, hNr]
  have hGR : G * Matrix.SpecialLinearGroup.toLin'_equiv r
      = Matrix.SpecialLinearGroup.toLin'_equiv r * G := by
    apply _root_.SpecialLinearGroup.ext
    intro y
    have hc : (G : (ι → F) →ₗ[F] (ι → F)) (N y) = N ((G : (ι → F) →ₗ[F] (ι → F)) y) := by
      have := congrArg (fun L : (ι → F) →ₗ[F] (ι → F) => L y) hGN
      simpa [Module.End.mul_apply] using this
    change (G : (ι → F) →ₗ[F] (ι → F))
        ((Matrix.SpecialLinearGroup.toLin'_equiv r : (ι → F) →ₗ[F] (ι → F)) y)
      = (Matrix.SpecialLinearGroup.toLin'_equiv r : (ι → F) →ₗ[F] (ι → F))
        ((G : (ι → F) →ₗ[F] (ι → F)) y)
    rw [hR, LinearMap.add_apply, LinearMap.add_apply, Module.End.one_apply, Module.End.one_apply,
      map_add, hc]
  let g : Matrix.SpecialLinearGroup ι F := Matrix.SpecialLinearGroup.toLin'_equiv.symm G
  refine ⟨g, ?_, ?_⟩
  · rw [Subgroup.mem_centralizer_singleton_iff]
    have hgG : Matrix.SpecialLinearGroup.toLin'_equiv g = G := by simp [g]
    have hh : Matrix.SpecialLinearGroup.toLin'_equiv (g * r)
        = Matrix.SpecialLinearGroup.toLin'_equiv (r * g) := by
      rw [map_mul, map_mul, hgG]
      exact hGR
    exact Matrix.SpecialLinearGroup.toLin'_equiv.injective hh
  · intro x
    have hxN : N (x : ι → F) = 0 := by
      have : (x : ι → F) ∈ LinearMap.ker N := by rw [hH]; exact hWH x.2
      simpa using this
    have hxG : (G : (ι → F) →ₗ[F] (ι → F)) (x : ι → F)
        = (x : ι → F) + f x • (u : ι → F) := by
      rw [hG]
      have hψx : ψ (x : ι → F) = 0 := by simp [ψ, hxN]
      have hφx : φ (x : ι → F) = f x := by simp [φ, hp x]
      simp [A, B, hψx, hφx, LinearMap.smulRight_apply]
    have hjg : (Matrix.SpecialLinearGroup.toGL g : Matrix ι ι F) = LinearMap.toMatrix' G := by
      rw [Matrix.SpecialLinearGroup.coe_GL_coe_matrix]
      rfl
    rw [hjg, LinearMap.toMatrix'_mulVec]
    exact hxG

theorem rckFlagIrredW_SL (m g : ℕ) (hg : 1 ≤ g) :
    FlagIrredW (Matrix.SpecialLinearGroup.toGL (n := Fin (m + 1)) (R := GaloisField 2 g)) none := by
  intro R' W H hWH hv hB r hr hr1 P hPW hInv
  by_cases hbot : P = ⊥
  · exact Or.inl hbot
  · right
    obtain ⟨x, hxP, hx0⟩ := (Submodule.ne_bot_iff P).mp hbot
    let xW : W := ⟨x, hPW hxP⟩
    have hxW0 : xW ≠ 0 := by
      intro h
      exact hx0 (congrArg Subtype.val h)
    obtain ⟨f, hfx⟩ := Module.Projective.exists_dual_eq_one (GaloisField 2 g) hxW0
    let N : (Fin (m + 1) → GaloisField 2 g) →ₗ[GaloisField 2 g]
        (Fin (m + 1) → GaloisField 2 g) :=
      Matrix.toLin' ((Matrix.SpecialLinearGroup.toGL r : Matrix (Fin (m + 1)) (Fin (m + 1))
        (GaloisField 2 g)) - 1)
    have hv' := hv r hr hr1
    have hW : LinearMap.range N = W := hv'.1
    have hH : LinearMap.ker N = H := hv'.2
    have hNr : Matrix.toLin' (r : Matrix (Fin (m + 1)) (Fin (m + 1)) (GaloisField 2 g))
        = N + 1 := by
      have h : Matrix.toLin' (r : Matrix (Fin (m + 1)) (Fin (m + 1)) (GaloisField 2 g)) - 1
          = N := by
        dsimp only [N]
        rw [map_sub, Matrix.toLin'_one, Matrix.SpecialLinearGroup.coe_GL_coe_matrix]
        rfl
      exact (sub_eq_iff_eq_add.mp h)
    obtain ⟨s', hs'⟩ := N.rangeRestrict.exists_rightInverse_of_surjective N.range_rangeRestrict
    let incl : W →ₗ[GaloisField 2 g] LinearMap.range N :=
      { toFun := fun w => ⟨(w : Fin (m + 1) → GaloisField 2 g), by rw [hW]; exact w.2⟩
        map_add' := fun a b => Subtype.ext rfl
        map_smul' := fun c a => Subtype.ext rfl }
    let s : W →ₗ[GaloisField 2 g] (Fin (m + 1) → GaloisField 2 g) := s'.comp incl
    have hs : ∀ w : W, N (s w) = (w : Fin (m + 1) → GaloisField 2 g) := by
      intro w
      have h3 := congrArg Subtype.val (LinearMap.congr_fun hs' (incl w))
      have h2 : N (s' (incl w)) = (incl w : Fin (m + 1) → GaloisField 2 g) := by
        simpa [LinearMap.rangeRestrict, LinearMap.codRestrict] using h3
      simpa [s, incl] using h2
    obtain ⟨Q, hQ⟩ := Submodule.exists_isCompl W
    have hcompl : IsCompl (LinearMap.range W.subtype) Q := by rwa [Submodule.range_subtype]
    let p : (Fin (m + 1) → GaloisField 2 g) →ₗ[GaloisField 2 g] W :=
      LinearMap.linearProjOfIsCompl Q W.subtype W.subtype_injective hcompl
    have hp : ∀ w : W, p (w : Fin (m + 1) → GaloisField 2 g) = w :=
      fun w => LinearMap.linearProjOfIsCompl_apply_left Q W.subtype W.subtype_injective hcompl w
    have hker_le : ∀ u : W, f u = 0 → (u : Fin (m + 1) → GaloisField 2 g) ∈ P := by
      intro u hfu
      obtain ⟨gu, hgu, hact⟩ :=
        rckFlagSL_transvection r N W H hNr hW hH hWH p s hp hs f u hfu
      have hact' : (Matrix.SpecialLinearGroup.toGL gu : Matrix (Fin (m + 1)) (Fin (m + 1))
          (GaloisField 2 g)).mulVec x
          = x + (u : Fin (m + 1) → GaloisField 2 g) := by
        have := hact xW
        simpa [xW, hfx] using this
      have hxpu : x + (u : Fin (m + 1) → GaloisField 2 g) ∈ P := by
        rw [← hact']; exact hInv gu hgu x hxP
      simpa using Submodule.sub_mem P hxpu hxP
    have hWleP : W ≤ P := by
      intro y hy
      let yW : W := ⟨y, hy⟩
      have h1 : f yW • x ∈ P := P.smul_mem (f yW) hxP
      have h2 : y - f yW • x ∈ P := by
        have hmemW : y - f yW • (xW : Fin (m + 1) → GaloisField 2 g) ∈ W :=
          W.sub_mem hy (W.smul_mem (f yW) (hPW hxP))
        have hzero : f ⟨y - f yW • (xW : Fin (m + 1) → GaloisField 2 g), hmemW⟩ = 0 := by
          have hEq : (⟨y - f yW • (xW : Fin (m + 1) → GaloisField 2 g), hmemW⟩ : W)
              = yW - f yW • xW := by ext; rfl
          rw [hEq]
          simp [hfx]
        have := hker_le ⟨y - f yW • (xW : Fin (m + 1) → GaloisField 2 g), hmemW⟩ hzero
        simpa [xW] using this
      have hyeq : y = f yW • x + (y - f yW • x) := by abel
      rw [hyeq]
      exact P.add_mem h1 h2
    exact le_antisymm hPW hWleP

theorem rckFlagCent_SL (m g : ℕ) (hg : 1 ≤ g) :
    FlagCentU (Matrix.SpecialLinearGroup.toGL (n := Fin (m + 1)) (R := GaloisField 2 g)) none := by
  exact flagCentU_of_irredW
    (Matrix.SpecialLinearGroup.toGL (n := Fin (m + 1)) (R := GaloisField 2 g)) none
    (Matrix.SpecialLinearGroup.toGL_injective (n := Fin (m + 1)) (R := GaloisField 2 g))
    (rckFlagIrredW_SL m g hg)

end CFSG.StandardType.RCKFlag
