module

public import CFSG.Quasithin.Background.C124YLL2Fix
public import CFSG.Quasithin.Background.C124YLS2Fix
public import CFSG.Quasithin.Background.C124YLL2Act

set_option linter.unusedSectionVars false

public section

namespace CFSG.Quasithin.C124.YL

open CFSG.Quasithin CFSG.Open CFSG.QuasithinUnique Matrix
open scoped MatrixGroups

namespace L2Ctx

variable {W : Type*} [CommGroup W] [Finite W] {F : Type} [Field F] [Finite F]
  {Xs Ls : Subgroup (MulAut W)} {U Z : Subgroup W} (C : L2Ctx F Xs Ls U Z)

theorem exists_theta_of_linear {x : ↥Xs} {k : ℕ} (hx : x ^ 2 ^ k = 1)
    (hlin : ∀ (a : F) v, C.gOf x (a • v) = a • C.gOf x v) :
    ∃ s : SL(2, F), x = C.thetaX s ∧ ∀ v, C.gOf x v = (s : Matrix (Fin 2) (Fin 2) F) *ᵥ v := by
  have hk : ∀ v, (C.gOf x)^[2 ^ k] v = v := fun v => by
    rw [← C.gOf_pow, hx, C.gOf_one]
  obtain ⟨s, hs⟩ := S2.exists_SL_of_linear C.hF4 (C.gOf x) hlin hk
  exact ⟨s, C.eq_of_gOf fun v => by rw [C.gOf_theta, hs], hs⟩

theorem linear_of_fix {x : ↥Xs} (hfix : ∀ a : F, C.gOf x ![a, 0] = ![a, 0]) :
    ∀ (a : F) v, C.gOf x (a • v) = a • C.gOf x v := by
  obtain ⟨τ, -, -, -, -, hτ⟩ := (C.normSL x).semilin
  have hτa : ∀ a, τ a = a := by
    intro a
    have h1 := hτ a ![1, 0]
    have e : a • (![1, 0] : Fin 2 → F) = ![a, 0] := by
      ext i
      fin_cases i <;> simp
    rw [e, hfix a, hfix 1] at h1
    have := congrFun h1 0
    simpa using this.symm
  intro a v
  rw [hτ, hτa]

theorem cent_Kroot {x : ↥Xs} {k : ℕ} (hx : x ^ 2 ^ k = 1)
    (hfix : ∀ u ∈ liftFix U Z C.Kroot, (x : MulAut W) u * u⁻¹ ∈ Z) :
    (x : MulAut W) ∈ C.Kroot := by
  have hfix' : ∀ a : F, C.gOf x ![a, 0] = ![a, 0] := by
    intro a
    have hq : Multiplicative.ofAdd (![a, 0] : Fin 2 → F) ∈ fixImg U Z C.c C.Kroot := by
      rw [C.mem_fixImg_Kroot]
      simp
    obtain ⟨u, hu, hu'⟩ := mem_fixImg.1 hq
    have h1 := (C.coord.ker (resU Xs C.hU x u * u⁻¹)).2 (hfix u (mem_liftFix.2 ⟨u.2, hu'⟩))
    rw [map_mul, map_inv, mul_inv_eq_one] at h1
    rw [gOf_apply]
    have h2 : C.indQ x (C.c u) = C.c u := by
      change indHom C.coord Xs C.hU C.hZ x (C.c u) = C.c u
      rw [indHom_apply]
      exact h1
    rw [hu] at h2
    rw [h2]
    rfl
  obtain ⟨s, hxs, hs⟩ := C.exists_theta_of_linear hx (C.linear_of_fix hfix')
  have h1 : (s : Matrix (Fin 2) (Fin 2) F) *ᵥ ![1, 0] = ![1, 0] := by
    rw [← hs, hfix' 1]
  have h00 : (s : Matrix (Fin 2) (Fin 2) F) 0 0 = 1 := by
    have := congrFun h1 0
    simpa [Matrix.mulVec, dotProduct, Fin.sum_univ_two] using this
  have h10 : (s : Matrix (Fin 2) (Fin 2) F) 1 0 = 0 := by
    have := congrFun h1 1
    simpa [Matrix.mulVec, dotProduct, Fin.sum_univ_two] using this
  have hdet : (s : Matrix (Fin 2) (Fin 2) F).det = 1 := s.2
  rw [Matrix.det_fin_two, h00, h10] at hdet
  have h11 : (s : Matrix (Fin 2) (Fin 2) F) 1 1 = 1 := by simpa using hdet
  have hs' : s = S2.uSL ((s : Matrix (Fin 2) (Fin 2) F) 0 1) := by
    apply Subtype.ext
    ext i j
    fin_cases i <;> fin_cases j <;> simp [S2.uSL, h00, h10, h11]
  rw [hxs]
  exact C.mem_Kroot.2 ⟨_, by rw [← hs']; rfl⟩

end L2Ctx

end CFSG.Quasithin.C124.YL
