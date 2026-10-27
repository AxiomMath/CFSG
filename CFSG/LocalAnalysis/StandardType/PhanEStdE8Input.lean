module

public import CFSG.LocalAnalysis.StandardType.PhanEStdE8
public import CFSG.LocalAnalysis.StandardType.PhanEStdGeom

public section

namespace CFSG.ClassicalInvolution.Phan.PhanE

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Universal CFSG.LieType.CurtisTits
  CFSG.LieType.RootSystem CFSG.LieType.Steinberg CFSG.LieType.Steinberg.Adjoint

theorem e8_hsl_aux :
    ∀ i j : Fin 8, i ≠ j → CoxeterMatrix.E₈ i j = 2 ∨ CoxeterMatrix.E₈ i j = 3 := by
  intro i j hij
  fin_cases i <;> fin_cases j <;> simp_all [CoxeterMatrix.E₈]

variable (k : Type) [Field k] [Finite k] [CharP k 2]

theorem e8_hsl : ∀ i j : Fin (e8Datum k).rank, i ≠ j →
    coxeterMatrix (e8Datum k).isFiniteType i j = 2 ∨
      coxeterMatrix (e8Datum k).isFiniteType i j = 3 := by
  intro i j hij
  rw [coxeterMatrix_e8Datum k]
  exact e8_hsl_aux i j hij

variable {k} (θ : k →+* k) (hθ : ∀ c, θ (θ c) = c)

@[expose] noncomputable def e8StdInput (hθne : ∃ c, θ c ≠ c)
    (hnorm : ∀ s : k, s ≠ 0 → θ s = s → ∃ a : k, a * θ a = s) :
    StdInput (e8Datum k) (CFSG.LieType.Chevalley.weylElement .E8 k)
      (Adjoint.torus (τ := .E8) k) where
  w₀ := e8W0 k
  hct := e8_isCTGroupDatum k
  F := e8Frob θ hθ
  hext := e8_steinbergExtras k
  hw₀ := e8W0_isLongest k
  hsq := fun i => e8_nm_mul_self i
  hBU := e8_bruhatExtras k
  L := e8StdLevi θ hθ hnorm
  R := e8RankOne θ hθ hθne
  hsl := e8_hsl k

end CFSG.ClassicalInvolution.Phan.PhanE
