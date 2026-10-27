module

public import CFSG.LocalAnalysis.StandardType.PhanEStdE6
public import CFSG.LocalAnalysis.StandardType.PhanEStdGeom
public import CFSG.LieType.Steinberg.Minuscule.BruhatExtras

public section

namespace CFSG.ClassicalInvolution.Phan.PhanE

open CFSG.Blueprint.Chevalley CFSG.LieType.Universal CFSG.LieType.CurtisTits
  CFSG.LieType.RootSystem CFSG.LieType.Steinberg CFSG.LieType.Steinberg.Minuscule
  CFSG.LieType.Steinberg.TwistedE6 CFSG.Timmesfeld

theorem e6_hsl_aux :
    ∀ i j : Fin 6, i ≠ j → CoxeterMatrix.E₆ i j = 2 ∨ CoxeterMatrix.E₆ i j = 3 := by
  intro i j hij
  fin_cases i <;> fin_cases j <;> simp_all [CoxeterMatrix.E₆]

variable (k : Type) [Field k] [Finite k] [CharP k 2]

theorem e6_hsl : ∀ i j : Fin (e6Datum k).rank, i ≠ j →
    coxeterMatrix (e6Datum k).isFiniteType i j = 2 ∨
      coxeterMatrix (e6Datum k).isFiniteType i j = 3 := by
  intro i j hij
  rw [coxeterMatrix_e6Datum k]
  exact e6_hsl_aux i j hij

variable {k} (θ : k →+* k) (hθ : ∀ c, θ (θ c) = c)

@[expose] noncomputable def e6StdInput (hθne : ∃ c, θ c ≠ c)
    (hnorm : ∀ s : k, s ≠ 0 → θ s = s → ∃ a : k, a * θ a = s) :
    StdInput (e6Datum k) (e6Data_valid.nm k) (e6Data_valid.torus k) where
  w₀ := e6W0 k
  hct := e6Datum_isCTGroupDatum k
  F := e6Frob θ hθ
  hext := e6Datum_steinbergExtras k
  hw₀ := e6W0_isLongest k
  hsq := fun i => e6_nm_mul_self i
  hBU := e6Datum_bruhatExtras k
  L := e6StdLevi θ hθ hnorm
  R := e6RankOne θ hθ hθne
  hsl := e6_hsl k

end CFSG.ClassicalInvolution.Phan.PhanE
