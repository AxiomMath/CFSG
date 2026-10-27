module

public import CFSG.LocalAnalysis.StandardType.PhanEStdE7
public import CFSG.LocalAnalysis.StandardType.PhanEStdGeom
public import CFSG.LieType.Steinberg.Minuscule.BruhatExtras

public section

namespace CFSG.ClassicalInvolution.Phan.PhanE

open CFSG.Blueprint.Chevalley CFSG.LieType.Universal CFSG.LieType.CurtisTits
  CFSG.LieType.RootSystem CFSG.LieType.Steinberg CFSG.LieType.Steinberg.Minuscule
  CFSG.HardMathSupport.Timmesfeld.CrossChar CFSG.Timmesfeld

theorem e7_hsl_aux :
    ∀ i j : Fin 7, i ≠ j → CoxeterMatrix.E₇ i j = 2 ∨ CoxeterMatrix.E₇ i j = 3 := by
  intro i j hij
  fin_cases i <;> fin_cases j <;> simp_all [CoxeterMatrix.E₇]

variable (k : Type) [Field k] [Finite k] [CharP k 2]

theorem e7_hsl : ∀ i j : Fin (e7Datum k).rank, i ≠ j →
    coxeterMatrix (e7Datum k).isFiniteType i j = 2 ∨
      coxeterMatrix (e7Datum k).isFiniteType i j = 3 := by
  intro i j hij
  rw [coxeterMatrix_e7Datum k]
  exact e7_hsl_aux i j hij

variable {k} (θ : k →+* k) (hθ : ∀ c, θ (θ c) = c)

@[expose] noncomputable def e7StdInput (hθne : ∃ c, θ c ≠ c)
    (hnorm : ∀ s : k, s ≠ 0 → θ s = s → ∃ a : k, a * θ a = s) :
    StdInput (e7Datum k) (e7Data_valid.nm k) (e7Data_valid.torus k) where
  w₀ := e7W0 k
  hct := e7Datum_isCTGroupDatum k
  F := e7Frob θ hθ
  hext := e7Datum_steinbergExtras k
  hw₀ := e7W0_isLongest k
  hsq := fun i => e7_nm_mul_self i
  hBU := e7Datum_bruhatExtras k
  L := e7StdLevi θ hθ hnorm
  R := e7RankOne θ hθ hθne
  hsl := e7_hsl k

end CFSG.ClassicalInvolution.Phan.PhanE
