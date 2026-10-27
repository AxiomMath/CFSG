module

public import CFSG.OddTranspositions.PartThree.Twelve.TenFiveMultModels
public import CFSG.LocalAnalysis.ComponentClassification.GSThmBCatalog516CSpin
public import CFSG.LieType.Universal.SpinClause0
public import CFSG.LieType.Universal.SpinOmega.Kernel
public import CFSG.LieType.Universal.SpinOmega.Center
public import CFSG.LieType.Steinberg.CentralExt.OrthogonalPerfect
public import CFSG.LieType.Steinberg.CentralExt.POmegaOddMultiplier
public import CFSG.LieType.Steinberg.CentralExt.POmegaPlusMultiplier
public import CFSG.LieType.Steinberg.CentralExt.SpinPlusCentrallyClosed
public import CFSG.LieType.Steinberg.CentralExt.SpinMinusCentrallyClosed

public section

namespace CFSG.OddTranspositions.PartThree

open Matrix CFSG.Open CFSG.LieType.Universal.Spin

section Generic

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]

theorem reflect_smul_of_ne_zero (Q : QuadraticForm K V) {a : V} (ha : Q a ≠ 0) {c : K}
    (hc : c ≠ 0) : CFSG.ClassicalGroups.Orthogonal.reflect Q (c • a) =
      CFSG.ClassicalGroups.Orthogonal.reflect Q a := by
  let _ : Invertible (Q a) := invertibleOfNonzero ha
  let _ : Invertible c := invertibleOfNonzero hc
  let _ : Invertible (Q (c • a)) := by
    rw [QuadraticMap.map_smul]
    let _ : Invertible (c * c) := invertibleMul c c
    exact invertibleMul (c * c) (Q a)
  have h := TauCeti.QuadraticMap.reflection_smul_eq (Q := Q) (v := a) c
  calc CFSG.ClassicalGroups.Orthogonal.reflect Q (c • a)
      = TauCeti.QuadraticMap.reflection Q (c • a) :=
        CFSG.ClassicalGroups.Orthogonal.reflect_eq_reflection
    _ = TauCeti.QuadraticMap.reflection Q a := h
    _ = CFSG.ClassicalGroups.Orthogonal.reflect Q a :=
        CFSG.ClassicalGroups.Orthogonal.reflect_eq_reflection.symm

end Generic

section Model

theorem modelReflect_eq {ι : Type} [Fintype ι] [DecidableEq ι]
    {Q : QuadraticForm (ZMod 5) (ι → ZMod 5)} {Q₀ : (ι → ZMod 5) → ZMod 5} (hcoe : ⇑Q = Q₀)
    {a : ι → ZMod 5} (ha : Q a ≠ 0) (v : ι → ZMod 5) :
    modelReflect Q₀ a v = v - (QuadraticMap.polar Q a v / Q a) • a := by
  rw [modelReflect]
  have hs : (Q₀ (v + a) - Q₀ v - Q₀ a) * (Q₀ a)⁻¹ = QuadraticMap.polar Q a v / Q a := by
    rw [QuadraticMap.polar, ← hcoe, add_comm v a]
    field_simp
    abel
  rw [hs]

end Model

end CFSG.OddTranspositions.PartThree
