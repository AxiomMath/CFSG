module

public import CFSG.Permutation.FiveTransitive.Degree24FiveCode

public section

namespace CFSG

namespace FiveTransitive.Degree25

open FiveTransitive.Degree24

@[expose] def standardFiveCode :
    Submodule (ZMod 5) FiveVector where
  carrier := {v | ∑ i, v i = 0}
  zero_mem' := by simp
  add_mem' := by
    intro u v hu hv
    change (∑ i, u i) = 0 at hu
    change (∑ i, v i) = 0 at hv
    change (∑ i, (u + v) i) = 0
    simp [Pi.add_apply, Finset.sum_add_distrib, hu, hv]
  smul_mem' := by
    intro a v hv
    change (∑ i, v i) = 0 at hv
    change (∑ i, (a • v) i) = 0
    simp only [Pi.smul_apply, smul_eq_mul]
    rw [← Finset.mul_sum, hv, mul_zero]

@[expose] def standardFiveCodeVector
    (v : Fin 3 → ZMod 5) :
    FiveVector :=
  ![v 0, v 1, v 2, -(v 0 + v 1 + v 2)]

@[expose] def standardFiveCodeDot
    (c v : Fin 3 → ZMod 5) :
    ZMod 5 :=
  ∑ i, c i * v i

@[expose] def standardFiveCodeShear
    (l c v : Fin 3 → ZMod 5) :
    Fin 3 → ZMod 5 :=
  v + standardFiveCodeDot c v • l

theorem standardFiveCode_no_weight_preserving_transvection :
    ∀ l c : Fin 3 → ZMod 5,
      l ≠ 0 →
      c ≠ 0 →
      standardFiveCodeDot c l = 0 →
      ¬∀ v : Fin 3 → ZMod 5,
        fiveWeight
            (standardFiveCodeVector
              (standardFiveCodeShear l c v)) =
          fiveWeight (standardFiveCodeVector v) := by
  decide +kernel

end FiveTransitive.Degree25

end CFSG
