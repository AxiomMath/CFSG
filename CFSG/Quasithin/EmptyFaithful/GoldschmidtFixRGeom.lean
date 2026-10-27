module

public import Mathlib.Data.Matrix.Basic
public import Mathlib.Data.Nat.Totient
public import Mathlib.Data.Sym.Sym2.Init
public import Mathlib.Tactic.ContinuousFunctionalCalculus
public import Mathlib.Tactic.NormNum.GCD

public section

namespace CFSG.Quasithin.FixR

abbrev Vec : Type := Fin 2 → ZMod 5

@[expose] def det2 (u v : Vec) : ZMod 5 := u 0 * v 1 - u 1 * v 0

set_option maxRecDepth 100000 in
set_option synthInstance.maxSize 4096 in
set_option synthInstance.maxHeartbeats 400000 in
theorem exists_fixed_vec :
    ∀ M : Matrix (Fin 2) (Fin 2) (ZMod 5), M ^ 5 = 1 → M ≠ 1 →
      ∃ u : Vec, u ≠ 0 ∧ M.mulVec u = u := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option synthInstance.maxSize 4096 in
set_option synthInstance.maxHeartbeats 400000 in
theorem orbit_indep :
    ∀ M : Matrix (Fin 2) (Fin 2) (ZMod 5), M ^ 5 = 1 → M ≠ 1 →
      ∀ u₀ : Vec, u₀ ≠ 0 → M.mulVec u₀ = u₀ → ∀ u : Vec, det2 u₀ u ≠ 0 →
        det2 u (M.mulVec u) ≠ 0 ∧ det2 u (M.mulVec (M.mulVec u)) ≠ 0 ∧
        det2 u (M.mulVec (M.mulVec (M.mulVec u))) ≠ 0 ∧
        det2 (M.mulVec u) (M.mulVec (M.mulVec u)) ≠ 0 ∧
        det2 (M.mulVec u) (M.mulVec (M.mulVec (M.mulVec u))) ≠ 0 ∧
        det2 (M.mulVec (M.mulVec u)) (M.mulVec (M.mulVec (M.mulVec u))) ≠ 0 := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option synthInstance.maxSize 4096 in
set_option synthInstance.maxHeartbeats 400000 in
theorem exists_indep : ∀ u₀ : Vec, u₀ ≠ 0 → ∃ u₁ : Vec, det2 u₀ u₁ ≠ 0 := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option synthInstance.maxSize 4096 in
set_option synthInstance.maxHeartbeats 400000 in
theorem two_four :
    ∀ M : Matrix (Fin 2) (Fin 2) (ZMod 5), M * M = 1 → M ≠ 1 → M ≠ -1 →
      ∀ N : Matrix (Fin 2) (Fin 2) (ZMod 5), N * N = 1 → M * N = N * M →
        N = 1 ∨ N = -1 ∨ N = M ∨ N = -M := by
  decide +kernel

end CFSG.Quasithin.FixR
