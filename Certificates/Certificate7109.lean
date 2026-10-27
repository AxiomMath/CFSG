module

public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
public import Mathlib.Data.ZMod.Defs
public import Mathlib.SetTheory.Cardinal.Finite
import CFSG.Certificates.Kernel.C7109.Glue
import Certificates.Kernel.C7109.Checks

public section

namespace Certificates

open CertificateChecks

open scoped Matrix in
theorem certificate7109 :
    (∀ S : Subgroup (GL (Fin 5) (ZMod 2)), (∀ x ∈ S, ∀ y ∈ S, x * y = y * x) →
      (∀ x ∈ S, x * x = 1) → 2 ^ 5 ≤ Nat.card S →
      (Nat.card {v : Fin 5 → ZMod 2 | ∀ g ∈ S, (g : Matrix (Fin 5) (Fin 5) (ZMod 2)) *ᵥ v = v} = 4 ∧
        Nat.card {v : Fin 5 → ZMod 2 |
          ∀ g ∈ S, (g : Matrix (Fin 5) (Fin 5) (ZMod 2))ᵀ *ᵥ v = v} = 8) ∨
      (Nat.card {v : Fin 5 → ZMod 2 | ∀ g ∈ S, (g : Matrix (Fin 5) (Fin 5) (ZMod 2)) *ᵥ v = v} = 8 ∧
        Nat.card {v : Fin 5 → ZMod 2 |
          ∀ g ∈ S, (g : Matrix (Fin 5) (Fin 5) (ZMod 2))ᵀ *ᵥ v = v} = 4)) ∧
    (∀ S : Subgroup (GL (Fin 5) (ZMod 2)), (∀ x ∈ S, ∀ y ∈ S, x * y = y * x) →
      (∀ x ∈ S, x * x = 1) → 2 ^ 4 ≤ Nat.card S →
      ∀ P : Matrix (Fin 5) (Fin 5) (ZMod 2), Pᵀ = P → P.det ≠ 0 →
      ∃ g ∈ S, (g : Matrix (Fin 5) (Fin 5) (ZMod 2)) * P *
        (g : Matrix (Fin 5) (Fin 5) (ZMod 2))ᵀ ≠ P) :=
  CFSG.KC.C7109.Glue.certificate_of_checks KernelC7109.c7109_recs KernelC7109.c7109_compl
    KernelC7109.c7109_walk

end Certificates
