module

public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
import Certificates.Kernel.GL33K.Glue

public section

namespace Certificates

theorem certificate1255001 : ∀ W : Subgroup (Matrix.GeneralLinearGroup (Fin 3) (ZMod 3)),
    (∀ B : AddSubgroup (Fin 3 → ZMod 3),
      (∀ w ∈ W, ∀ b ∈ B, Matrix.mulVec (w : Matrix (Fin 3) (Fin 3) (ZMod 3)) b ∈ B) →
        B = ⊥ ∨ B = ⊤) →
    (∃ Bi : Fin 3 → AddSubgroup (Fin 3 → ZMod 3), (∀ i, Nat.card (Bi i) = 3) ∧ (⨆ i, Bi i) = ⊤ ∧
        (∀ w ∈ W, ∀ i, ∃ j, ∀ v ∈ Bi i,
          Matrix.mulVec (w : Matrix (Fin 3) (Fin 3) (ZMod 3)) v ∈ Bi j) ∧
        Nat.card W ∣ 48) ∨
      (∃ U : Subgroup (Matrix.GeneralLinearGroup (Fin 3) (ZMod 3)), U ≤ W ∧
        (U.subgroupOf W).Normal ∧ Nat.card U = 13) ∨
      (∃ U : Subgroup (Matrix.GeneralLinearGroup (Fin 3) (ZMod 3)), U ≤ W ∧
        (U.subgroupOf W).Normal ∧ Nonempty (U ≃* Matrix.SpecialLinearGroup (Fin 3) (ZMod 3))) :=
  fun _ hW => CFSG.KD.GL33K.gfacts.sixSevenGL hW

end Certificates
