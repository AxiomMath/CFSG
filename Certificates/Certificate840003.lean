module

public import CFSG.CGT.Hall82.DModelFacts
import Certificates.Kernel.Hall82K.RmGlue

public section

namespace Certificates

open CFSG.KD.Hall82R

open CFSG.CGT.Hall82 CFSG.ComponentClassification.AS81.Hexa in
theorem certificate840003 :
    (∀ e f, hallRMPerm e * hallRMPerm f = hallRMPerm (xor8 e f)) ∧
      Function.Injective hallRMPerm ∧
      (∀ x, x ∈ hallRM ↔ ∃ e, hallRMPerm e = x) ∧
      hallRM ≤ hexaM ∧
      (∀ e, hallRMPerm e 5 = 5) ∧
      ¬ hallRM ≤ hexaL ∧
      (∀ B : Subgroup (Equiv.Perm (Fin 64)), B ≤ hexaM → IsPGroup 2 B → (∀ b ∈ B, b 5 = 5) →
        (∀ a ∈ hexaL, a 5 = 5 → ∀ b ∈ B, a * b * a⁻¹ ∈ B) → B ≤ hallRM) ∧
      (∀ B : Subgroup (Equiv.Perm (Fin 64)), B ≤ hallRM →
        (∀ a ∈ hexaL, a 5 = 5 → ∀ b ∈ B, a * b * a⁻¹ ∈ B) →
        hallRM ≤ B ∨ ∀ a ∈ B, ∀ b ∈ B, ∀ v, xorF (xorF (a (b v)) (a v)) (xorF (b v) v) = 0) ∧
      (∀ s ∈ hexaM, s 5 = 5 → ∀ v, InHallU v → InHallU (s v)) ∧
      (∀ e v, InHallU v → xorF (hallRMPerm e v) v = 0 ∨ xorF (hallRMPerm e v) v = 5) ∧
      (∀ e, (∀ v, InHallU v → hallRMPerm e v = v) → e = 0) ∧
      (∀ v, (∀ e, hallRMPerm e v = v) → v = 0 ∨ v = 5) ∧
      (∀ W : Set (Fin 64), (∀ v ∈ W, ∀ w ∈ W, xorF v w ∈ W) → (∀ v, InHallU v → v ∈ W) →
        (∀ a ∈ hexaL, a 5 = 5 → ∀ w ∈ W, a w ∈ W) → W = {v | InHallU v} ∨ W = Set.univ) :=
  ⟨rm_mul, rm_inj, mem_rm_iff, rm_le, rm_fix, rm_not_le, le_rm, rm_le_or_quad, u_inv,
    rm_comm_u, rm_eq_zero_of_fix_u, fix_rm, u_maximal⟩

end Certificates
