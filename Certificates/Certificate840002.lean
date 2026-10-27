module

public import CFSG.CGT.Hall82.DModelFacts
import Certificates.Kernel.Hall82K.DAGlue

public section

namespace Certificates

open CFSG.KD.Hall82A

open CFSG.CGT.Hall82 CFSG.ComponentClassification.AS81.Hexa in
open CFSG.ComponentClassification.AS81.HeTri CFSG.Monster.B.Co2 in
theorem certificate840002 :
    (∀ x ∈ hexaM, ∀ v w, x (xorF v w) = xorF (x v) (x w)) ∧
      (∀ h h', IsOvalVec h → IsOvalVec h' → ∃ a ∈ hexaL, a h = h') ∧
      (∀ v, v ≠ 0 → ¬ IsOvalVec v → ∃ a ∈ hexaL, a 5 = v) ∧
      ¬ IsOvalVec 5 ∧
      (∀ h, IsOvalVec h → Nat.card (stabSub hexaM h) = 120) ∧
      (∀ v, v ≠ 0 → ¬ IsOvalVec v → Nat.card (stabSub hexaM v) = 48) ∧
      (∀ h, IsOvalVec h → Nat.card (stabSub hexaL h) = 60) ∧
      (∀ v, v ≠ 0 → ¬ IsOvalVec v → Nat.card (stabSub hexaL v) = 24) ∧
      (∀ h, IsOvalVec h → ∀ B : Subgroup (Equiv.Perm (Fin 64)), B ≤ hexaM →
        IsPGroup 2 B → (∀ b ∈ B, b h = h) →
        (∀ a ∈ hexaL, a h = h → ∀ b ∈ B, a * b * a⁻¹ ∈ B) → B = ⊥) ∧
      (∀ v, heZeta v = v → v = 0) :=
  ⟨lin, oval_trans, five_trans, five_not_oval, card_stab_oval, card_stab, card_stabL_oval,
    card_stabL, eq_bot_of_oval, zeta_fix⟩

end Certificates
