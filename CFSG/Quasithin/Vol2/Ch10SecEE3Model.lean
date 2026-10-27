module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.A5.Delta5

public section

namespace CFSG.Quasithin.Vol2.Ch10.SecE

open CFSG.QuasithinUnique.A5.Delta5 Equiv

@[expose] def sA : Perm (Fin 5) := swap 0 1

@[expose] def sB : Perm (Fin 5) := swap 2 3

@[expose] def fixCount (b₁ b₂ b₃ : Bool) : ℕ :=
  (Finset.univ.filter fun x : Fin 5 → ZMod 2 => isEven x ∧ (b₁ = true → pact sA x = x) ∧
    (b₂ = true → pact sB x = x) ∧ (b₃ = true → pact (sA * sB) x = x)).card

@[expose] def selCard (b₁ b₂ b₃ : Bool) : ℕ := 1 + b₁.toNat + b₂.toNat + b₃.toNat

@[expose] def SelClosed (b₁ b₂ b₃ : Bool) : Prop :=
  (b₁ = true → b₂ = true → b₃ = true) ∧ (b₁ = true → b₃ = true → b₂ = true) ∧
    (b₂ = true → b₃ = true → b₁ = true)

instance (b₁ b₂ b₃ : Bool) : Decidable (SelClosed b₁ b₂ b₃) := by
  unfold SelClosed; infer_instance

theorem card_mul_fixCount_le : ∀ b₁ b₂ b₃ : Bool, SelClosed b₁ b₂ b₃ →
    selCard b₁ b₂ b₃ * fixCount b₁ b₂ b₃ ≤ 16 := by
  decide +kernel

theorem card_mul_fixCount_eq_iff : ∀ b₁ b₂ b₃ : Bool, SelClosed b₁ b₂ b₃ →
    (selCard b₁ b₂ b₃ * fixCount b₁ b₂ b₃ = 16 ↔ (b₃ = true → b₁ = true)) := by
  decide +kernel

theorem card_evenWeight : (Finset.univ.filter fun x : Fin 5 → ZMod 2 => isEven x).card = 16 := by
  decide +kernel

end CFSG.Quasithin.Vol2.Ch10.SecE
