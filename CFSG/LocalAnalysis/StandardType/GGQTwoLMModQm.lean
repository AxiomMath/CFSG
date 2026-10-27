module

public import CFSG.LocalAnalysis.StandardType.GGQTwoLMMod
import CFSG.LocalAnalysis.StandardType.GGQTwoLMModHmAuxQm

public section

namespace CFSG.StandardType.QTwo

open CFSG.StandardType CFSG.Blueprint CFSG.Open CFSG.StandardType.UCoord

theorem qTwoLMSkel_isQmModel_card {m : ℕ} {V : Type} [Group V]
    {ρ : Equiv.Perm (Fin m) →* MulAut V} (h : IsQmModel m V ρ) :
    Nat.card V = 3 ^ (m - 1) :=
  qTwoLMH_card_of_qmodel h

theorem qTwoLMSkel_isQmModel_fixed {m : ℕ} {V : Type} [Group V]
    {ρ : Equiv.Perm (Fin m) →* MulAut V} (h : IsQmModel m V ρ) (h3 : 3 ∣ m) (hm : 5 ≤ m) :
    ∀ v : V, (∀ σ, ρ σ v = v) → v = 1 :=
  qTwoLMH_fixed_qmodel h h3 hm

theorem qTwoLMSkel_isQmModel_faithful {m : ℕ} {V : Type} [Group V]
    {ρ : Equiv.Perm (Fin m) →* MulAut V} (h : IsQmModel m V ρ) (hm : 5 ≤ m) :
    ∀ σ, (∀ v, ρ σ v = v) → σ = 1 :=
  qTwoLMH_faithful_qmodel h hm

theorem qTwoLMSkel_isQmModel_transposition {m : ℕ} {V : Type} [Group V]
    {ρ : Equiv.Perm (Fin m) →* MulAut V} (h : IsQmModel m V ρ) (a b : Fin m) (hab : a ≠ b) :
    ρ (Equiv.swap a b) ^ 2 = 1 ∧ Nat.card {v : V // ρ (Equiv.swap a b) v = v} * 3 = Nat.card V :=
  ⟨by rw [sq, ← map_mul, Equiv.swap_mul_self, map_one], qTwoLMH_fix_swap_card_qmodel h a b hab⟩

end CFSG.StandardType.QTwo

end
