module

public import CFSG.LocalAnalysis.StandardType.GGQTwoLMMod
import CFSG.LocalAnalysis.StandardType.GGQTwoLMModHmAuxB

public section

namespace CFSG.StandardType.QTwo

open CFSG.StandardType CFSG.Blueprint CFSG.Open CFSG.StandardType.UCoord

theorem qTwoLMSkel_isHmModel_card {m : ℕ} (h3 : 3 ∣ m) {V : Type} [Group V]
    {ρ : Equiv.Perm (Fin m) →* MulAut V} (h : IsHmModel m h3 V ρ) :
    Nat.card V = 3 ^ (m - 2) :=
  qTwoLMH_card_of_model h3 h

theorem qTwoLMSkel_isHmModel_fixed {m : ℕ} (h3 : 3 ∣ m) {V : Type} [Group V]
    {ρ : Equiv.Perm (Fin m) →* MulAut V} (h : IsHmModel m h3 V ρ) (hm : 5 ≤ m) :
    ∀ v : V, (∀ σ, ρ σ v = v) → v = 1 :=
  qTwoLMH_fixed h3 h hm

theorem qTwoLMSkel_isHmModel_comm {m : ℕ} (h3 : 3 ∣ m) {V : Type} [Group V]
    {ρ : Equiv.Perm (Fin m) →* MulAut V} (h : IsHmModel m h3 V ρ) :
    Subgroup.closure {w : V | ∃ σ v, w = ρ σ v * v⁻¹} = ⊤ :=
  qTwoLMH_comm h3 h

theorem qTwoLMSkel_isHmModel_faithful {m : ℕ} (h3 : 3 ∣ m) {V : Type} [Group V]
    {ρ : Equiv.Perm (Fin m) →* MulAut V} (h : IsHmModel m h3 V ρ) (hm : 5 ≤ m) :
    ∀ σ, (∀ v, ρ σ v = v) → σ = 1 :=
  qTwoLMH_faithful h3 h hm

theorem qTwoLMSkel_isHmModel_transposition {m : ℕ} (h3 : 3 ∣ m) {V : Type} [Group V]
    {ρ : Equiv.Perm (Fin m) →* MulAut V} (h : IsHmModel m h3 V ρ) (a b : Fin m) (hab : a ≠ b) :
    ρ (Equiv.swap a b) ^ 2 = 1 ∧ Nat.card {v : V // ρ (Equiv.swap a b) v = v} * 3 = Nat.card V :=
  ⟨by rw [sq, ← map_mul, Equiv.swap_mul_self, map_one], qTwoLMH_fix_swap_card h3 h a b hab⟩

end CFSG.StandardType.QTwo

end
