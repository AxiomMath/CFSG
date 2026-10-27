module

public import CFSG.SignalizerFunctorTheorem.McBride.Nonsolv.Sec6.Basic

public section

open CFSG.Open

universe u

namespace CFSG.SignalizerFunctorTheorem.McBride.Nonsolv

namespace Counterexample

variable {p : ℕ} {G : Type u} [Group G] [Finite G] {A : Subgroup G} {θ : G → Subgroup G}

theorem kSetting_apply (h : Counterexample p A θ) {a : G} (ha : a ∈ A) (ha1 : a ≠ 1) :
    KSetting p A (θ a) :=
  ⟨h.prime, h.elemAbelian, h.isFunctor.normalized a ha ha1, h.hypC a ha ha1⟩

theorem ne_bot_of_mem_E2 (h : Counterexample p A θ) {B : Subgroup G}
    (hB : B ∈ signalizerFunctorEk p 2 A) : B ≠ ⊥ := by
  rintro rfl
  have h1 := hB.2
  rw [Subgroup.card_bot] at h1
  exact absurd h1.symm (Nat.one_lt_pow (by norm_num) h.prime.one_lt).ne'

theorem isElemAbelian_of_mem_E2 (h : Counterexample p A θ) {B : Subgroup G}
    (hB : B ∈ signalizerFunctorEk p 2 A) : IsElemAbelian p B :=
  h.isElemAbelian_of_le hB.1

end Counterexample

end CFSG.SignalizerFunctorTheorem.McBride.Nonsolv
