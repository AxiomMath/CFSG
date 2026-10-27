module

public import CFSG.SignalizerFunctorTheorem.McBride.Defs

public section

open CFSG.Open

universe u

namespace CFSG.SignalizerFunctorTheorem.McBride.Near

structure NearHyp (p : ℕ) {G : Type*} [Group G] (A : Subgroup G) (θ : G → Subgroup G) : Prop where
  prime : p.Prime
  odd : p ≠ 2
  elemAbelian : IsElemAbelian p A
  card : Nat.card A = p ^ 3
  isFunctor : IsFunctor p A θ
  near : ∀ a ∈ A, a ≠ 1 → NearASolvable p A (θ a)

structure Counterexample (p : ℕ) {G : Type u} [Group G] [Finite G] (A : Subgroup G)
    (θ : G → Subgroup G) : Prop where
  hyp : NearHyp p A θ
  notComplete : ¬ IsCompleteIn (signalizers p A θ (NearASolvable p A))
  ih : ∀ (H : Type u) [Group H] [Finite H], Nat.card H < Nat.card G →
    ∀ (A' : Subgroup H) (θ' : H → Subgroup H), NearHyp p A' θ' →
      IsCompleteIn (signalizers p A' θ' (NearASolvable p A'))
  minimal : ∀ θ' : G → Subgroup G, NearHyp p A θ' →
    ¬ IsCompleteIn (signalizers p A θ' (NearASolvable p A)) → size A θ ≤ size A θ'

namespace Counterexample

variable {p : ℕ} {G : Type u} [Group G] [Finite G] {A : Subgroup G} {θ : G → Subgroup G}

theorem complete_of_size_lt (h : Counterexample p A θ) {θ' : G → Subgroup G}
    (hθ' : NearHyp p A θ') (hlt : size A θ' < size A θ) :
    IsCompleteIn (signalizers p A θ' (NearASolvable p A)) := by
  by_contra hnc
  exact absurd (h.minimal θ' hθ' hnc) (not_le.mpr hlt)

end Counterexample

end CFSG.SignalizerFunctorTheorem.McBride.Near
