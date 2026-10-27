module

public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.Quasithin.Background.GoldschmidtS146PPerf

public section

namespace CFSG.Quasithin

open scoped Pointwise commutatorElement

namespace SBc17

@[expose] def sylowOfIndex {G : Type*} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]
    (H : Subgroup G) (hH : IsPGroup p H) (hi : ¬ p ∣ H.index) : Sylow p G where
  toSubgroup := H
  isPGroup' := hH
  is_maximal' := by
    intro Q hQ hHQ
    have hrel : H.relIndex Q ∣ H.index := ⟨Q.index, (Subgroup.relIndex_mul_index hHQ).symm⟩
    obtain ⟨n, hn⟩ := hQ.index (H.subgroupOf Q)
    have hn' : H.relIndex Q = p ^ n := hn
    have hn0 : n = 0 := by
      by_contra hne
      exact hi ((dvd_pow_self p hne).trans (hn' ▸ hrel))
    have : H.relIndex Q = 1 := by rw [hn', hn0, pow_zero]
    exact le_antisymm (Subgroup.relIndex_eq_one.mp this) hHQ

end SBc17

end CFSG.Quasithin
