module

public import CFSG.LocalAnalysis.StandardType.GGQTwoDL1LocalO
public import CFSG.LocalAnalysis.StandardType.GGQTwoDOrthMemberPair

public section

namespace CFSG.StandardType.QTwo

open CFSG.ClassicalInvolution.Phan

private theorem pmoop_eq_one_of_isReflection_one {G : Type} [Group G] [Finite G]
    {Bs : Subgroup G} {r : MulAut ↥Bs} (hr : GGIsReflection 1 r) : r = 1 := by
  ext b
  by_contra hb
  have hb' : ¬ r b = b := by simpa using hb
  have hlt := Finite.card_subtype_lt (α := ↥Bs) (p := fun x : ↥Bs => r x = x) (x := b) hb'
  have h := hr.2
  rw [mul_one] at h
  omega

theorem qtwoDL1OrthPair_holds : QTwoDL1OrthPair := by
  intro G _ _ p Bs X Φ hF _hZ r hrX hr r' hr'X hr' hnc
  have hp3 : p ∣ 3 := by
    have h := Φ.hpq
    rwa [hF] at h
  rcases (Nat.dvd_prime Nat.prime_three).mp hp3 with rfl | rfl
  · exact absurd (by rw [pmoop_eq_one_of_isReflection_one hr, one_mul, mul_one]) hnc
  · haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
    obtain ⟨hpair, hcard⟩ := qtwoOrth_pair_card_core Φ hF hrX hr'X hr hr' hnc
    exact ⟨ggRankTwoIn X Bs r r', ggOTwoPrime_le _, hpair, hcard⟩

end CFSG.StandardType.QTwo

end
