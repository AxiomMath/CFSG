module

public import CFSG.Quasithin.EmptyFaithful.S153ZLd
public import CFSG.Quasithin.Background.F918P8C

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.Assembly.LowTwoRank CFSG.QuasithinUnique

@[expose] def D391V : Prop :=
  ∀ (W : Type) [CommGroup W] [Finite W] (M Mp T L : Subgroup (MulAut W)) (V : Subgroup W),
    Mp = L → D3Std M Mp T L V → qhatOf M ≤ ((2 : ℚ) : WithTop ℚ) → V = orbSup T V →
    ∀ A : Subgroup (MulAut W), IsA2 M A → A ≤ T → commSeries A 3 = ⊥ → rAV A ≤ 2 →
      (∀ a ∈ A, (∀ x ∈ Mp, a * x = x * a) → a = 1) →
      orbSup T V = ⊤ ∨ IsFFModule (autSec (L ⊔ T) V (fixV Mp))

@[expose] def D391Deep : Prop :=
  ∀ (W : Type) [CommGroup W] [Finite W] (M Mp T L : Subgroup (MulAut W)) (V : Subgroup W),
    Mp = L → D3Std M Mp T L V → qhatOf M ≤ ((2 : ℚ) : WithTop ℚ) →
    (V = commSub V L ∧ commSub V L < commSub (orbSup T V) L) →
    ∀ A : Subgroup (MulAut W), IsA2 M A → A ≤ T → commSeries A 3 = ⊥ → rAV A ≤ 2 →
      (∀ a ∈ A, (∀ x ∈ Mp, a * x = x * a) → a = 1) →
      orbSup T V = ⊤

theorem d391L_of_pieces (hV : D391V) (hD : D391Deep) : D391L := by
  intro W _ _ M Mp T L V hMp hstd hqM hcase A hA1 hA2 hA3 hA4 hA5
  rcases hcase with hVT | hdeep
  · rcases hV W M Mp T L V hMp hstd hqM hVT A hA1 hA2 hA3 hA4 hA5 with h | h
    · exact Or.inl h
    · exact Or.inr ⟨hVT, h⟩
  · exact Or.inl (hD W M Mp T L V hMp hstd hqM hdeep A hA1 hA2 hA3 hA4 hA5)

theorem d310Deep_of_unfaithfulD (h391 : D391Deep) (hU : D310Unfaith) : D310Deep := by
  intro W _ _ M Mp T L V hD hMp hqM hlt
  subst hMp
  have hle := d310_orbSup_le_commSub hD
  have hcomm : commSub V Mp = V := by
    rw [← commOf_eq_commSub]
    exact hD.hyp.irr.2.2.1
  by_cases hf : ∃ A : Subgroup (MulAut W), IsA2 M A ∧ A ≤ T ∧ commSeries A 3 = ⊥ ∧ rAV A ≤ 2 ∧
      (∀ a ∈ A, (∀ x ∈ Mp, a * x = x * a) → a = 1)
  · obtain ⟨A, hA1, hA2, hA3, hA4, hA5⟩ := hf
    have hstrict : commSub V Mp < commSub (orbSup T V) Mp := by
      rw [hcomm]
      exact lt_of_lt_of_le hlt hle
    exact h391 W M Mp T Mp V rfl hD hqM ⟨hcomm.symm, hstrict⟩ A hA1 hA2 hA3 hA4 hA5
  · apply hU W M Mp T Mp V hD rfl hqM hlt
    intro A hA1 hA2 hA3 hA4
    by_contra hcon
    apply hf
    refine ⟨A, hA1, hA2, hA3, hA4, fun a ha hc => ?_⟩
    by_contra hne
    exact hcon ⟨a, ha, hne, hc⟩

theorem d310_of_unfaithfulD (h35 : D35) (h391 : D391Deep) (hU : D310Unfaith) : D310 :=
  d310_of_deep h35 (d310Deep_of_unfaithfulD h391 hU)

end CFSG.Quasithin
