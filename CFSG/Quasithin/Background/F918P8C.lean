module

public import CFSG.Quasithin.Background.F918P8

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.Assembly.LowTwoRank CFSG.QuasithinUnique
open scoped Pointwise

@[expose] def D310Unfaith : Prop :=
  ∀ (W : Type) [CommGroup W] [Finite W] (M Mp T L : Subgroup (MulAut W)) (V : Subgroup W),
    D3Std M Mp T L V → Mp = L → qhatOf M ≤ ((2 : ℚ) : WithTop ℚ) → V < orbSup T V →
    (∀ A : Subgroup (MulAut W), IsA2 M A → A ≤ T → commSeries A 3 = ⊥ → rAV A ≤ 2 →
      ∃ a ∈ A, a ≠ 1 ∧ ∀ x ∈ Mp, a * x = x * a) →
    orbSup T V = ⊤

section Pieces

variable {W : Type} [CommGroup W] [Finite W] {M Mp T L : Subgroup (MulAut W)} {V : Subgroup W}

theorem d310_orbSup_le_commSub (hD : D3Std M Mp T L V) :
    orbSup T V ≤ commSub (orbSup T V) Mp := by
  have hTX : T ≤ Subgroup.normalizer (Mp : Set (MulAut W)) := by
    rw [hD.hyp.Mp_eq]
    exact le_normalizer_conjClosure L T
  have hcomm : modComm Mp V = V := hD.irrT.1.2.2.1
  have h1 : orbSup T V ≤ modComm Mp (orbSup T V) := by
    refine orbSup_le fun t ht => ?_
    change t • V ≤ modComm Mp (orbSup T V)
    calc t • V = t • modComm Mp V := by rw [hcomm]
      _ = modComm Mp (t • V) := smul_modComm (hTX ht) V
      _ ≤ modComm Mp (orbSup T V) := XMod.commOf_mono (map_le_orbSup ht)
  rwa [modComm, commOf_eq_commSub] at h1

end Pieces

theorem d310Deep_of_unfaithful (h391 : D391) (hU : D310Unfaith) : D310Deep := by
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
    rcases h391 W M Mp T Mp V rfl hD hqM (Or.inr ⟨hcomm.symm, hstrict⟩) A hA1 hA2 hA3 hA4 hA5 with
      h | ⟨hV, -⟩
    · exact h
    · exact absurd hV hlt.ne
  · apply hU W M Mp T Mp V hD rfl hqM hlt
    intro A hA1 hA2 hA3 hA4
    by_contra hcon
    apply hf
    refine ⟨A, hA1, hA2, hA3, hA4, fun a ha hc => ?_⟩
    by_contra hne
    exact hcon ⟨a, ha, hne, hc⟩

theorem d310_of_unfaithful (h35 : D35) (h391 : D391) (hU : D310Unfaith) : D310 :=
  d310_of_deep h35 (d310Deep_of_unfaithful h391 hU)

end CFSG.Quasithin
