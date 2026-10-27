module

public import CFSG.SignalizerFunctorTheorem.Assembly
public import CFSG.LocalAnalysis.SignalizerFunctor.MinimalIncompleteSolvable
public import CFSG.LocalAnalysis.SignalizerFunctor.OnePrimeCompleteness
public import CFSG.LocalAnalysis.SignalizerFunctor.TwoStageCore

public section

open CFSG.Open CFSG.SignalizerFunctor.Helpers

namespace CFSG.SignalizerFunctorTheorem.Solvable

@[expose] def TwoThreeCase (prime rank : ℕ) : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (actor : Subgroup G), IsElemAbelian prime actor →
    prime ^ (rank + 2) ≤ Nat.card actor → ∀ values : Subgroup G → Subgroup G,
    SolvableSignalizerConditions prime rank actor values →
    solvableSignalizerLocallyComplete prime rank actor values →
    signalizerSpectrum prime rank actor values = {2, 3} →
    solvableSignalizerCompatible prime rank actor values
      (⨆ selected ∈ signalizerFunctorEk prime rank actor, values selected)

@[expose] def FiveCase (prime rank : ℕ) : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (actor : Subgroup G), IsElemAbelian prime actor →
    prime ^ (rank + 2) ≤ Nat.card actor → ∀ values : Subgroup G → Subgroup G,
    SolvableSignalizerConditions prime rank actor values →
    solvableSignalizerLocallyComplete prime rank actor values →
    ∀ q ∈ signalizerSpectrum prime rank actor values, 5 ≤ q →
    solvableSignalizerCompatible prime rank actor values
      (⨆ selected ∈ signalizerFunctorEk prime rank actor, values selected)

variable {G : Type*} [Group G] [Finite G]

theorem complete_of_spectrum_subsingleton
    (prime rank : ℕ) (prime_prime : prime.Prime)
    (actor : Subgroup G) (elementary : IsElemAbelian prime actor)
    (large : prime ^ (rank + 2) ≤ Nat.card actor)
    (values : Subgroup G → Subgroup G)
    (conditions : SolvableSignalizerConditions prime rank actor values)
    (small : (signalizerSpectrum prime rank actor values).Subsingleton) :
    solvableSignalizerCompatible prime rank actor values
      (⨆ selected ∈ signalizerFunctorEk prime rank actor, values selected) := by
  obtain ⟨r, hr, hrp, hpgroup⟩ : ∃ r : ℕ, r.Prime ∧ prime ≠ r ∧
      ∀ S ∈ signalizerFunctorEk prime rank actor, IsPGroup r (values S) := by
    by_cases hempty : signalizerSpectrum prime rank actor values = ∅
    · obtain ⟨r, hr, hrp⟩ : ∃ r : ℕ, r.Prime ∧ prime ≠ r := by
        by_cases h2 : prime = 2
        · exact ⟨3, Nat.prime_three, by omega⟩
        · exact ⟨2, Nat.prime_two, h2⟩
      refine ⟨r, hr, hrp, fun S hS => ?_⟩
      apply (prime_supported_singleton_iff_pgroup r hr (values S)).mp
      intro t ht hdvd
      exact absurd (show t ∈ signalizerSpectrum prime rank actor values from ⟨ht, S, hS, hdvd⟩)
        (hempty ▸ Set.notMem_empty t)
    · obtain ⟨r, hrmem⟩ := Set.nonempty_iff_ne_empty.mpr hempty
      refine ⟨r, hrmem.1, fun h => signalizer_spectrum_prime_excluded prime rank prime_prime actor
        values conditions.coprime (h ▸ hrmem), fun S hS => ?_⟩
      apply (prime_supported_singleton_iff_pgroup r hrmem.1 (values S)).mp
      intro t ht hdvd
      exact Set.mem_singleton_iff.mpr (small ⟨ht, S, hS, hdvd⟩ hrmem)
  obtain ⟨⟨-, hnorm⟩, hcent, -, -, hsolv⟩ := signalizer_one_prime_completeness prime rank r
    prime_prime hr hrp actor elementary large values conditions.central conditions.coprime
    conditions.normalized conditions.balanced hpgroup
  exact ⟨⟨hnorm, fun S hS => (hcent S hS).le⟩, hsolv⟩

theorem complete_of_ne_two_three
    (prime rank : ℕ) (prime_prime : prime.Prime)
    (actor : Subgroup G) (elementary : IsElemAbelian prime actor)
    (large : prime ^ (rank + 2) ≤ Nat.card actor)
    (values : Subgroup G → Subgroup G)
    (conditions : SolvableSignalizerConditions prime rank actor values)
    (five : ∀ q ∈ signalizerSpectrum prime rank actor values, 5 ≤ q →
      solvableSignalizerCompatible prime rank actor values
        (⨆ selected ∈ signalizerFunctorEk prime rank actor, values selected))
    (hne : signalizerSpectrum prime rank actor values ≠ {2, 3}) :
    solvableSignalizerCompatible prime rank actor values
      (⨆ selected ∈ signalizerFunctorEk prime rank actor, values selected) := by
  by_cases small : (signalizerSpectrum prime rank actor values).Subsingleton
  · exact complete_of_spectrum_subsingleton prime rank prime_prime actor elementary large values
      conditions small
  obtain ⟨q, hq, hq5⟩ : ∃ q ∈ signalizerSpectrum prime rank actor values, 5 ≤ q := by
    by_contra! hsmall
    apply hne
    obtain ⟨a, ha, b, hb, hab⟩ := Set.not_subsingleton_iff.mp small
    have hsub : signalizerSpectrum prime rank actor values ⊆ {2, 3} := by
      intro t ht
      have h2 := (ht.1 : t.Prime).two_le
      have h4 : t ≠ 4 := fun h => by
        have := ht.1
        rw [h] at this
        norm_num at this
      have := hsmall t ht
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
      omega
    apply Set.Subset.antisymm hsub
    have ha' := hsub ha
    have hb' := hsub hb
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at ha' hb'
    intro t ht
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at ht
    rcases ht with rfl | rfl <;> rcases ha' with rfl | rfl <;> rcases hb' with rfl | rfl <;>
      first | exact ha | exact hb | exact absurd rfl hab
  exact five q hq hq5

theorem complete_of_twoThreeCase (prime rank : ℕ) (prime_prime : prime.Prime)
    (fiveCase : FiveCase prime rank) (twoThree : TwoThreeCase prime rank) :
    ∀ (G : Type) [Group G] [Finite G] (actor : Subgroup G), IsElemAbelian prime actor →
      prime ^ (rank + 2) ≤ Nat.card actor → ∀ values : Subgroup G → Subgroup G,
      SolvableSignalizerConditions prime rank actor values →
      solvableSignalizerCompatible prime rank actor values
        (⨆ selected ∈ signalizerFunctorEk prime rank actor, values selected) := by
  suffices h : ∀ n : ℕ, ∀ (G : Type) [Group G] [Finite G] (actor : Subgroup G),
      IsElemAbelian prime actor → prime ^ (rank + 2) ≤ Nat.card actor →
      ∀ values : Subgroup G → Subgroup G, SolvableSignalizerConditions prime rank actor values →
      Nat.card G + (signalizerSpectrum prime rank actor values).ncard = n →
      solvableSignalizerCompatible prime rank actor values
        (⨆ selected ∈ signalizerFunctorEk prime rank actor, values selected) from
    fun G _ _ actor elementary large values conditions =>
      h _ G actor elementary large values conditions rfl
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro G _ _ actor elementary large values conditions hn
    by_contra incomplete
    obtain ⟨-, locally_complete⟩ := minimal_incomplete_solvable_completion_local prime rank
      prime_prime actor elementary large values conditions incomplete
      (fun H _ _ actorH elementaryH largeH valuesH conditionsH hlt =>
        ih _ (hn ▸ hlt) H actorH elementaryH largeH valuesH conditionsH rfl)
    by_cases htt : signalizerSpectrum prime rank actor values = {2, 3}
    · exact incomplete (twoThree G actor elementary large values conditions locally_complete htt)
    · exact incomplete (complete_of_ne_two_three prime rank prime_prime actor
        elementary large values conditions
        (fiveCase G actor elementary large values conditions locally_complete) htt)

theorem twoThreeCase_of_le_three (prime rank : ℕ) (prime_prime : prime.Prime)
    (hp3 : prime ≤ 3) : TwoThreeCase prime rank := by
  intro G _ _ actor _ _ values conditions _ hspec
  have hmem : prime ∈ signalizerSpectrum prime rank actor values := by
    rw [hspec]
    have := prime_prime.two_le
    interval_cases prime <;> simp
  exact absurd hmem (signalizer_spectrum_prime_excluded prime rank prime_prime actor values
    conditions.coprime)

theorem solvableRankOneTheoremAt_of_cases (p : ℕ) (hp : p.Prime) (fiveCase : FiveCase p 1)
    (twoThree : TwoThreeCase p 1) : SolvableRankOneTheoremAt p := by
  intro G _ _ A hA hlarge Θ hΘ hsol
  have conditions : SolvableSignalizerConditions p 1 A Θ :=
    ⟨hΘ.central, hΘ.coprime, hΘ.normalized, hΘ.balanced, hsol⟩
  obtain ⟨⟨-, hbounds⟩, hWsol⟩ := complete_of_twoThreeCase p 1 hp fiveCase twoThree
    G A hA hlarge Θ conditions
  obtain ⟨⟨hcop, -⟩, hcent, -⟩ := completion_properties_of_centralizer_bounds p 1 hp A hA
    ((Nat.pow_le_pow_right hp.pos (by omega)).trans hlarge) Θ hΘ.central hΘ.coprime
    hΘ.normalized hbounds
  exact ⟨⟨hcop, hcent⟩, hWsol⟩

end CFSG.SignalizerFunctorTheorem.Solvable
